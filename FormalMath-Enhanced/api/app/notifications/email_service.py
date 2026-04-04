"""
邮件服务核心模块
支持 SendGrid、AWS SES 和 SMTP 三种发送方式
"""
import json
import base64
import boto3
import aiohttp
import smtplib
from typing import List, Optional, Dict, Any, Union
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders
from abc import ABC, abstractmethod
from datetime import datetime
import asyncio
from functools import lru_cache

from ..core.email_config import email_settings
from ..cache.redis_cache import redis_cache


class EmailProvider(ABC):
    """邮件提供商抽象基类"""
    
    @abstractmethod
    async def send_email(
        self,
        to_addresses: List[str],
        subject: str,
        html_content: str,
        text_content: Optional[str] = None,
        from_address: Optional[str] = None,
        from_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        attachments: Optional[List[Dict[str, Any]]] = None,
        custom_args: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        """发送邮件"""
        pass


class SendGridProvider(EmailProvider):
    """SendGrid 邮件提供商"""
    
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.api_url = email_settings.SENDGRID_API_URL
    
    async def send_email(
        self,
        to_addresses: List[str],
        subject: str,
        html_content: str,
        text_content: Optional[str] = None,
        from_address: Optional[str] = None,
        from_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        attachments: Optional[List[Dict[str, Any]]] = None,
        custom_args: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        """使用 SendGrid API 发送邮件"""
        
        from_addr = from_address or email_settings.EMAIL_FROM_ADDRESS
        from_nm = from_name or email_settings.EMAIL_FROM_NAME
        
        # 构建收件人列表
        personalizations = [{
            "to": [{"email": addr} for addr in to_addresses]
        }]
        
        # 构建邮件内容
        content = [{"type": "text/html", "value": html_content}]
        if text_content:
            content.insert(0, {"type": "text/plain", "value": text_content})
        
        payload = {
            "personalizations": personalizations,
            "from": {"email": from_addr, "name": from_nm},
            "subject": subject,
            "content": content,
        }
        
        # 添加回复地址
        if reply_to or email_settings.EMAIL_REPLY_TO:
            payload["reply_to"] = {"email": reply_to or email_settings.EMAIL_REPLY_TO}
        
        # 添加附件
        if attachments:
            payload["attachments"] = []
            for att in attachments:
                content_b64 = base64.b64encode(att["content"]).decode()
                payload["attachments"].append({
                    "content": content_b64,
                    "filename": att["filename"],
                    "type": att.get("type", "application/octet-stream"),
                    "disposition": "attachment",
                })
        
        # 添加自定义参数（用于追踪）
        if custom_args:
            payload["custom_args"] = custom_args
        
        # 添加配置集（用于 AWS SES 事件追踪）
        if email_settings.AWS_SES_CONFIGURATION_SET:
            payload["tracking_settings"] = {
                "click_tracking": {"enable": True},
                "open_tracking": {"enable": True},
            }
        
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }
        
        async with aiohttp.ClientSession() as session:
            async with session.post(
                self.api_url,
                headers=headers,
                json=payload,
                timeout=aiohttp.ClientTimeout(total=30)
            ) as response:
                if response.status == 202:
                    return {
                        "success": True,
                        "provider": "sendgrid",
                        "message_id": response.headers.get("X-Message-Id"),
                        "status_code": response.status,
                    }
                else:
                    error_text = await response.text()
                    raise Exception(f"SendGrid API error: {response.status} - {error_text}")


class AWSSESProvider(EmailProvider):
    """AWS SES 邮件提供商"""
    
    def __init__(
        self,
        aws_access_key_id: str,
        aws_secret_access_key: str,
        region_name: str,
    ):
        self.client = boto3.client(
            "ses",
            aws_access_key_id=aws_access_key_id,
            aws_secret_access_key=aws_secret_access_key,
            region_name=region_name,
        )
    
    async def send_email(
        self,
        to_addresses: List[str],
        subject: str,
        html_content: str,
        text_content: Optional[str] = None,
        from_address: Optional[str] = None,
        from_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        attachments: Optional[List[Dict[str, Any]]] = None,
        custom_args: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        """使用 AWS SES API 发送邮件"""
        
        from_addr = from_address or email_settings.EMAIL_FROM_ADDRESS
        from_nm = from_name or email_settings.EMAIL_FROM_NAME
        
        # 构建发件人地址
        source = f"{from_nm} <{from_addr}>" if from_nm else from_addr
        
        # 构建邮件主体
        message = {
            "Subject": {"Data": subject, "Charset": "UTF-8"},
            "Body": {},
        }
        
        if text_content:
            message["Body"]["Text"] = {"Data": text_content, "Charset": "UTF-8"}
        
        if html_content:
            message["Body"]["Html"] = {"Data": html_content, "Charset": "UTF-8"}
        
        # 构建发送参数
        params = {
            "Source": source,
            "Destination": {"ToAddresses": to_addresses},
            "Message": message,
        }
        
        # 添加回复地址
        if reply_to or email_settings.EMAIL_REPLY_TO:
            params["ReplyToAddresses"] = [reply_to or email_settings.EMAIL_REPLY_TO]
        
        # 添加配置集
        if email_settings.AWS_SES_CONFIGURATION_SET:
            params["ConfigurationSetName"] = email_settings.AWS_SES_CONFIGURATION_SET
        
        # 在异步环境中运行 boto3 客户端
        loop = asyncio.get_event_loop()
        response = await loop.run_in_executor(None, self.client.send_email, params)
        
        return {
            "success": True,
            "provider": "aws_ses",
            "message_id": response["MessageId"],
        }


class SMTPProvider(EmailProvider):
    """SMTP 邮件提供商（备用）"""
    
    def __init__(
        self,
        host: str,
        port: int,
        username: str,
        password: str,
        use_tls: bool = True,
    ):
        self.host = host
        self.port = port
        self.username = username
        self.password = password
        self.use_tls = use_tls
    
    async def send_email(
        self,
        to_addresses: List[str],
        subject: str,
        html_content: str,
        text_content: Optional[str] = None,
        from_address: Optional[str] = None,
        from_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        attachments: Optional[List[Dict[str, Any]]] = None,
        custom_args: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        """使用 SMTP 发送邮件"""
        
        from_addr = from_address or email_settings.EMAIL_FROM_ADDRESS
        from_nm = from_name or email_settings.EMAIL_FROM_NAME
        
        # 构建邮件
        msg = MIMEMultipart("alternative")
        msg["Subject"] = subject
        msg["From"] = f"{from_nm} <{from_addr}>" if from_nm else from_addr
        msg["To"] = ", ".join(to_addresses)
        
        if reply_to or email_settings.EMAIL_REPLY_TO:
            msg["Reply-To"] = reply_to or email_settings.EMAIL_REPLY_TO
        
        # 添加正文
        if text_content:
            msg.attach(MIMEText(text_content, "plain", "utf-8"))
        if html_content:
            msg.attach(MIMEText(html_content, "html", "utf-8"))
        
        # 添加附件
        if attachments:
            for att in attachments:
                part = MIMEBase("application", "octet-stream")
                part.set_payload(att["content"])
                encoders.encode_base64(part)
                part.add_header(
                    "Content-Disposition",
                    f"attachment; filename= {att['filename']}",
                )
                msg.attach(part)
        
        # 发送邮件
        def _send():
            with smtplib.SMTP(self.host, self.port) as server:
                if self.use_tls:
                    server.starttls()
                server.login(self.username, self.password)
                server.send_message(msg)
        
        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, _send)
        
        return {
            "success": True,
            "provider": "smtp",
            "message_id": None,
        }


class EmailService:
    """邮件服务类"""
    
    def __init__(self):
        self.provider: Optional[EmailProvider] = None
        self._init_provider()
    
    def _init_provider(self):
        """初始化邮件提供商"""
        provider_type = email_settings.EMAIL_PROVIDER
        
        if provider_type == "sendgrid":
            if not email_settings.SENDGRID_API_KEY:
                raise ValueError("SendGrid API key not configured")
            self.provider = SendGridProvider(email_settings.SENDGRID_API_KEY)
        
        elif provider_type == "aws_ses":
            if not all([
                email_settings.AWS_ACCESS_KEY_ID,
                email_settings.AWS_SECRET_ACCESS_KEY,
            ]):
                raise ValueError("AWS credentials not configured")
            self.provider = AWSSESProvider(
                email_settings.AWS_ACCESS_KEY_ID,
                email_settings.AWS_SECRET_ACCESS_KEY,
                email_settings.AWS_REGION,
            )
        
        elif provider_type == "smtp":
            if not all([
                email_settings.SMTP_HOST,
                email_settings.SMTP_USER,
                email_settings.SMTP_PASSWORD,
            ]):
                raise ValueError("SMTP configuration incomplete")
            self.provider = SMTPProvider(
                email_settings.SMTP_HOST,
                email_settings.SMTP_PORT,
                email_settings.SMTP_USER,
                email_settings.SMTP_PASSWORD,
                email_settings.SMTP_USE_TLS,
            )
        
        else:
            raise ValueError(f"Unknown email provider: {provider_type}")
    
    async def send_email(
        self,
        to_addresses: Union[str, List[str]],
        subject: str,
        html_content: str,
        text_content: Optional[str] = None,
        from_address: Optional[str] = None,
        from_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        attachments: Optional[List[Dict[str, Any]]] = None,
        custom_args: Optional[Dict[str, str]] = None,
    ) -> Dict[str, Any]:
        """
        发送邮件
        
        Args:
            to_addresses: 收件人地址或地址列表
            subject: 邮件主题
            html_content: HTML 内容
            text_content: 纯文本内容（可选）
            from_address: 发件人地址
            from_name: 发件人名称
            reply_to: 回复地址
            attachments: 附件列表
            custom_args: 自定义参数
        
        Returns:
            发送结果字典
        """
        if isinstance(to_addresses, str):
            to_addresses = [to_addresses]
        
        if not self.provider:
            raise RuntimeError("Email provider not initialized")
        
        # 检查速率限制
        if not await self._check_rate_limit():
            raise Exception("Email rate limit exceeded")
        
        result = await self.provider.send_email(
            to_addresses=to_addresses,
            subject=subject,
            html_content=html_content,
            text_content=text_content,
            from_address=from_address,
            from_name=from_name,
            reply_to=reply_to,
            attachments=attachments,
            custom_args=custom_args,
        )
        
        # 记录发送统计
        await self._record_send_attempt(result["success"])
        
        return result
    
    async def _check_rate_limit(self) -> bool:
        """检查速率限制"""
        key = "email_rate_limit:hourly"
        current = await redis_cache.get(key)
        
        if current is None:
            await redis_cache.set(key, 1, ttl=3600)
            return True
        
        if int(current) >= email_settings.EMAIL_RATE_LIMIT:
            return False
        
        await redis_cache.incr(key)
        return True
    
    async def _record_send_attempt(self, success: bool):
        """记录发送尝试"""
        key = f"email_stats:{datetime.utcnow().strftime('%Y-%m-%d')}"
        field = "sent" if success else "failed"
        await redis_cache.hincrby(key, field, 1)
        await redis_cache.expire(key, email_settings.EMAIL_STATS_RETENTION_DAYS * 86400)
    
    async def get_provider_status(self) -> Dict[str, Any]:
        """获取提供商状态"""
        return {
            "provider": email_settings.EMAIL_PROVIDER,
            "initialized": self.provider is not None,
            "from_address": email_settings.EMAIL_FROM_ADDRESS,
            "from_name": email_settings.EMAIL_FROM_NAME,
            "queue_enabled": email_settings.EMAIL_QUEUE_ENABLED,
            "tracking_enabled": email_settings.EMAIL_TRACKING_ENABLED,
        }


@lru_cache()
def get_email_service() -> EmailService:
    """获取邮件服务实例"""
    return EmailService()
