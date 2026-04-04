"""
邮件队列处理任务
使用 Celery 处理异步邮件发送
"""
import json
from typing import Dict, Any, Optional
from datetime import datetime
from celery import shared_task
from celery.exceptions import MaxRetriesExceededError

from ..core.email_config import email_settings
from ..cache.redis_cache import redis_cache
from .email_service import get_email_service
from .template_manager import get_template_manager
from .email_stats import get_email_stats_manager


@shared_task(
    bind=True,
    max_retries=email_settings.EMAIL_RETRY_MAX_ATTEMPTS,
    default_retry_delay=email_settings.EMAIL_RETRY_DELAY,
    queue=email_settings.EMAIL_QUEUE_NAME,
)
def send_email_task(
    self,
    to_addresses: list,
    subject: str,
    html_content: str,
    text_content: Optional[str] = None,
    from_address: Optional[str] = None,
    from_name: Optional[str] = None,
    reply_to: Optional[str] = None,
    attachments: Optional[list] = None,
    tracking_id: Optional[str] = None,
) -> Dict[str, Any]:
    """
    发送邮件的 Celery 任务
    
    Args:
        to_addresses: 收件人地址列表
        subject: 邮件主题
        html_content: HTML 内容
        text_content: 纯文本内容
        from_address: 发件人地址
        from_name: 发件人名称
        reply_to: 回复地址
        attachments: 附件列表
        tracking_id: 追踪ID
    """
    email_service = get_email_service()
    stats_manager = get_email_stats_manager()
    
    try:
        # 记录任务开始
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "processing",
                {"started_at": datetime.utcnow().isoformat()},
            )
        
        # 发送邮件（需要在异步环境中运行）
        import asyncio
        result = asyncio.run(email_service.send_email(
            to_addresses=to_addresses,
            subject=subject,
            html_content=html_content,
            text_content=text_content,
            from_address=from_address,
            from_name=from_name,
            reply_to=reply_to,
            attachments=attachments,
            custom_args={"tracking_id": tracking_id} if tracking_id else None,
        ))
        
        # 更新追踪状态
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "sent",
                {
                    "sent_at": datetime.utcnow().isoformat(),
                    "provider": result.get("provider"),
                    "message_id": result.get("message_id"),
                },
            )
        
        return {
            "success": True,
            "tracking_id": tracking_id,
            "result": result,
        }
        
    except Exception as exc:
        # 更新失败状态
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "failed",
                {
                    "failed_at": datetime.utcnow().isoformat(),
                    "error": str(exc),
                    "retry_count": self.request.retries,
                },
            )
        
        # 重试
        try:
            self.retry(exc=exc)
        except MaxRetriesExceededError:
            # 最终失败处理
            if tracking_id:
                stats_manager.update_send_status(
                    tracking_id,
                    "permanently_failed",
                    {"max_retries_exceeded": True},
                )
            
            return {
                "success": False,
                "tracking_id": tracking_id,
                "error": str(exc),
                "retries_exceeded": True,
            }


@shared_task(
    bind=True,
    max_retries=3,
    default_retry_delay=30,
    queue=email_settings.EMAIL_QUEUE_NAME,
)
def send_template_email_task(
    self,
    to_addresses: list,
    template_name: str,
    template_variables: Dict[str, Any],
    language: Optional[str] = None,
    tracking_id: Optional[str] = None,
) -> Dict[str, Any]:
    """
    使用模板发送邮件的 Celery 任务
    
    Args:
        to_addresses: 收件人地址列表
        template_name: 模板名称
        template_variables: 模板变量
        language: 语言
        tracking_id: 追踪ID
    """
    template_manager = get_template_manager()
    email_service = get_email_service()
    stats_manager = get_email_stats_manager()
    
    try:
        # 渲染模板
        rendered = template_manager.render_template(
            template_name,
            template_variables,
            language,
        )
        
        # 记录任务开始
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "processing",
                {"started_at": datetime.utcnow().isoformat()},
            )
        
        # 发送邮件
        import asyncio
        result = asyncio.run(email_service.send_email(
            to_addresses=to_addresses,
            subject=rendered["subject"],
            html_content=rendered["html"],
            text_content=rendered["text"],
            custom_args={"tracking_id": tracking_id} if tracking_id else None,
        ))
        
        # 更新追踪状态
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "sent",
                {
                    "sent_at": datetime.utcnow().isoformat(),
                    "template": template_name,
                    "provider": result.get("provider"),
                    "message_id": result.get("message_id"),
                },
            )
        
        return {
            "success": True,
            "tracking_id": tracking_id,
            "template": template_name,
            "result": result,
        }
        
    except Exception as exc:
        if tracking_id:
            stats_manager.update_send_status(
                tracking_id,
                "failed",
                {
                    "failed_at": datetime.utcnow().isoformat(),
                    "error": str(exc),
                    "retry_count": self.request.retries,
                },
            )
        
        try:
            self.retry(exc=exc)
        except MaxRetriesExceededError:
            if tracking_id:
                stats_manager.update_send_status(
                    tracking_id,
                    "permanently_failed",
                    {"max_retries_exceeded": True},
                )
            
            return {
                "success": False,
                "tracking_id": tracking_id,
                "error": str(exc),
                "retries_exceeded": True,
            }


@shared_task(
    bind=True,
    queue=email_settings.EMAIL_QUEUE_NAME,
)
def process_email_queue_task(self) -> Dict[str, Any]:
    """
    处理邮件队列任务
    定期执行以处理队列中的邮件
    """
    stats = {
        "processed": 0,
        "sent": 0,
        "failed": 0,
        "queued": 0,
    }
    
    # 获取队列中的邮件
    queue_key = f"email_queue:{email_settings.EMAIL_QUEUE_NAME}"
    
    # 批量处理（每次最多100封）
    batch_size = 100
    
    for _ in range(batch_size):
        # 从队列中获取邮件
        email_data = redis_cache.lpop(queue_key)
        
        if not email_data:
            break
        
        try:
            email_info = json.loads(email_data)
            
            # 根据类型调用相应的任务
            if email_info.get("use_template"):
                send_template_email_task.delay(
                    to_addresses=email_info["to_addresses"],
                    template_name=email_info["template_name"],
                    template_variables=email_info.get("template_variables", {}),
                    language=email_info.get("language"),
                    tracking_id=email_info.get("tracking_id"),
                )
            else:
                send_email_task.delay(
                    to_addresses=email_info["to_addresses"],
                    subject=email_info["subject"],
                    html_content=email_info["html_content"],
                    text_content=email_info.get("text_content"),
                    from_address=email_info.get("from_address"),
                    from_name=email_info.get("from_name"),
                    reply_to=email_info.get("reply_to"),
                    attachments=email_info.get("attachments"),
                    tracking_id=email_info.get("tracking_id"),
                )
            
            stats["queued"] += 1
            
        except Exception as e:
            print(f"Failed to process email from queue: {e}")
            stats["failed"] += 1
    
    return stats


@shared_task(
    bind=True,
    queue=email_settings.EMAIL_QUEUE_NAME,
)
def send_bulk_emails_task(
    self,
    recipients: list,
    template_name: Optional[str] = None,
    subject: Optional[str] = None,
    html_content: Optional[str] = None,
    text_content: Optional[str] = None,
    language: Optional[str] = None,
) -> Dict[str, Any]:
    """
    批量发送邮件任务
    
    Args:
        recipients: 收件人列表，每项包含 email 和 template_variables
        template_name: 模板名称（使用模板时）
        subject: 邮件主题（不使用模板时）
        html_content: HTML 内容（不使用模板时）
        text_content: 纯文本内容（不使用模板时）
        language: 语言
    """
    stats = {"total": len(recipients), "sent": 0, "failed": 0}
    
    for recipient in recipients:
        try:
            to_address = recipient["email"]
            tracking_id = recipient.get("tracking_id")
            
            if template_name:
                # 使用模板发送
                send_template_email_task.delay(
                    to_addresses=[to_address],
                    template_name=template_name,
                    template_variables=recipient.get("template_variables", {}),
                    language=language,
                    tracking_id=tracking_id,
                )
            else:
                # 直接发送
                send_email_task.delay(
                    to_addresses=[to_address],
                    subject=subject,
                    html_content=html_content,
                    text_content=text_content,
                    tracking_id=tracking_id,
                )
            
            stats["sent"] += 1
            
        except Exception as e:
            print(f"Failed to queue email for {recipient.get('email')}: {e}")
            stats["failed"] += 1
    
    return stats


@shared_task(
    bind=True,
    queue="default",
)
def cleanup_old_email_stats_task(self, days: int = None) -> Dict[str, Any]:
    """
    清理过期的邮件统计数据
    
    Args:
        days: 保留天数，默认使用配置
    """
    retention_days = days or email_settings.EMAIL_STATS_RETENTION_DAYS
    stats_manager = get_email_stats_manager()
    
    result = stats_manager.cleanup_old_stats(retention_days)
    
    return {
        "cleaned": result,
        "retention_days": retention_days,
    }


# ============ 队列管理工具函数 ============

async def enqueue_email(
    to_addresses: list,
    subject: str,
    html_content: str,
    text_content: Optional[str] = None,
    **kwargs
) -> str:
    """
    将邮件添加到队列
    
    Returns:
        追踪ID
    """
    import uuid
    tracking_id = str(uuid.uuid4())
    
    email_data = {
        "to_addresses": to_addresses if isinstance(to_addresses, list) else [to_addresses],
        "subject": subject,
        "html_content": html_content,
        "text_content": text_content,
        "use_template": False,
        "tracking_id": tracking_id,
        **kwargs,
    }
    
    queue_key = f"email_queue:{email_settings.EMAIL_QUEUE_NAME}"
    await redis_cache.rpush(queue_key, json.dumps(email_data))
    
    return tracking_id


async def enqueue_template_email(
    to_addresses: list,
    template_name: str,
    template_variables: Dict[str, Any],
    language: Optional[str] = None,
) -> str:
    """
    将模板邮件添加到队列
    
    Returns:
        追踪ID
    """
    import uuid
    tracking_id = str(uuid.uuid4())
    
    email_data = {
        "to_addresses": to_addresses if isinstance(to_addresses, list) else [to_addresses],
        "template_name": template_name,
        "template_variables": template_variables,
        "language": language,
        "use_template": True,
        "tracking_id": tracking_id,
    }
    
    queue_key = f"email_queue:{email_settings.EMAIL_QUEUE_NAME}"
    await redis_cache.rpush(queue_key, json.dumps(email_data))
    
    return tracking_id


async def get_queue_status() -> Dict[str, Any]:
    """获取队列状态"""
    queue_key = f"email_queue:{email_settings.EMAIL_QUEUE_NAME}"
    queue_length = await redis_cache.llen(queue_key)
    
    return {
        "queue_name": email_settings.EMAIL_QUEUE_NAME,
        "pending_count": queue_length,
        "queue_enabled": email_settings.EMAIL_QUEUE_ENABLED,
    }
