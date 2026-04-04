"""
邮件通知系统测试
"""
import pytest
import asyncio
from unittest.mock import Mock, patch, AsyncMock
from datetime import datetime

from app.notifications import (
    get_email_service,
    get_template_manager,
    get_notification_trigger,
    get_email_stats_manager,
)
from app.notifications.email_service import (
    SendGridProvider,
    AWSSESProvider,
    SMTPProvider,
    EmailService,
)
from app.notifications.template_manager import TemplateManager, EmailTemplate
from app.notifications.notification_triggers import NotificationTrigger, NotificationType
from app.notifications.email_stats import EmailStatsManager, EmailSendRecord, DailyStats


class TestEmailProviders:
    """测试邮件提供商"""
    
    @pytest.mark.asyncio
    async def test_sendgrid_provider(self):
        """测试 SendGrid 提供商"""
        provider = SendGridProvider("test_api_key")
        
        with patch("aiohttp.ClientSession.post") as mock_post:
            mock_response = AsyncMock()
            mock_response.status = 202
            mock_response.headers = {"X-Message-Id": "test-message-id"}
            mock_post.return_value.__aenter__.return_value = mock_response
            
            result = await provider.send_email(
                to_addresses=["test@example.com"],
                subject="Test Subject",
                html_content="<h1>Test</h1>",
            )
            
            assert result["success"] is True
            assert result["provider"] == "sendgrid"
            assert result["message_id"] == "test-message-id"
    
    @pytest.mark.asyncio
    async def test_aws_ses_provider(self):
        """测试 AWS SES 提供商"""
        with patch("boto3.client") as mock_boto:
            mock_client = Mock()
            mock_client.send_email.return_value = {"MessageId": "aws-message-id"}
            mock_boto.return_value = mock_client
            
            provider = AWSSESProvider(
                aws_access_key_id="test_key",
                aws_secret_access_key="test_secret",
                region_name="us-east-1",
            )
            
            # Mock asyncio.run_in_executor
            with patch("asyncio.get_event_loop") as mock_loop:
                mock_executor = Mock()
                mock_executor.run_in_executor.return_value = {"MessageId": "aws-message-id"}
                mock_loop.return_value = mock_executor
                
                result = await provider.send_email(
                    to_addresses=["test@example.com"],
                    subject="Test Subject",
                    html_content="<h1>Test</h1>",
                )
                
                assert result["success"] is True
                assert result["provider"] == "aws_ses"


class TestTemplateManager:
    """测试模板管理器"""
    
    def test_get_template(self):
        """测试获取模板"""
        manager = TemplateManager()
        
        template = manager.get_template("welcome", "zh_CN")
        assert template is not None
        assert template.name == "welcome"
        assert "欢迎" in template.subject
        
        # 测试回退到默认语言
        template = manager.get_template("welcome", "en_US")
        assert template is not None
        assert "Welcome" in template.subject
    
    def test_render_template(self):
        """测试渲染模板"""
        manager = TemplateManager()
        
        variables = {
            "username": "TestUser",
            "verification_link": "https://example.com/verify",
        }
        
        rendered = manager.render_template("welcome", variables, "zh_CN")
        
        assert "欢迎" in rendered["subject"]
        assert "TestUser" in rendered["html"]
        assert "https://example.com/verify" in rendered["html"]
    
    def test_list_templates(self):
        """测试列出模板"""
        manager = TemplateManager()
        
        templates = manager.list_templates()
        assert len(templates) > 0
        
        template_names = [t["name"] for t in templates]
        assert "welcome" in template_names
        assert "verification" in template_names
        assert "password_reset" in template_names


class TestNotificationTriggers:
    """测试通知触发器"""
    
    @pytest.mark.asyncio
    async def test_should_send_notification(self):
        """测试是否应该发送通知（冷却时间）"""
        trigger = NotificationTrigger()
        
        with patch("app.notifications.notification_triggers.redis_cache") as mock_cache:
            # 模拟没有发送记录
            mock_cache.get.return_value = None
            mock_cache.set.return_value = None
            
            result = await trigger._should_send_notification(
                user_id=123,
                notification_type=NotificationType.LEARNING_REMINDER,
                cooldown_minutes=60,
            )
            
            assert result is True
            mock_cache.set.assert_called_once()
    
    @pytest.mark.asyncio
    async def test_is_notification_enabled(self):
        """测试通知是否启用"""
        trigger = NotificationTrigger()
        
        with patch("app.notifications.notification_triggers.redis_cache") as mock_cache:
            # 模拟用户偏好
            import json
            mock_cache.get.return_value = json.dumps({
                "learning_reminder": True,
                "marketing": False,
            })
            
            result = await trigger._is_notification_enabled(
                user_id=123,
                notification_type=NotificationType.LEARNING_REMINDER,
            )
            assert result is True
            
            result = await trigger._is_notification_enabled(
                user_id=123,
                notification_type=NotificationType.WEEKLY_REPORT,  # 默认启用
            )
            assert result is True


class TestEmailStats:
    """测试邮件统计"""
    
    def test_create_send_record(self):
        """测试创建发送记录"""
        with patch("app.notifications.email_stats.redis_cache") as mock_cache:
            mock_cache.set = AsyncMock(return_value=None)
            
            stats_manager = EmailStatsManager()
            
            # 使用 asyncio 运行异步方法
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            
            record = loop.run_until_complete(stats_manager.create_send_record(
                tracking_id="test-id",
                recipient="test@example.com",
                template_name="welcome",
                subject="Test Subject",
            ))
            
            assert record.tracking_id == "test-id"
            assert record.recipient == "test@example.com"
            assert record.status == "pending"
            
            loop.close()
    
    def test_update_send_status(self):
        """测试更新发送状态"""
        with patch("app.notifications.email_stats.redis_cache") as mock_cache:
            import json
            record = EmailSendRecord(
                tracking_id="test-id",
                recipient="test@example.com",
                template_name="welcome",
                subject="Test",
                status="pending",
                created_at=datetime.utcnow().isoformat(),
            )
            mock_cache.get = AsyncMock(return_value=json.dumps(record.to_dict()))
            mock_cache.set = AsyncMock(return_value=None)
            
            stats_manager = EmailStatsManager()
            
            result = stats_manager.update_send_status(
                tracking_id="test-id",
                status="sent",
                metadata={"sent_at": datetime.utcnow().isoformat()},
            )
            
            assert result is True


class TestEmailService:
    """测试邮件服务"""
    
    @pytest.mark.asyncio
    async def test_rate_limit(self):
        """测试速率限制"""
        with patch("app.notifications.email_service.redis_cache") as mock_cache:
            mock_cache.get = AsyncMock(return_value="50")  # 已发送50封
            mock_cache.set = AsyncMock(return_value=None)
            mock_cache.incr = AsyncMock(return_value=51)
            
            service = EmailService()
            
            # 模拟 provider
            service.provider = AsyncMock()
            service.provider.send_email.return_value = {
                "success": True,
                "message_id": "test-id",
            }
            
            result = await service._check_rate_limit()
            assert result is True  # 50 < 100 限制
    
    @pytest.mark.asyncio
    async def test_get_provider_status(self):
        """测试获取提供商状态"""
        service = EmailService()
        
        # 模拟 provider
        service.provider = Mock()
        
        status = await service.get_provider_status()
        
        assert "provider" in status
        assert "initialized" in status
        assert "from_address" in status


# ========== 集成测试 ==========

@pytest.mark.integration
class TestNotificationIntegration:
    """通知系统集成测试"""
    
    @pytest.mark.asyncio
    async def test_full_email_flow(self):
        """测试完整邮件流程"""
        # 1. 获取模板
        template_manager = get_template_manager()
        template = template_manager.get_template("welcome", "zh_CN")
        assert template is not None
        
        # 2. 渲染模板
        variables = {
            "username": "TestUser",
            "verification_link": "https://example.com/verify",
        }
        rendered = template_manager.render_template("welcome", variables)
        assert "TestUser" in rendered["html"]
        
        # 3. 发送邮件（模拟）
        with patch("app.notifications.email_service.EmailService.send_email") as mock_send:
            mock_send.return_value = {
                "success": True,
                "provider": "sendgrid",
                "message_id": "test-message-id",
            }
            
            email_service = get_email_service()
            result = await email_service.send_email(
                to_addresses=["test@example.com"],
                subject=rendered["subject"],
                html_content=rendered["html"],
            )
            
            assert result["success"] is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
