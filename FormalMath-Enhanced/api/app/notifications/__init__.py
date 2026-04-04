"""
邮件通知系统模块
提供邮件服务、模板管理、队列处理和统计追踪功能
"""
from .email_service import EmailService, get_email_service
from .template_manager import TemplateManager, get_template_manager
from .notification_triggers import NotificationTrigger, get_notification_trigger
from .email_stats import EmailStatsManager, get_email_stats_manager

__all__ = [
    "EmailService",
    "get_email_service",
    "TemplateManager",
    "get_template_manager",
    "NotificationTrigger",
    "get_notification_trigger",
    "EmailStatsManager",
    "get_email_stats_manager",
]
