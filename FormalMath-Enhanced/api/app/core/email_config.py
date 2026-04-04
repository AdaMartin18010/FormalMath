"""
邮件服务配置
支持 SendGrid 和 AWS SES 两种邮件服务提供商
"""
from typing import Optional, Literal
from functools import lru_cache
from pydantic_settings import BaseSettings


class EmailSettings(BaseSettings):
    """邮件服务配置类"""
    
    # 邮件服务提供商: sendgrid 或 aws_ses
    EMAIL_PROVIDER: Literal["sendgrid", "aws_ses", "smtp"] = "sendgrid"
    
    # 发件人配置
    EMAIL_FROM_NAME: str = "FormalMath"
    EMAIL_FROM_ADDRESS: str = "noreply@formalmath.edu"
    EMAIL_REPLY_TO: Optional[str] = None
    
    # SendGrid 配置
    SENDGRID_API_KEY: Optional[str] = None
    SENDGRID_API_URL: str = "https://api.sendgrid.com/v3/mail/send"
    
    # AWS SES 配置
    AWS_REGION: str = "us-east-1"
    AWS_ACCESS_KEY_ID: Optional[str] = None
    AWS_SECRET_ACCESS_KEY: Optional[str] = None
    AWS_SES_CONFIGURATION_SET: Optional[str] = None
    
    # SMTP 配置（备用）
    SMTP_HOST: Optional[str] = None
    SMTP_PORT: int = 587
    SMTP_USER: Optional[str] = None
    SMTP_PASSWORD: Optional[str] = None
    SMTP_USE_TLS: bool = True
    
    # 邮件队列配置
    EMAIL_QUEUE_ENABLED: bool = True
    EMAIL_QUEUE_NAME: str = "email_notifications"
    EMAIL_RETRY_MAX_ATTEMPTS: int = 3
    EMAIL_RETRY_DELAY: int = 60  # 秒
    EMAIL_RATE_LIMIT: int = 100  # 每小时最大发送数量
    
    # 邮件模板配置
    EMAIL_TEMPLATE_DIR: str = "app/notifications/templates"
    EMAIL_DEFAULT_LANGUAGE: str = "zh_CN"
    
    # 邮件追踪配置
    EMAIL_TRACKING_ENABLED: bool = True
    EMAIL_TRACKING_DOMAIN: Optional[str] = None
    
    # 邮件统计配置
    EMAIL_STATS_RETENTION_DAYS: int = 90
    
    class Config:
        env_file = ".env"
        case_sensitive = True


@lru_cache()
def get_email_settings() -> EmailSettings:
    """获取缓存的邮件配置实例"""
    return EmailSettings()


email_settings = get_email_settings()
