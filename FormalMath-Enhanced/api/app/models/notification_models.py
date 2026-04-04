"""
邮件通知相关数据库模型
"""
from datetime import datetime
from enum import Enum as PyEnum
from sqlalchemy import Column, Integer, String, DateTime, Text, Boolean, JSON, ForeignKey, Enum, Float
from sqlalchemy.orm import relationship

from ..core.database import Base


class EmailNotificationStatus(str, PyEnum):
    """邮件通知状态"""
    PENDING = "pending"
    QUEUED = "queued"
    PROCESSING = "processing"
    SENT = "sent"
    DELIVERED = "delivered"
    OPENED = "opened"
    CLICKED = "clicked"
    BOUNCED = "bounced"
    FAILED = "failed"
    COMPLAINED = "complained"


class EmailNotification(Base):
    """邮件通知记录表"""
    __tablename__ = "email_notifications"
    
    id = Column(Integer, primary_key=True, index=True)
    tracking_id = Column(String(36), unique=True, index=True, nullable=False)
    
    # 收件人信息
    recipient_email = Column(String(255), nullable=False, index=True)
    recipient_user_id = Column(Integer, ForeignKey("users.id"), nullable=True)
    
    # 邮件内容
    template_name = Column(String(100), nullable=True, index=True)
    subject = Column(String(500), nullable=False)
    language = Column(String(10), default="zh_CN")
    
    # 发送状态
    status = Column(Enum(EmailNotificationStatus), default=EmailNotificationStatus.PENDING, index=True)
    
    # 提供商信息
    provider = Column(String(50), nullable=True)  # sendgrid, aws_ses, smtp
    provider_message_id = Column(String(255), nullable=True)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow, index=True)
    queued_at = Column(DateTime, nullable=True)
    sent_at = Column(DateTime, nullable=True)
    delivered_at = Column(DateTime, nullable=True)
    opened_at = Column(DateTime, nullable=True)
    clicked_at = Column(DateTime, nullable=True)
    failed_at = Column(DateTime, nullable=True)
    
    # 重试信息
    retry_count = Column(Integer, default=0)
    last_error = Column(Text, nullable=True)
    
    # 追踪信息
    open_count = Column(Integer, default=0)
    click_count = Column(Integer, default=0)
    last_opened_at = Column(DateTime, nullable=True)
    last_clicked_at = Column(DateTime, nullable=True)
    
    # 额外数据
    template_variables = Column(JSON, default=dict)
    metadata = Column(JSON, default=dict)
    
    # 关系
    recipient_user = relationship("User", back_populates="email_notifications")


class EmailTemplateDB(Base):
    """邮件模板数据库表（用于自定义模板）"""
    __tablename__ = "email_templates"
    
    id = Column(Integer, primary_key=True, index=True)
    name = Column(String(100), nullable=False, index=True)
    language = Column(String(10), default="zh_CN")
    
    # 模板内容
    subject = Column(String(500), nullable=False)
    html_content = Column(Text, nullable=False)
    text_content = Column(Text, nullable=True)
    
    # 模板信息
    description = Column(String(500), nullable=True)
    variables = Column(JSON, default=list)  # 变量列表
    category = Column(String(50), nullable=True)  # 模板分类
    
    # 状态
    is_active = Column(Boolean, default=True)
    is_builtin = Column(Boolean, default=False)  # 是否内置模板
    
    # 版本控制
    version = Column(Integer, default=1)
    parent_id = Column(Integer, ForeignKey("email_templates.id"), nullable=True)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    created_by = Column(Integer, ForeignKey("users.id"), nullable=True)
    
    # 关系
    parent = relationship("EmailTemplateDB", remote_side=[id])
    versions = relationship("EmailTemplateDB", back_populates="parent")


class EmailUserPreference(Base):
    """用户邮件偏好设置表"""
    __tablename__ = "email_user_preferences"
    
    id = Column(Integer, primary_key=True, index=True)
    user_id = Column(Integer, ForeignKey("users.id"), unique=True, nullable=False)
    
    # 各类通知的开关
    welcome = Column(Boolean, default=True)
    verification = Column(Boolean, default=True)
    password_reset = Column(Boolean, default=True)
    learning_reminder = Column(Boolean, default=True)
    achievement_unlocked = Column(Boolean, default=True)
    learning_path_complete = Column(Boolean, default=True)
    weekly_report = Column(Boolean, default=True)
    monthly_report = Column(Boolean, default=True)
    new_follower = Column(Boolean, default=True)
    challenge_invitation = Column(Boolean, default=True)
    system_maintenance = Column(Boolean, default=True)
    security_alert = Column(Boolean, default=True)
    marketing = Column(Boolean, default=False)
    newsletter = Column(Boolean, default=True)
    
    # 发送时间偏好
    preferred_send_time = Column(String(5), default="09:00")  # HH:MM 格式
    timezone = Column(String(50), default="Asia/Shanghai")
    
    # 频率限制
    max_daily_emails = Column(Integer, default=10)
    digest_mode = Column(Boolean, default=False)  # 是否使用摘要模式
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)
    
    # 关系
    user = relationship("User", back_populates="email_preferences")


class EmailBounce(Base):
    """邮件退信记录表"""
    __tablename__ = "email_bounces"
    
    id = Column(Integer, primary_key=True, index=True)
    
    # 关联的邮件
    notification_id = Column(Integer, ForeignKey("email_notifications.id"), nullable=True)
    recipient_email = Column(String(255), nullable=False, index=True)
    
    # 退信信息
    bounce_type = Column(String(50), nullable=False)  # hard_bounce, soft_bounce
    bounce_reason = Column(Text, nullable=True)
    bounce_code = Column(String(10), nullable=True)
    
    # 原始数据
    raw_data = Column(JSON, default=dict)
    
    # 时间戳
    created_at = Column(DateTime, default=datetime.utcnow, index=True)
    
    # 处理状态
    is_processed = Column(Boolean, default=False)
    processed_at = Column(DateTime, nullable=True)


class EmailStatsDaily(Base):
    """每日邮件统计表"""
    __tablename__ = "email_stats_daily"
    
    id = Column(Integer, primary_key=True, index=True)
    date = Column(String(10), unique=True, nullable=False, index=True)  # YYYY-MM-DD
    
    # 发送统计
    total_sent = Column(Integer, default=0)
    total_delivered = Column(Integer, default=0)
    total_failed = Column(Integer, default=0)
    total_bounced = Column(Integer, default=0)
    
    # 互动统计
    total_opened = Column(Integer, default=0)
    total_clicked = Column(Integer, default=0)
    unique_opens = Column(Integer, default=0)
    unique_clicks = Column(Integer, default=0)
    
    # 计算指标
    delivery_rate = Column(Float, default=0.0)
    open_rate = Column(Float, default=0.0)
    click_rate = Column(Float, default=0.0)
    bounce_rate = Column(Float, default=0.0)
    
    # 详细数据（JSON）
    template_stats = Column(JSON, default=dict)  # 各模板使用统计
    provider_stats = Column(JSON, default=dict)  # 各提供商统计
    hourly_distribution = Column(JSON, default=dict)  # 小时分布
    top_links = Column(JSON, default=list)  # 热门点击链接
    
    created_at = Column(DateTime, default=datetime.utcnow)
    updated_at = Column(DateTime, default=datetime.utcnow, onupdate=datetime.utcnow)


class EmailUnsubscribe(Base):
    """邮件退订记录表"""
    __tablename__ = "email_unsubscribes"
    
    id = Column(Integer, primary_key=True, index=True)
    email = Column(String(255), unique=True, nullable=False, index=True)
    
    # 退订信息
    unsubscribed_at = Column(DateTime, default=datetime.utcnow)
    source = Column(String(100), nullable=True)  # 退订来源
    reason = Column(Text, nullable=True)  # 退订原因
    
    # IP 和用户代理（用于防滥用）
    ip_address = Column(String(45), nullable=True)
    user_agent = Column(String(500), nullable=True)
    
    # 状态
    is_resubscribed = Column(Boolean, default=False)
    resubscribed_at = Column(DateTime, nullable=True)


class EmailSuppressionList(Base):
    """邮件抑制列表（垃圾邮件投诉等）"""
    __tablename__ = "email_suppression_list"
    
    id = Column(Integer, primary_key=True, index=True)
    email = Column(String(255), unique=True, nullable=False, index=True)
    
    # 抑制原因
    reason = Column(String(50), nullable=False)  # complaint, bounce, unsubscribe
    
    # 来源信息
    source_provider = Column(String(50), nullable=True)  # sendgrid, aws_ses
    source_data = Column(JSON, default=dict)
    
    # 时间戳
    added_at = Column(DateTime, default=datetime.utcnow, index=True)
    expires_at = Column(DateTime, nullable=True)  # 过期时间（可选）
    
    # 状态
    is_active = Column(Boolean, default=True)


# 更新 User 模型关系
# 需要在 models.py 中添加以下关系：
# email_notifications = relationship("EmailNotification", back_populates="recipient_user")
# email_preferences = relationship("EmailUserPreference", back_populates="user", uselist=False)
