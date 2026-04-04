"""
邮件通知 API 端点
提供邮件发送、模板管理、统计查询等功能
"""
from typing import List, Optional, Dict, Any
from datetime import datetime
from fastapi import APIRouter, Depends, HTTPException, BackgroundTasks, Query
from pydantic import BaseModel, EmailStr

from ..notifications import (
    get_email_service,
    get_template_manager,
    get_notification_trigger,
    get_email_stats_manager,
)
from ..notifications.email_tasks import (
    send_email_task,
    send_template_email_task,
    enqueue_email,
    enqueue_template_email,
    get_queue_status,
)

router = APIRouter(prefix="/notifications", tags=["notifications"])


# ========== 请求模型 ==========

class SendEmailRequest(BaseModel):
    """发送邮件请求"""
    to_addresses: List[EmailStr]
    subject: str
    html_content: str
    text_content: Optional[str] = None
    from_address: Optional[EmailStr] = None
    from_name: Optional[str] = None
    reply_to: Optional[EmailStr] = None
    use_queue: bool = False


class SendTemplateEmailRequest(BaseModel):
    """发送模板邮件请求"""
    to_addresses: List[EmailStr]
    template_name: str
    template_variables: Dict[str, Any] = {}
    language: Optional[str] = None
    use_queue: bool = False


class TriggerNotificationRequest(BaseModel):
    """触发通知请求"""
    notification_type: str
    user_email: EmailStr
    username: str
    variables: Dict[str, Any] = {}
    language: Optional[str] = None


class EmailPreferencesRequest(BaseModel):
    """邮件偏好设置请求"""
    welcome: bool = True
    verification: bool = True
    password_reset: bool = True
    learning_reminder: bool = True
    achievement_unlocked: bool = True
    learning_path_complete: bool = True
    weekly_report: bool = True
    new_follower: bool = True
    challenge_invitation: bool = True
    system_maintenance: bool = True
    security_alert: bool = True
    marketing: bool = False


# ========== 响应模型 ==========

class EmailSendResponse(BaseModel):
    """邮件发送响应"""
    success: bool
    tracking_id: Optional[str] = None
    message: str
    queued: bool = False


class TemplateInfoResponse(BaseModel):
    """模板信息响应"""
    name: str
    languages: List[str]
    description: str
    variables: List[str]


class QueueStatusResponse(BaseModel):
    """队列状态响应"""
    queue_name: str
    pending_count: int
    queue_enabled: bool


class DailyStatsResponse(BaseModel):
    """每日统计响应"""
    date: str
    total_sent: int
    total_failed: int
    templates_used: Dict[str, int]
    providers_used: Dict[str, int]
    hourly_distribution: Dict[str, int]


class SummaryStatsResponse(BaseModel):
    """汇总统计响应"""
    period_days: int
    total_sent: int
    total_failed: int
    success_rate: float
    templates_used: Dict[str, int]
    providers_used: Dict[str, int]
    daily_average: float


class RealtimeStatsResponse(BaseModel):
    """实时统计响应"""
    today: Dict[str, int]
    queue: Dict[str, int]
    hourly_distribution: Dict[str, int]


class SendRecordResponse(BaseModel):
    """发送记录响应"""
    tracking_id: str
    recipient: str
    template_name: Optional[str]
    subject: str
    status: str
    created_at: str
    sent_at: Optional[str] = None
    failed_at: Optional[str] = None
    provider: Optional[str] = None
    opened_at: Optional[str] = None
    clicked_at: Optional[str] = None


# ========== API 端点 ==========

@router.get("/status")
async def get_email_service_status():
    """获取邮件服务状态"""
    email_service = get_email_service()
    return await email_service.get_provider_status()


@router.post("/send", response_model=EmailSendResponse)
async def send_email(request: SendEmailRequest):
    """发送邮件"""
    try:
        if request.use_queue:
            # 添加到队列
            tracking_id = await enqueue_email(
                to_addresses=request.to_addresses,
                subject=request.subject,
                html_content=request.html_content,
                text_content=request.text_content,
                from_address=request.from_address,
                from_name=request.from_name,
                reply_to=request.reply_to,
            )
            
            return EmailSendResponse(
                success=True,
                tracking_id=tracking_id,
                message="Email queued for sending",
                queued=True,
            )
        else:
            # 直接发送
            email_service = get_email_service()
            result = await email_service.send_email(
                to_addresses=request.to_addresses,
                subject=request.subject,
                html_content=request.html_content,
                text_content=request.text_content,
                from_address=request.from_address,
                from_name=request.from_name,
                reply_to=request.reply_to,
            )
            
            return EmailSendResponse(
                success=result.get("success", False),
                tracking_id=result.get("message_id"),
                message="Email sent successfully",
                queued=False,
            )
            
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/send-template", response_model=EmailSendResponse)
async def send_template_email(request: SendTemplateEmailRequest):
    """发送模板邮件"""
    try:
        if request.use_queue:
            # 添加到队列
            tracking_id = await enqueue_template_email(
                to_addresses=request.to_addresses,
                template_name=request.template_name,
                template_variables=request.template_variables,
                language=request.language,
            )
            
            return EmailSendResponse(
                success=True,
                tracking_id=tracking_id,
                message="Template email queued for sending",
                queued=True,
            )
        else:
            # 直接发送（使用 Celery 任务）
            task = send_template_email_task.delay(
                to_addresses=request.to_addresses,
                template_name=request.template_name,
                template_variables=request.template_variables,
                language=request.language,
            )
            
            return EmailSendResponse(
                success=True,
                tracking_id=task.id,
                message="Template email task created",
                queued=True,
            )
            
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/templates", response_model=List[TemplateInfoResponse])
async def list_templates():
    """列出所有邮件模板"""
    template_manager = get_template_manager()
    templates = template_manager.list_templates()
    return templates


@router.get("/templates/{template_name}")
async def get_template(
    template_name: str,
    language: Optional[str] = None,
):
    """获取邮件模板详情"""
    template_manager = get_template_manager()
    template = template_manager.get_template(template_name, language)
    
    if not template:
        raise HTTPException(status_code=404, detail="Template not found")
    
    return {
        "name": template.name,
        "subject": template.subject,
        "description": template.description,
        "variables": template.variables,
        "language": template.language,
    }


@router.post("/templates/{template_name}/preview")
async def preview_template(
    template_name: str,
    variables: Dict[str, Any],
    language: Optional[str] = None,
):
    """预览邮件模板"""
    template_manager = get_template_manager()
    
    try:
        rendered = template_manager.render_template(
            template_name,
            variables,
            language,
        )
        return rendered
    except ValueError as e:
        raise HTTPException(status_code=404, detail=str(e))


@router.post("/trigger/welcome")
async def trigger_welcome_email(
    user_email: str,
    username: str,
    verification_link: str,
    language: Optional[str] = None,
):
    """触发欢迎邮件"""
    trigger = get_notification_trigger()
    result = await trigger.send_welcome_email(
        user_email=user_email,
        username=username,
        verification_link=verification_link,
        language=language,
    )
    
    if result:
        return {"success": True, "tracking_id": result.get("message_id")}
    else:
        raise HTTPException(status_code=500, detail="Failed to send welcome email")


@router.post("/trigger/verification")
async def trigger_verification_email(
    user_email: str,
    username: str,
    verification_code: str,
    expires_minutes: int = 30,
    language: Optional[str] = None,
):
    """触发验证邮件"""
    trigger = get_notification_trigger()
    result = await trigger.send_verification_email(
        user_email=user_email,
        username=username,
        verification_code=verification_code,
        expires_minutes=expires_minutes,
        language=language,
    )
    
    if result:
        return {"success": True, "tracking_id": result.get("message_id")}
    else:
        raise HTTPException(status_code=500, detail="Failed to send verification email")


@router.post("/trigger/password-reset")
async def trigger_password_reset_email(
    user_email: str,
    username: str,
    reset_link: str,
    expires_hours: int = 24,
    language: Optional[str] = None,
):
    """触发密码重置邮件"""
    trigger = get_notification_trigger()
    result = await trigger.send_password_reset_email(
        user_email=user_email,
        username=username,
        reset_link=reset_link,
        expires_hours=expires_hours,
        language=language,
    )
    
    if result:
        return {"success": True, "tracking_id": result.get("message_id")}
    else:
        raise HTTPException(status_code=500, detail="Failed to send password reset email")


@router.get("/queue/status", response_model=QueueStatusResponse)
async def get_queue_status_endpoint():
    """获取邮件队列状态"""
    status = await get_queue_status()
    return status


@router.get("/stats/daily/{date}", response_model=DailyStatsResponse)
async def get_daily_stats(date: str):
    """获取每日发送统计"""
    stats_manager = get_email_stats_manager()
    stats = await stats_manager.get_daily_stats(date)
    
    if not stats:
        raise HTTPException(status_code=404, detail="No stats found for this date")
    
    return {
        "date": stats.date,
        "total_sent": stats.total_sent,
        "total_failed": stats.total_failed,
        "templates_used": stats.templates_used,
        "providers_used": stats.providers_used,
        "hourly_distribution": stats.hourly_distribution,
    }


@router.get("/stats/summary", response_model=SummaryStatsResponse)
async def get_summary_stats(days: int = Query(default=30, ge=1, le=365)):
    """获取汇总统计"""
    stats_manager = get_email_stats_manager()
    stats = await stats_manager.get_summary_stats(days)
    return stats


@router.get("/stats/realtime", response_model=RealtimeStatsResponse)
async def get_realtime_stats():
    """获取实时统计"""
    stats_manager = get_email_stats_manager()
    stats = await stats_manager.get_realtime_stats()
    return stats


@router.get("/stats/top-templates")
async def get_top_templates(
    days: int = Query(default=30, ge=1, le=365),
    limit: int = Query(default=10, ge=1, le=50),
):
    """获取热门模板"""
    stats_manager = get_email_stats_manager()
    templates = await stats_manager.get_top_templates(days, limit)
    return templates


@router.get("/records/{tracking_id}", response_model=SendRecordResponse)
async def get_send_record(tracking_id: str):
    """获取发送记录详情"""
    stats_manager = get_email_stats_manager()
    record = await stats_manager.get_send_record(tracking_id)
    
    if not record:
        raise HTTPException(status_code=404, detail="Record not found")
    
    return {
        "tracking_id": record.tracking_id,
        "recipient": record.recipient,
        "template_name": record.template_name,
        "subject": record.subject,
        "status": record.status,
        "created_at": record.created_at,
        "sent_at": record.sent_at,
        "failed_at": record.failed_at,
        "provider": record.provider,
        "opened_at": record.opened_at,
        "clicked_at": record.clicked_at,
    }


@router.post("/track/open/{tracking_id}")
async def track_email_open(tracking_id: str):
    """追踪邮件打开事件"""
    stats_manager = get_email_stats_manager()
    await stats_manager.record_open_event(tracking_id)
    return {"success": True}


@router.post("/track/click/{tracking_id}")
async def track_email_click(tracking_id: str, url: str):
    """追踪邮件点击事件"""
    stats_manager = get_email_stats_manager()
    await stats_manager.record_click_event(tracking_id, url)
    return {"success": True}


@router.get("/preferences/{user_id}")
async def get_email_preferences(user_id: int):
    """获取用户邮件偏好设置"""
    trigger = get_notification_trigger()
    prefs = await trigger._get_user_email_preferences(user_id)
    return prefs


@router.put("/preferences/{user_id}")
async def update_email_preferences(
    user_id: int,
    request: EmailPreferencesRequest,
):
    """更新用户邮件偏好设置"""
    from ..cache.redis_cache import redis_cache
    import json
    
    prefs = request.dict()
    key = f"user_email_prefs:{user_id}"
    await redis_cache.set(key, json.dumps(prefs), ttl=86400 * 365)  # 保留1年
    
    return {"success": True, "preferences": prefs}
