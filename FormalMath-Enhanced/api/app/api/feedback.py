"""
用户反馈API路由
提供反馈的提交、查询、管理等功能
"""
from typing import List, Dict, Optional, Any
from datetime import datetime, timedelta
from fastapi import APIRouter, Depends, HTTPException, Query, Body
from pydantic import BaseModel, Field
from sqlalchemy.orm import Session

from ..core.database import get_db
from ..models.models import (
    FeedbackType, FeedbackStatus, FeedbackPriority,
    UserFeedback, User
)
from ..services.feedback_service import get_feedback_service, FeedbackService
from ..services.feedback_classifier import get_feedback_classifier

router = APIRouter()


# ========== 请求/响应模型 ==========

class CreateFeedbackRequest(BaseModel):
    """创建反馈请求"""
    title: str = Field(..., description="反馈标题", min_length=1, max_length=255)
    content: str = Field(..., description="反馈内容", min_length=1, max_length=5000)
    feedback_type: Optional[str] = Field(None, description="反馈类型")
    related_concept_id: Optional[str] = Field(None, description="相关概念ID")
    related_page: Optional[str] = Field(None, description="相关页面URL")
    satisfaction_rating: Optional[int] = Field(None, description="满意度评分(1-5)", ge=1, le=5)
    browser_info: Optional[Dict[str, Any]] = Field(None, description="浏览器信息")
    device_info: Optional[Dict[str, Any]] = Field(None, description="设备信息")
    session_id: Optional[str] = Field(None, description="会话ID")


class UpdateFeedbackRequest(BaseModel):
    """更新反馈请求"""
    status: Optional[str] = Field(None, description="新状态")
    priority: Optional[str] = Field(None, description="新优先级")
    assigned_to: Optional[int] = Field(None, description="指派人ID")
    resolution_notes: Optional[str] = Field(None, description="解决备注")


class AddResponseRequest(BaseModel):
    """添加回复请求"""
    content: str = Field(..., description="回复内容", min_length=1, max_length=3000)
    is_internal: bool = Field(False, description="是否内部备注")
    responder_id: int = Field(..., description="回复人ID")


class FeedbackFilterRequest(BaseModel):
    """反馈筛选请求"""
    status: Optional[str] = Field(None, description="状态筛选")
    feedback_type: Optional[str] = Field(None, description="类型筛选")
    priority: Optional[str] = Field(None, description="优先级筛选")
    keyword: Optional[str] = Field(None, description="关键词搜索")
    start_date: Optional[datetime] = Field(None, description="开始日期")
    end_date: Optional[datetime] = Field(None, description="结束日期")
    page: int = Field(1, description="页码", ge=1)
    page_size: int = Field(20, description="每页数量", ge=1, le=100)


class FeedbackPreview(BaseModel):
    """反馈预览"""
    id: int
    title: str
    feedback_type: str
    status: str
    priority: str
    created_at: str
    
    class Config:
        from_attributes = True


class FeedbackDetail(BaseModel):
    """反馈详情"""
    id: int
    title: str
    content: str
    feedback_type: str
    auto_classified_type: Optional[str]
    classification_confidence: float
    status: str
    priority: str
    related_concept_id: Optional[str]
    related_page: Optional[str]
    satisfaction_rating: Optional[int]
    browser_info: Dict[str, Any]
    device_info: Dict[str, Any]
    created_at: str
    updated_at: str
    resolved_at: Optional[str]
    resolution_notes: Optional[str]
    
    class Config:
        from_attributes = True


class ClassificationResult(BaseModel):
    """分类结果"""
    feedback_type: str
    confidence: float
    priority: str
    keywords: List[str]
    sentiment: Dict[str, Any]


# ========== 辅助函数 ==========

def parse_feedback_type(type_str: Optional[str]) -> Optional[FeedbackType]:
    """解析反馈类型字符串"""
    if not type_str:
        return None
    try:
        return FeedbackType(type_str)
    except ValueError:
        raise HTTPException(status_code=400, detail=f"无效的反馈类型: {type_str}")


def parse_feedback_status(status_str: Optional[str]) -> Optional[FeedbackStatus]:
    """解析反馈状态字符串"""
    if not status_str:
        return None
    try:
        return FeedbackStatus(status_str)
    except ValueError:
        raise HTTPException(status_code=400, detail=f"无效的反馈状态: {status_str}")


def parse_feedback_priority(priority_str: Optional[str]) -> Optional[FeedbackPriority]:
    """解析反馈优先级字符串"""
    if not priority_str:
        return None
    try:
        return FeedbackPriority(priority_str)
    except ValueError:
        raise HTTPException(status_code=400, detail=f"无效的反馈优先级: {priority_str}")


# ========== API端点 ==========

@router.post("/feedbacks", response_model=Dict, summary="提交反馈")
async def create_feedback(
    request: CreateFeedbackRequest,
    user_id: Optional[int] = None,
    service: FeedbackService = Depends(lambda db: get_feedback_service(db)),
    db: Session = Depends(get_db)
):
    """
    提交新的用户反馈
    
    如果未指定feedback_type，系统将自动进行分类。
    """
    try:
        feedback_type = parse_feedback_type(request.feedback_type)
        
        feedback = service.create_feedback(
            title=request.title,
            content=request.content,
            feedback_type=feedback_type,
            user_id=user_id,
            related_concept_id=request.related_concept_id,
            related_page=request.related_page,
            satisfaction_rating=request.satisfaction_rating,
            browser_info=request.browser_info,
            device_info=request.device_info,
            session_id=request.session_id
        )
        
        return {
            "success": True,
            "data": {
                "id": feedback.id,
                "feedback_type": feedback.feedback_type.value,
                "status": feedback.status.value,
                "priority": feedback.priority.value,
                "message": "反馈提交成功"
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"提交反馈失败: {str(e)}")


@router.get("/feedbacks", response_model=Dict, summary="获取反馈列表")
async def list_feedbacks(
    status: Optional[str] = Query(None, description="状态筛选"),
    feedback_type: Optional[str] = Query(None, description="类型筛选"),
    priority: Optional[str] = Query(None, description="优先级筛选"),
    keyword: Optional[str] = Query(None, description="关键词搜索"),
    page: int = Query(1, description="页码", ge=1),
    page_size: int = Query(20, description="每页数量", ge=1, le=100),
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """查询反馈列表，支持多种筛选条件"""
    try:
        feedbacks, total = service.list_feedbacks(
            status=parse_feedback_status(status),
            feedback_type=parse_feedback_type(feedback_type),
            priority=parse_feedback_priority(priority),
            keyword=keyword,
            page=page,
            page_size=page_size
        )
        
        return {
            "success": True,
            "data": {
                "items": [
                    {
                        "id": f.id,
                        "title": f.title,
                        "feedback_type": f.feedback_type.value,
                        "status": f.status.value,
                        "priority": f.priority.value,
                        "created_at": f.created_at.isoformat()
                    }
                    for f in feedbacks
                ],
                "total": total,
                "page": page,
                "page_size": page_size,
                "total_pages": (total + page_size - 1) // page_size
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取反馈列表失败: {str(e)}")


@router.get("/feedbacks/{feedback_id}", response_model=Dict, summary="获取反馈详情")
async def get_feedback(
    feedback_id: int,
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """获取单个反馈的详细信息"""
    feedback = service.get_feedback(feedback_id)
    if not feedback:
        raise HTTPException(status_code=404, detail="反馈不存在")
    
    return {
        "success": True,
        "data": {
            "id": feedback.id,
            "title": feedback.title,
            "content": feedback.content,
            "feedback_type": feedback.feedback_type.value,
            "auto_classified_type": feedback.auto_classified_type.value if feedback.auto_classified_type else None,
            "classification_confidence": feedback.classification_confidence,
            "status": feedback.status.value,
            "priority": feedback.priority.value,
            "related_concept_id": feedback.related_concept_id,
            "related_page": feedback.related_page,
            "satisfaction_rating": feedback.satisfaction_rating,
            "browser_info": feedback.browser_info,
            "device_info": feedback.device_info,
            "resolution_notes": feedback.resolution_notes,
            "created_at": feedback.created_at.isoformat(),
            "updated_at": feedback.updated_at.isoformat(),
            "resolved_at": feedback.resolved_at.isoformat() if feedback.resolved_at else None,
            "responses": [
                {
                    "id": r.id,
                    "content": r.content,
                    "responder_id": r.responder_id,
                    "is_internal": r.is_internal,
                    "created_at": r.created_at.isoformat()
                }
                for r in feedback.responses if not r.is_internal
            ]
        }
    }


@router.put("/feedbacks/{feedback_id}", response_model=Dict, summary="更新反馈")
async def update_feedback(
    feedback_id: int,
    request: UpdateFeedbackRequest,
    performed_by: Optional[int] = None,
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """更新反馈状态、优先级等信息"""
    try:
        feedback = service.update_feedback(
            feedback_id=feedback_id,
            status=parse_feedback_status(request.status),
            priority=parse_feedback_priority(request.priority),
            assigned_to=request.assigned_to,
            resolution_notes=request.resolution_notes,
            performed_by=performed_by
        )
        
        if not feedback:
            raise HTTPException(status_code=404, detail="反馈不存在")
        
        return {
            "success": True,
            "data": {
                "id": feedback.id,
                "status": feedback.status.value,
                "priority": feedback.priority.value,
                "message": "反馈更新成功"
            }
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"更新反馈失败: {str(e)}")


@router.delete("/feedbacks/{feedback_id}", response_model=Dict, summary="删除反馈")
async def delete_feedback(
    feedback_id: int,
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """删除反馈"""
    success = service.delete_feedback(feedback_id)
    if not success:
        raise HTTPException(status_code=404, detail="反馈不存在")
    
    return {
        "success": True,
        "data": {"message": "反馈删除成功"}
    }


@router.post("/feedbacks/{feedback_id}/responses", response_model=Dict, summary="添加回复")
async def add_response(
    feedback_id: int,
    request: AddResponseRequest,
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """为反馈添加回复"""
    try:
        response = service.add_response(
            feedback_id=feedback_id,
            content=request.content,
            responder_id=request.responder_id,
            is_internal=request.is_internal
        )
        
        if not response:
            raise HTTPException(status_code=404, detail="反馈不存在")
        
        return {
            "success": True,
            "data": {
                "id": response.id,
                "feedback_id": response.feedback_id,
                "created_at": response.created_at.isoformat(),
                "message": "回复添加成功"
            }
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"添加回复失败: {str(e)}")


# ========== 分类相关API ==========

@router.post("/classify", response_model=Dict, summary="反馈预分类")
async def preview_classification(
    title: str = Body(..., description="反馈标题"),
    content: str = Body(..., description="反馈内容")
):
    """
    预览反馈自动分类结果
    
    在不提交反馈的情况下，预先查看系统的分类建议。
    """
    try:
        classifier = get_feedback_classifier()
        result = classifier.get_classification_details(title, content)
        
        return {
            "success": True,
            "data": result
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"分类失败: {str(e)}")


@router.get("/types", response_model=Dict, summary="获取反馈类型列表")
async def get_feedback_types():
    """获取所有可用的反馈类型"""
    return {
        "success": True,
        "data": {
            "types": [
                {"value": t.value, "label": _get_type_label(t)}
                for t in FeedbackType
            ]
        }
    }


@router.get("/statuses", response_model=Dict, summary="获取反馈状态列表")
async def get_feedback_statuses():
    """获取所有可用的反馈状态"""
    return {
        "success": True,
        "data": {
            "statuses": [
                {"value": s.value, "label": _get_status_label(s)}
                for s in FeedbackStatus
            ]
        }
    }


@router.get("/priorities", response_model=Dict, summary="获取反馈优先级列表")
async def get_feedback_priorities():
    """获取所有可用的反馈优先级"""
    return {
        "success": True,
        "data": {
            "priorities": [
                {"value": p.value, "label": _get_priority_label(p)}
                for p in FeedbackPriority
            ]
        }
    }


def _get_type_label(feedback_type: FeedbackType) -> str:
    """获取反馈类型的中文标签"""
    labels = {
        FeedbackType.BUG_REPORT: "错误报告",
        FeedbackType.FEATURE_REQUEST: "功能请求",
        FeedbackType.CONTENT_ERROR: "内容错误",
        FeedbackType.USABILITY: "可用性问题",
        FeedbackType.PERFORMANCE: "性能问题",
        FeedbackType.GENERAL: "一般反馈",
        FeedbackType.COMPLAINT: "投诉",
        FeedbackType.COMPLIMENT: "表扬"
    }
    return labels.get(feedback_type, feedback_type.value)


def _get_status_label(status: FeedbackStatus) -> str:
    """获取反馈状态的中文标签"""
    labels = {
        FeedbackStatus.PENDING: "待处理",
        FeedbackStatus.CLASSIFIED: "已分类",
        FeedbackStatus.UNDER_REVIEW: "审核中",
        FeedbackStatus.IN_PROGRESS: "处理中",
        FeedbackStatus.RESOLVED: "已解决",
        FeedbackStatus.CLOSED: "已关闭",
        FeedbackStatus.REJECTED: "已拒绝"
    }
    return labels.get(status, status.value)


def _get_priority_label(priority: FeedbackPriority) -> str:
    """获取反馈优先级的中文标签"""
    labels = {
        FeedbackPriority.CRITICAL: "紧急",
        FeedbackPriority.HIGH: "高",
        FeedbackPriority.MEDIUM: "中",
        FeedbackPriority.LOW: "低"
    }
    return labels.get(priority, priority.value)


# ========== 统计和分析API ==========

@router.get("/statistics", response_model=Dict, summary="获取反馈统计")
async def get_statistics(
    days: int = Query(30, description="统计天数", ge=1, le=365),
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """获取反馈统计数据"""
    try:
        start_date = datetime.utcnow() - timedelta(days=days)
        stats = service.get_statistics(start_date=start_date)
        
        return {
            "success": True,
            "data": stats
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取统计失败: {str(e)}")


@router.get("/trends", response_model=Dict, summary="获取反馈趋势")
async def get_trends(
    days: int = Query(30, description="天数", ge=7, le=365),
    group_by: str = Query("day", description="分组方式: day, week, month"),
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """获取反馈趋势数据"""
    try:
        trend_data = service.get_trend_data(days=days, group_by=group_by)
        
        return {
            "success": True,
            "data": {
                "trends": trend_data,
                "days": days,
                "group_by": group_by
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取趋势失败: {str(e)}")


# ========== 仪表板API ==========

@router.get("/dashboard/summary", response_model=Dict, summary="仪表板摘要")
async def get_dashboard_summary(
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """获取反馈仪表板摘要数据"""
    try:
        summary = service.get_dashboard_summary()
        
        return {
            "success": True,
            "data": summary
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取仪表板数据失败: {str(e)}")


@router.get("/dashboard/overview", response_model=Dict, summary="仪表板概览")
async def get_dashboard_overview(
    service: FeedbackService = Depends(lambda db: get_feedback_service(db))
):
    """获取反馈系统的完整仪表板概览"""
    try:
        # 今日数据
        now = datetime.utcnow()
        today_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
        
        # 30天统计
        month_start = now - timedelta(days=30)
        month_stats = service.get_statistics(start_date=month_start)
        
        # 7天趋势
        week_trends = service.get_trend_data(days=7, group_by='day')
        
        # 摘要
        summary = service.get_dashboard_summary()
        
        return {
            "success": True,
            "data": {
                "summary": summary,
                "month_stats": month_stats,
                "week_trends": week_trends,
                "last_updated": now.isoformat()
            }
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取仪表板概览失败: {str(e)}")
