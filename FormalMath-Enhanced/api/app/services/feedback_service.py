"""
反馈处理服务
处理反馈的创建、更新、查询等业务逻辑
"""
from typing import List, Dict, Optional, Tuple
from datetime import datetime, timedelta
from sqlalchemy.orm import Session
from sqlalchemy import func, desc, and_, or_
import logging

from ..models.models import (
    UserFeedback, FeedbackResponse, FeedbackProcessingLog,
    FeedbackType, FeedbackStatus, FeedbackPriority, FeedbackAnalytics,
    User
)
from .feedback_classifier import get_feedback_classifier

logger = logging.getLogger(__name__)


class FeedbackService:
    """反馈处理服务"""
    
    def __init__(self, db: Session):
        """初始化服务
        
        Args:
            db: 数据库会话
        """
        self.db = db
        self.classifier = get_feedback_classifier()
    
    # ========== 反馈CRUD操作 ==========
    
    def create_feedback(
        self,
        title: str,
        content: str,
        feedback_type: Optional[FeedbackType] = None,
        user_id: Optional[int] = None,
        related_concept_id: Optional[str] = None,
        related_page: Optional[str] = None,
        satisfaction_rating: Optional[int] = None,
        browser_info: Optional[Dict] = None,
        device_info: Optional[Dict] = None,
        session_id: Optional[str] = None
    ) -> UserFeedback:
        """创建新反馈
        
        Args:
            title: 反馈标题
            content: 反馈内容
            feedback_type: 反馈类型（可选，不提供则自动分类）
            user_id: 用户ID（可选，匿名反馈）
            related_concept_id: 相关概念ID
            related_page: 相关页面
            satisfaction_rating: 满意度评分
            browser_info: 浏览器信息
            device_info: 设备信息
            session_id: 会话ID
            
        Returns:
            创建的反馈对象
        """
        # 自动分类
        auto_type, confidence = self.classifier.classify(title, content)
        priority = self.classifier.determine_priority(title, content, auto_type)
        
        # 使用用户指定的类型或自动分类结果
        final_type = feedback_type or auto_type
        
        # 映射优先级字符串到枚举
        priority_map = {
            'critical': FeedbackPriority.CRITICAL,
            'high': FeedbackPriority.HIGH,
            'medium': FeedbackPriority.MEDIUM,
            'low': FeedbackPriority.LOW
        }
        final_priority = priority_map.get(priority, FeedbackPriority.MEDIUM)
        
        # 创建反馈
        feedback = UserFeedback(
            user_id=user_id,
            title=title,
            content=content,
            feedback_type=final_type,
            auto_classified_type=auto_type if not feedback_type else None,
            classification_confidence=confidence,
            status=FeedbackStatus.CLASSIFIED if not feedback_type else FeedbackStatus.PENDING,
            priority=final_priority,
            related_concept_id=related_concept_id,
            related_page=related_page,
            satisfaction_rating=satisfaction_rating,
            browser_info=browser_info or {},
            device_info=device_info or {},
            session_id=session_id
        )
        
        self.db.add(feedback)
        self.db.commit()
        self.db.refresh(feedback)
        
        # 记录处理日志
        self._add_processing_log(
            feedback_id=feedback.id,
            action='created',
            new_status=feedback.status,
            new_priority=feedback.priority,
            notes=f'自动分类: {auto_type.value}, 置信度: {confidence}'
        )
        
        logger.info(f"创建反馈成功: ID={feedback.id}, 类型={final_type.value}")
        return feedback
    
    def get_feedback(self, feedback_id: int) -> Optional[UserFeedback]:
        """获取单个反馈详情
        
        Args:
            feedback_id: 反馈ID
            
        Returns:
            反馈对象或None
        """
        return self.db.query(UserFeedback).filter(
            UserFeedback.id == feedback_id
        ).first()
    
    def list_feedbacks(
        self,
        status: Optional[FeedbackStatus] = None,
        feedback_type: Optional[FeedbackType] = None,
        priority: Optional[FeedbackPriority] = None,
        user_id: Optional[int] = None,
        assigned_to: Optional[int] = None,
        keyword: Optional[str] = None,
        start_date: Optional[datetime] = None,
        end_date: Optional[datetime] = None,
        page: int = 1,
        page_size: int = 20
    ) -> Tuple[List[UserFeedback], int]:
        """查询反馈列表
        
        Args:
            status: 状态筛选
            feedback_type: 类型筛选
            priority: 优先级筛选
            user_id: 用户筛选
            assigned_to: 指派人筛选
            keyword: 关键词搜索
            start_date: 开始日期
            end_date: 结束日期
            page: 页码
            page_size: 每页数量
            
        Returns:
            (反馈列表, 总数)
        """
        query = self.db.query(UserFeedback)
        
        # 应用筛选条件
        if status:
            query = query.filter(UserFeedback.status == status)
        if feedback_type:
            query = query.filter(UserFeedback.feedback_type == feedback_type)
        if priority:
            query = query.filter(UserFeedback.priority == priority)
        if user_id:
            query = query.filter(UserFeedback.user_id == user_id)
        if assigned_to:
            query = query.filter(UserFeedback.assigned_to == assigned_to)
        if keyword:
            search_filter = or_(
                UserFeedback.title.ilike(f'%{keyword}%'),
                UserFeedback.content.ilike(f'%{keyword}%')
            )
            query = query.filter(search_filter)
        if start_date:
            query = query.filter(UserFeedback.created_at >= start_date)
        if end_date:
            query = query.filter(UserFeedback.created_at <= end_date)
        
        # 计算总数
        total = query.count()
        
        # 分页
        feedbacks = query.order_by(
            desc(UserFeedback.priority),
            desc(UserFeedback.created_at)
        ).offset((page - 1) * page_size).limit(page_size).all()
        
        return feedbacks, total
    
    def update_feedback(
        self,
        feedback_id: int,
        status: Optional[FeedbackStatus] = None,
        priority: Optional[FeedbackPriority] = None,
        assigned_to: Optional[int] = None,
        resolution_notes: Optional[str] = None,
        performed_by: Optional[int] = None
    ) -> Optional[UserFeedback]:
        """更新反馈状态
        
        Args:
            feedback_id: 反馈ID
            status: 新状态
            priority: 新优先级
            assigned_to: 新指派人
            resolution_notes: 解决备注
            performed_by: 操作人ID
            
        Returns:
            更新后的反馈对象或None
        """
        feedback = self.get_feedback(feedback_id)
        if not feedback:
            return None
        
        old_status = feedback.status
        old_priority = feedback.priority
        
        # 更新字段
        if status:
            feedback.status = status
            if status == FeedbackStatus.RESOLVED and not feedback.resolved_at:
                feedback.resolved_at = datetime.utcnow()
        
        if priority:
            feedback.priority = priority
        
        if assigned_to is not None:
            feedback.assigned_to = assigned_to
        
        if resolution_notes:
            feedback.resolution_notes = resolution_notes
        
        feedback.updated_at = datetime.utcnow()
        
        self.db.commit()
        self.db.refresh(feedback)
        
        # 记录处理日志
        if status or priority:
            self._add_processing_log(
                feedback_id=feedback_id,
                action='updated',
                old_status=old_status,
                new_status=feedback.status if status else None,
                old_priority=old_priority,
                new_priority=feedback.priority if priority else None,
                performed_by=performed_by,
                notes=resolution_notes
            )
        
        logger.info(f"更新反馈成功: ID={feedback_id}")
        return feedback
    
    def delete_feedback(self, feedback_id: int) -> bool:
        """删除反馈
        
        Args:
            feedback_id: 反馈ID
            
        Returns:
            是否删除成功
        """
        feedback = self.get_feedback(feedback_id)
        if not feedback:
            return False
        
        self.db.delete(feedback)
        self.db.commit()
        
        logger.info(f"删除反馈成功: ID={feedback_id}")
        return True
    
    # ========== 回复操作 ==========
    
    def add_response(
        self,
        feedback_id: int,
        content: str,
        responder_id: int,
        is_internal: bool = False
    ) -> Optional[FeedbackResponse]:
        """添加回复
        
        Args:
            feedback_id: 反馈ID
            content: 回复内容
            responder_id: 回复人ID
            is_internal: 是否内部备注
            
        Returns:
            创建的回复对象或None
        """
        feedback = self.get_feedback(feedback_id)
        if not feedback:
            return None
        
        response = FeedbackResponse(
            feedback_id=feedback_id,
            responder_id=responder_id,
            content=content,
            is_internal=is_internal
        )
        
        self.db.add(response)
        
        # 如果不是内部备注，更新反馈状态为审核中
        if not is_internal and feedback.status == FeedbackStatus.CLASSIFIED:
            feedback.status = FeedbackStatus.UNDER_REVIEW
        
        self.db.commit()
        self.db.refresh(response)
        
        # 记录处理日志
        self._add_processing_log(
            feedback_id=feedback_id,
            action='response_added',
            performed_by=responder_id,
            notes=f'{"内部" if is_internal else "公开"}回复已添加'
        )
        
        logger.info(f"添加回复成功: FeedbackID={feedback_id}")
        return response
    
    # ========== 统计和分析 ==========
    
    def get_statistics(
        self,
        start_date: Optional[datetime] = None,
        end_date: Optional[datetime] = None
    ) -> Dict:
        """获取反馈统计数据
        
        Args:
            start_date: 开始日期
            end_date: 结束日期
            
        Returns:
            统计数据
        """
        query = self.db.query(UserFeedback)
        
        if start_date:
            query = query.filter(UserFeedback.created_at >= start_date)
        if end_date:
            query = query.filter(UserFeedback.created_at <= end_date)
        
        # 基础统计
        total = query.count()
        
        # 按类型统计
        type_stats = self.db.query(
            UserFeedback.feedback_type,
            func.count(UserFeedback.id)
        ).group_by(UserFeedback.feedback_type).all()
        
        # 按状态统计
        status_stats = self.db.query(
            UserFeedback.status,
            func.count(UserFeedback.id)
        ).group_by(UserFeedback.status).all()
        
        # 按优先级统计
        priority_stats = self.db.query(
            UserFeedback.priority,
            func.count(UserFeedback.id)
        ).group_by(UserFeedback.priority).all()
        
        # 平均解决时间
        resolved_feedbacks = self.db.query(UserFeedback).filter(
            UserFeedback.status == FeedbackStatus.RESOLVED,
            UserFeedback.resolved_at.isnot(None)
        ).all()
        
        avg_resolution_hours = 0
        if resolved_feedbacks:
            total_hours = sum(
                (f.resolved_at - f.created_at).total_seconds() / 3600
                for f in resolved_feedbacks
            )
            avg_resolution_hours = total_hours / len(resolved_feedbacks)
        
        # 满意度统计
        satisfaction_data = self.db.query(
            UserFeedback.satisfaction_rating,
            func.count(UserFeedback.id)
        ).filter(
            UserFeedback.satisfaction_rating.isnot(None)
        ).group_by(UserFeedback.satisfaction_rating).all()
        
        return {
            'total_feedbacks': total,
            'by_type': {t.value: c for t, c in type_stats},
            'by_status': {s.value: c for s, c in status_stats},
            'by_priority': {p.value: c for p, c in priority_stats},
            'avg_resolution_hours': round(avg_resolution_hours, 2),
            'resolved_count': len(resolved_feedbacks),
            'satisfaction_distribution': {r: c for r, c in satisfaction_data}
        }
    
    def get_trend_data(
        self,
        days: int = 30,
        group_by: str = 'day'  # day, week, month
    ) -> List[Dict]:
        """获取反馈趋势数据
        
        Args:
            days: 天数
            group_by: 分组方式
            
        Returns:
            趋势数据列表
        """
        end_date = datetime.utcnow()
        start_date = end_date - timedelta(days=days)
        
        # 根据分组方式选择时间格式
        if group_by == 'day':
            date_format = func.date(UserFeedback.created_at)
        elif group_by == 'week':
            date_format = func.date_trunc('week', UserFeedback.created_at)
        else:  # month
            date_format = func.date_trunc('month', UserFeedback.created_at)
        
        results = self.db.query(
            date_format.label('period'),
            func.count(UserFeedback.id).label('count')
        ).filter(
            UserFeedback.created_at >= start_date
        ).group_by('period').order_by('period').all()
        
        return [
            {
                'period': r.period.isoformat() if hasattr(r.period, 'isoformat') else str(r.period),
                'count': r.count
            }
            for r in results
        ]
    
    def get_dashboard_summary(self) -> Dict:
        """获取仪表板摘要数据
        
        Returns:
            仪表板数据
        """
        now = datetime.utcnow()
        
        # 今日反馈
        today_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
        today_count = self.db.query(UserFeedback).filter(
            UserFeedback.created_at >= today_start
        ).count()
        
        # 待处理反馈
        pending_count = self.db.query(UserFeedback).filter(
            UserFeedback.status.in_([
                FeedbackStatus.PENDING,
                FeedbackStatus.CLASSIFIED,
                FeedbackStatus.UNDER_REVIEW
            ])
        ).count()
        
        # 紧急反馈
        critical_count = self.db.query(UserFeedback).filter(
            UserFeedback.priority == FeedbackPriority.CRITICAL,
            UserFeedback.status != FeedbackStatus.RESOLVED
        ).count()
        
        # 本周统计
        week_start = now - timedelta(days=7)
        week_stats = self.get_statistics(start_date=week_start)
        
        # 最新反馈
        recent_feedbacks = self.db.query(UserFeedback).order_by(
            desc(UserFeedback.created_at)
        ).limit(5).all()
        
        return {
            'today_count': today_count,
            'pending_count': pending_count,
            'critical_count': critical_count,
            'week_stats': week_stats,
            'recent_feedbacks': [
                {
                    'id': f.id,
                    'title': f.title,
                    'type': f.feedback_type.value,
                    'priority': f.priority.value,
                    'status': f.status.value,
                    'created_at': f.created_at.isoformat()
                }
                for f in recent_feedbacks
            ]
        }
    
    # ========== 私有方法 ==========
    
    def _add_processing_log(
        self,
        feedback_id: int,
        action: str,
        old_status: Optional[FeedbackStatus] = None,
        new_status: Optional[FeedbackStatus] = None,
        old_priority: Optional[FeedbackPriority] = None,
        new_priority: Optional[FeedbackPriority] = None,
        performed_by: Optional[int] = None,
        notes: Optional[str] = None
    ) -> None:
        """添加处理日志"""
        log = FeedbackProcessingLog(
            feedback_id=feedback_id,
            action=action,
            old_status=old_status,
            new_status=new_status,
            old_priority=old_priority,
            new_priority=new_priority,
            performed_by=performed_by,
            notes=notes
        )
        self.db.add(log)
        self.db.commit()


def get_feedback_service(db: Session) -> FeedbackService:
    """获取反馈服务实例
    
    Args:
        db: 数据库会话
        
    Returns:
        FeedbackService实例
    """
    return FeedbackService(db)
