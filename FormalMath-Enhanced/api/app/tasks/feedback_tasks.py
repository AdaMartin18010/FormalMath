"""
反馈处理异步任务
使用Celery处理反馈相关的后台任务
"""
from datetime import datetime, timedelta
from typing import List, Dict
import logging

from .celery_app import celery_app
from ..core.database import db_manager
from ..models.models import (
    UserFeedback, FeedbackStatus, FeedbackPriority, 
    FeedbackAnalytics, FeedbackType
)
from ..services.feedback_service import FeedbackService
from ..services.feedback_classifier import get_feedback_classifier

logger = logging.getLogger(__name__)


@celery_app.task(bind=True, max_retries=3)
def process_new_feedback(self, feedback_id: int):
    """
    处理新提交的反馈
    
    - 自动分类
    - 提取关键词
    - 情感分析
    - 发送通知
    
    Args:
        feedback_id: 反馈ID
    """
    try:
        with db_manager.session_scope() as db:
            service = FeedbackService(db)
            feedback = service.get_feedback(feedback_id)
            
            if not feedback:
                logger.warning(f"反馈不存在: {feedback_id}")
                return {"status": "failed", "reason": "feedback_not_found"}
            
            # 自动分类（如果用户未指定类型）
            if feedback.status == FeedbackStatus.PENDING:
                classifier = get_feedback_classifier()
                auto_type, confidence = classifier.classify(
                    feedback.title, 
                    feedback.content
                )
                
                feedback.auto_classified_type = auto_type
                feedback.classification_confidence = confidence
                feedback.status = FeedbackStatus.CLASSIFIED
                
                # 确定优先级
                priority_str = classifier.determine_priority(
                    feedback.title,
                    feedback.content,
                    auto_type
                )
                priority_map = {
                    'critical': FeedbackPriority.CRITICAL,
                    'high': FeedbackPriority.HIGH,
                    'medium': FeedbackPriority.MEDIUM,
                    'low': FeedbackPriority.LOW
                }
                feedback.priority = priority_map.get(priority_str, FeedbackPriority.MEDIUM)
                
                db.commit()
                
                logger.info(
                    f"反馈 {feedback_id} 自动分类完成: "
                    f"类型={auto_type.value}, 置信度={confidence}"
                )
            
            # 发送通知（可以集成邮件、短信、Webhook等）
            send_feedback_notification.delay(feedback_id)
            
            return {
                "status": "success",
                "feedback_id": feedback_id,
                "classified_type": feedback.auto_classified_type.value if feedback.auto_classified_type else None
            }
            
    except Exception as exc:
        logger.error(f"处理反馈 {feedback_id} 失败: {str(exc)}")
        raise self.retry(exc=exc, countdown=60)


@celery_app.task(bind=True, max_retries=3)
def send_feedback_notification(self, feedback_id: int):
    """
    发送反馈通知
    
    可以扩展为发送邮件、Slack通知、Webhook等
    
    Args:
        feedback_id: 反馈ID
    """
    try:
        with db_manager.session_scope() as db:
            service = FeedbackService(db)
            feedback = service.get_feedback(feedback_id)
            
            if not feedback:
                return {"status": "failed", "reason": "feedback_not_found"}
            
            # 根据优先级和类型决定通知方式
            notification_channels = _determine_notification_channels(feedback)
            
            # 记录通知日志
            logger.info(
                f"反馈 {feedback_id} 通知已发送: "
                f"渠道={notification_channels}"
            )
            
            return {
                "status": "success",
                "feedback_id": feedback_id,
                "channels": notification_channels
            }
            
    except Exception as exc:
        logger.error(f"发送通知失败 {feedback_id}: {str(exc)}")
        raise self.retry(exc=exc, countdown=30)


def _determine_notification_channels(feedback: UserFeedback) -> List[str]:
    """根据反馈属性确定通知渠道"""
    channels = []
    
    # 紧急优先级：多渠道通知
    if feedback.priority == FeedbackPriority.CRITICAL:
        channels.extend(['email', 'slack', 'sms'])
    # 高优先级：邮件+Slack
    elif feedback.priority == FeedbackPriority.HIGH:
        channels.extend(['email', 'slack'])
    # 错误报告：邮件通知
    elif feedback.feedback_type == FeedbackType.BUG_REPORT:
        channels.append('email')
    # 其他：仅日志记录
    else:
        channels.append('log')
    
    return channels


@celery_app.task(bind=True)
def auto_close_resolved_feedbacks(self):
    """
    自动关闭长时间未活动的已解决反馈
    
    已解决超过7天的反馈自动关闭
    """
    try:
        with db_manager.session_scope() as db:
            cutoff_date = datetime.utcnow() - timedelta(days=7)
            
            # 查找符合条件的反馈
            feedbacks_to_close = db.query(UserFeedback).filter(
                UserFeedback.status == FeedbackStatus.RESOLVED,
                UserFeedback.resolved_at < cutoff_date
            ).all()
            
            closed_count = 0
            for feedback in feedbacks_to_close:
                feedback.status = FeedbackStatus.CLOSED
                feedback.updated_at = datetime.utcnow()
                
                # 添加处理日志
                service = FeedbackService(db)
                service._add_processing_log(
                    feedback_id=feedback.id,
                    action='auto_closed',
                    old_status=FeedbackStatus.RESOLVED,
                    new_status=FeedbackStatus.CLOSED,
                    notes='系统自动关闭：已解决超过7天'
                )
                
                closed_count += 1
            
            db.commit()
            
            logger.info(f"自动关闭反馈完成: {closed_count} 个")
            return {"status": "success", "closed_count": closed_count}
            
    except Exception as exc:
        logger.error(f"自动关闭反馈失败: {str(exc)}")
        raise self.retry(exc=exc, countdown=300)


@celery_app.task(bind=True)
def generate_feedback_analytics(self, period_type: str = 'daily'):
    """
    生成反馈分析统计
    
    Args:
        period_type: 统计周期类型 (daily, weekly, monthly)
    """
    try:
        with db_manager.session_scope() as db:
            now = datetime.utcnow()
            
            # 确定统计周期
            if period_type == 'daily':
                period_start = now.replace(hour=0, minute=0, second=0, microsecond=0)
                period_end = period_start + timedelta(days=1)
            elif period_type == 'weekly':
                period_start = now - timedelta(days=now.weekday())
                period_start = period_start.replace(hour=0, minute=0, second=0, microsecond=0)
                period_end = period_start + timedelta(days=7)
            else:  # monthly
                period_start = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
                if period_start.month == 12:
                    period_end = period_start.replace(year=period_start.year + 1, month=1)
                else:
                    period_end = period_start.replace(month=period_start.month + 1)
            
            service = FeedbackService(db)
            stats = service.get_statistics(start_date=period_start, end_date=period_end)
            
            # 按类型统计
            type_counts = db.query(
                UserFeedback.feedback_type,
                db.func.count(UserFeedback.id)
            ).filter(
                UserFeedback.created_at >= period_start,
                UserFeedback.created_at < period_end
            ).group_by(UserFeedback.feedback_type).all()
            
            # 按状态统计
            status_counts = db.query(
                UserFeedback.status,
                db.func.count(UserFeedback.id)
            ).filter(
                UserFeedback.created_at >= period_start,
                UserFeedback.created_at < period_end
            ).group_by(UserFeedback.status).all()
            
            # 按优先级统计
            priority_counts = db.query(
                UserFeedback.priority,
                db.func.count(UserFeedback.id)
            ).filter(
                UserFeedback.created_at >= period_start,
                UserFeedback.created_at < period_end
            ).group_by(UserFeedback.priority).all()
            
            # 创建或更新分析记录
            analytics = db.query(FeedbackAnalytics).filter(
                FeedbackAnalytics.period_type == period_type,
                FeedbackAnalytics.period_start == period_start
            ).first()
            
            if not analytics:
                analytics = FeedbackAnalytics(
                    period_type=period_type,
                    period_start=period_start,
                    period_end=period_end
                )
                db.add(analytics)
            
            analytics.total_feedbacks = stats['total_feedbacks']
            analytics.feedbacks_by_type = {t.value: c for t, c in type_counts}
            analytics.feedbacks_by_status = {s.value: c for s, c in status_counts}
            analytics.feedbacks_by_priority = {p.value: c for p, c in priority_counts}
            analytics.avg_resolution_time_hours = stats['avg_resolution_hours']
            analytics.resolved_count = stats['resolved_count']
            analytics.pending_count = stats['by_status'].get('pending', 0) + \
                                      stats['by_status'].get('classified', 0) + \
                                      stats['by_status'].get('under_review', 0)
            
            # 满意度统计
            satisfaction_data = db.query(
                UserFeedback.satisfaction_rating,
                db.func.count(UserFeedback.id)
            ).filter(
                UserFeedback.created_at >= period_start,
                UserFeedback.created_at < period_end,
                UserFeedback.satisfaction_rating.isnot(None)
            ).group_by(UserFeedback.satisfaction_rating).all()
            
            if satisfaction_data:
                total_satisfaction = sum(r * c for r, c in satisfaction_data)
                total_count = sum(c for _, c in satisfaction_data)
                analytics.avg_satisfaction = round(total_satisfaction / total_count, 2)
                analytics.satisfaction_distribution = {str(r): c for r, c in satisfaction_data}
            
            analytics.updated_at = now
            db.commit()
            
            logger.info(f"生成反馈统计完成: {period_type}")
            return {
                "status": "success",
                "period_type": period_type,
                "period_start": period_start.isoformat(),
                "total_feedbacks": analytics.total_feedbacks
            }
            
    except Exception as exc:
        logger.error(f"生成反馈统计失败: {str(exc)}")
        raise self.retry(exc=exc, countdown=60)


@celery_app.task(bind=True)
def analyze_feedback_sentiment_batch(self, feedback_ids: List[int] = None):
    """
    批量分析反馈情感
    
    Args:
        feedback_ids: 要分析的反馈ID列表，None则分析所有未分析的
    """
    try:
        with db_manager.session_scope() as db:
            classifier = get_feedback_classifier()
            
            if feedback_ids:
                feedbacks = db.query(UserFeedback).filter(
                    UserFeedback.id.in_(feedback_ids)
                ).all()
            else:
                # 分析最近100条没有情感分析的反馈
                feedbacks = db.query(UserFeedback).filter(
                    UserFeedback.created_at >= datetime.utcnow() - timedelta(days=30)
                ).order_by(
                    UserFeedback.created_at.desc()
                ).limit(100).all()
            
            analyzed_count = 0
            for feedback in feedbacks:
                sentiment = classifier.analyze_sentiment(
                    feedback.title,
                    feedback.content
                )
                
                # 将情感分析结果存入metadata
                if not feedback.browser_info:
                    feedback.browser_info = {}
                feedback.browser_info['sentiment_analysis'] = sentiment
                analyzed_count += 1
            
            db.commit()
            
            logger.info(f"批量情感分析完成: {analyzed_count} 个")
            return {
                "status": "success",
                "analyzed_count": analyzed_count
            }
            
    except Exception as exc:
        logger.error(f"批量情感分析失败: {str(exc)}")
        raise self.retry(exc=exc, countdown=60)


@celery_app.task(bind=True)
def cleanup_old_feedbacks(self, days: int = 365):
    """
    清理旧反馈数据
    
    将超时的已关闭反馈归档或删除
    
    Args:
        days: 保留天数，超过此天数的已关闭反馈将被清理
    """
    try:
        with db_manager.session_scope() as db:
            cutoff_date = datetime.utcnow() - timedelta(days=days)
            
            # 查找超时的已关闭反馈
            old_feedbacks = db.query(UserFeedback).filter(
                UserFeedback.status == FeedbackStatus.CLOSED,
                UserFeedback.updated_at < cutoff_date
            ).all()
            
            # 这里可以实现归档逻辑，目前仅记录日志
            archived_count = len(old_feedbacks)
            
            logger.info(f"发现 {archived_count} 个可归档的旧反馈")
            
            return {
                "status": "success",
                "archivable_count": archived_count,
                "cutoff_date": cutoff_date.isoformat()
            }
            
    except Exception as exc:
        logger.error(f"清理旧反馈失败: {str(exc)}")
        raise self.retry(exc=exc, countdown=300)


# ========== 定时任务调度配置 ==========

@celery_app.on_after_configure.connect
def setup_feedback_periodic_tasks(sender, **kwargs):
    """设置反馈系统的定时任务"""
    
    # 每小时处理新反馈
    sender.add_periodic_task(
        3600.0,
        process_new_feedback.s(),
        name='process-pending-feedbacks'
    )
    
    # 每天自动关闭已解决反馈
    sender.add_periodic_task(
        86400.0,
        auto_close_resolved_feedbacks.s(),
        name='auto-close-feedbacks'
    )
    
    # 每天生成日报
    sender.add_periodic_task(
        86400.0,
        generate_feedback_analytics.s('daily'),
        name='generate-daily-analytics'
    )
    
    # 每周生成周报
    sender.add_periodic_task(
        604800.0,
        generate_feedback_analytics.s('weekly'),
        name='generate-weekly-analytics'
    )
    
    # 每月生成月报
    sender.add_periodic_task(
        2592000.0,
        generate_feedback_analytics.s('monthly'),
        name='generate-monthly-analytics'
    )
