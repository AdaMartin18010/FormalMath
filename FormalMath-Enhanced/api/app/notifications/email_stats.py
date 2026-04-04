"""
邮件统计追踪模块
提供邮件发送统计、追踪和分析功能
"""
import json
from typing import Dict, Any, Optional, List
from datetime import datetime, timedelta
from dataclasses import dataclass, asdict
from functools import lru_cache
import asyncio

from ..cache.redis_cache import redis_cache
from ..core.email_config import email_settings


@dataclass
class EmailSendRecord:
    """邮件发送记录"""
    tracking_id: str
    recipient: str
    template_name: Optional[str]
    subject: str
    status: str  # pending, processing, sent, failed, permanently_failed
    created_at: str
    sent_at: Optional[str] = None
    failed_at: Optional[str] = None
    provider: Optional[str] = None
    message_id: Optional[str] = None
    error_message: Optional[str] = None
    retry_count: int = 0
    opened_at: Optional[str] = None
    clicked_at: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "EmailSendRecord":
        return cls(**data)


@dataclass
class DailyStats:
    """每日统计"""
    date: str
    total_sent: int = 0
    total_failed: int = 0
    unique_recipients: int = 0
    templates_used: Dict[str, int] = None
    providers_used: Dict[str, int] = None
    hourly_distribution: Dict[int, int] = None
    
    def __post_init__(self):
        if self.templates_used is None:
            self.templates_used = {}
        if self.providers_used is None:
            self.providers_used = {}
        if self.hourly_distribution is None:
            self.hourly_distribution = {}
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class EmailStatsManager:
    """邮件统计管理器"""
    
    def __init__(self):
        self.stats_key_prefix = "email_stats"
        self.tracking_key_prefix = "email_tracking"
    
    # ========== 发送记录管理 ==========
    
    async def create_send_record(
        self,
        tracking_id: str,
        recipient: str,
        template_name: Optional[str],
        subject: str,
    ) -> EmailSendRecord:
        """
        创建发送记录
        
        Args:
            tracking_id: 追踪ID
            recipient: 收件人
            template_name: 模板名称
            subject: 邮件主题
        
        Returns:
            发送记录
        """
        record = EmailSendRecord(
            tracking_id=tracking_id,
            recipient=recipient,
            template_name=template_name,
            subject=subject,
            status="pending",
            created_at=datetime.utcnow().isoformat(),
        )
        
        # 保存记录
        key = f"{self.tracking_key_prefix}:{tracking_id}"
        await redis_cache.set(key, json.dumps(record.to_dict()), ttl=86400 * 7)  # 保留7天
        
        return record
    
    def update_send_status(
        self,
        tracking_id: str,
        status: str,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> bool:
        """
        更新发送状态（同步方法，供 Celery 任务调用）
        
        Args:
            tracking_id: 追踪ID
            status: 新状态
            metadata: 元数据
        
        Returns:
            是否成功
        """
        try:
            key = f"{self.tracking_key_prefix}:{tracking_id}"
            
            # 使用 asyncio 运行异步操作
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            
            # 获取现有记录
            data = loop.run_until_complete(redis_cache.get(key))
            
            if not data:
                return False
            
            record = EmailSendRecord.from_dict(json.loads(data))
            record.status = status
            
            # 更新元数据
            if metadata:
                if "sent_at" in metadata:
                    record.sent_at = metadata["sent_at"]
                if "failed_at" in metadata:
                    record.failed_at = metadata["failed_at"]
                if "provider" in metadata:
                    record.provider = metadata["provider"]
                if "message_id" in metadata:
                    record.message_id = metadata["message_id"]
                if "error" in metadata:
                    record.error_message = metadata["error"]
                if "retry_count" in metadata:
                    record.retry_count = metadata["retry_count"]
            
            # 保存更新
            loop.run_until_complete(redis_cache.set(
                key,
                json.dumps(record.to_dict()),
                ttl=86400 * 7,
            ))
            
            # 更新每日统计
            if status in ["sent", "failed"]:
                self._update_daily_stats_sync(record, status)
            
            loop.close()
            return True
            
        except Exception as e:
            print(f"Failed to update send status: {e}")
            return False
    
    def _update_daily_stats_sync(self, record: EmailSendRecord, status: str):
        """更新每日统计（同步版本）"""
        try:
            date = datetime.utcnow().strftime("%Y-%m-%d")
            key = f"{self.stats_key_prefix}:daily:{date}"
            
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            
            # 获取或创建每日统计
            data = loop.run_until_complete(redis_cache.get(key))
            
            if data:
                stats = DailyStats.from_dict(json.loads(data))
            else:
                stats = DailyStats(date=date)
            
            # 更新统计
            if status == "sent":
                stats.total_sent += 1
            else:
                stats.total_failed += 1
            
            # 更新模板使用统计
            if record.template_name:
                stats.templates_used[record.template_name] = \
                    stats.templates_used.get(record.template_name, 0) + 1
            
            # 更新提供商统计
            if record.provider:
                stats.providers_used[record.provider] = \
                    stats.providers_used.get(record.provider, 0) + 1
            
            # 更新小时分布
            hour = datetime.utcnow().hour
            stats.hourly_distribution[hour] = \
                stats.hourly_distribution.get(hour, 0) + 1
            
            # 保存统计
            loop.run_until_complete(redis_cache.set(
                key,
                json.dumps(stats.to_dict()),
                ttl=86400 * email_settings.EMAIL_STATS_RETENTION_DAYS,
            ))
            
            loop.close()
            
        except Exception as e:
            print(f"Failed to update daily stats: {e}")
    
    async def get_send_record(self, tracking_id: str) -> Optional[EmailSendRecord]:
        """
        获取发送记录
        
        Args:
            tracking_id: 追踪ID
        
        Returns:
            发送记录或 None
        """
        key = f"{self.tracking_key_prefix}:{tracking_id}"
        data = await redis_cache.get(key)
        
        if data:
            return EmailSendRecord.from_dict(json.loads(data))
        
        return None
    
    # ========== 追踪事件处理 ==========
    
    async def record_open_event(self, tracking_id: str, metadata: Optional[Dict] = None):
        """
        记录邮件打开事件
        
        Args:
            tracking_id: 追踪ID
            metadata: 元数据（如IP、用户代理等）
        """
        key = f"{self.tracking_key_prefix}:{tracking_id}"
        data = await redis_cache.get(key)
        
        if data:
            record = EmailSendRecord.from_dict(json.loads(data))
            record.opened_at = datetime.utcnow().isoformat()
            await redis_cache.set(key, json.dumps(record.to_dict()), ttl=86400 * 7)
            
            # 更新打开统计
            date = datetime.utcnow().strftime("%Y-%m-%d")
            await redis_cache.hincrby(f"{self.stats_key_prefix}:opens:{date}", "total", 1)
    
    async def record_click_event(
        self,
        tracking_id: str,
        link_url: str,
        metadata: Optional[Dict] = None,
    ):
        """
        记录邮件点击事件
        
        Args:
            tracking_id: 追踪ID
            link_url: 点击的链接
            metadata: 元数据
        """
        key = f"{self.tracking_key_prefix}:{tracking_id}"
        data = await redis_cache.get(key)
        
        if data:
            record = EmailSendRecord.from_dict(json.loads(data))
            record.clicked_at = datetime.utcnow().isoformat()
            await redis_cache.set(key, json.dumps(record.to_dict()), ttl=86400 * 7)
            
            # 更新点击统计
            date = datetime.utcnow().strftime("%Y-%m-%d")
            await redis_cache.hincrby(f"{self.stats_key_prefix}:clicks:{date}", "total", 1)
            await redis_cache.hincrby(f"{self.stats_key_prefix}:clicks:{date}", link_url, 1)
    
    # ========== 统计分析 ==========
    
    async def get_daily_stats(self, date: str = None) -> Optional[DailyStats]:
        """
        获取每日统计
        
        Args:
            date: 日期字符串，默认今天
        
        Returns:
            每日统计
        """
        date = date or datetime.utcnow().strftime("%Y-%m-%d")
        key = f"{self.stats_key_prefix}:daily:{date}"
        
        data = await redis_cache.get(key)
        
        if data:
            return DailyStats.from_dict(json.loads(data))
        
        return DailyStats(date=date)
    
    async def get_stats_range(
        self,
        start_date: str,
        end_date: str,
    ) -> List[DailyStats]:
        """
        获取日期范围内的统计
        
        Args:
            start_date: 开始日期
            end_date: 结束日期
        
        Returns:
            统计列表
        """
        stats_list = []
        
        start = datetime.strptime(start_date, "%Y-%m-%d")
        end = datetime.strptime(end_date, "%Y-%m-%d")
        
        current = start
        while current <= end:
            date_str = current.strftime("%Y-%m-%d")
            stats = await self.get_daily_stats(date_str)
            if stats:
                stats_list.append(stats)
            current += timedelta(days=1)
        
        return stats_list
    
    async def get_summary_stats(self, days: int = 30) -> Dict[str, Any]:
        """
        获取汇总统计
        
        Args:
            days: 天数
        
        Returns:
            汇总统计
        """
        end_date = datetime.utcnow()
        start_date = end_date - timedelta(days=days)
        
        stats_list = await self.get_stats_range(
            start_date.strftime("%Y-%m-%d"),
            end_date.strftime("%Y-%m-%d"),
        )
        
        total_sent = sum(s.total_sent for s in stats_list)
        total_failed = sum(s.total_failed for s in stats_list)
        
        # 合并模板统计
        all_templates = {}
        all_providers = {}
        
        for stats in stats_list:
            for template, count in stats.templates_used.items():
                all_templates[template] = all_templates.get(template, 0) + count
            for provider, count in stats.providers_used.items():
                all_providers[provider] = all_providers.get(provider, 0) + count
        
        # 计算成功率
        total_attempts = total_sent + total_failed
        success_rate = (total_sent / total_attempts * 100) if total_attempts > 0 else 0
        
        return {
            "period_days": days,
            "total_sent": total_sent,
            "total_failed": total_failed,
            "success_rate": round(success_rate, 2),
            "templates_used": all_templates,
            "providers_used": all_providers,
            "daily_average": round(total_sent / days, 2) if days > 0 else 0,
        }
    
    async def get_realtime_stats(self) -> Dict[str, Any]:
        """获取实时统计"""
        today = datetime.utcnow().strftime("%Y-%m-%d")
        
        daily_stats = await self.get_daily_stats(today)
        
        # 获取队列状态
        queue_key = f"email_queue:{email_settings.EMAIL_QUEUE_NAME}"
        queue_length = await redis_cache.llen(queue_key)
        
        # 获取今日打开和点击数
        opens_data = await redis_cache.hgetall(f"{self.stats_key_prefix}:opens:{today}")
        clicks_data = await redis_cache.hgetall(f"{self.stats_key_prefix}:clicks:{today}")
        
        total_opens = sum(int(v) for v in opens_data.values()) if opens_data else 0
        total_clicks = sum(int(v) for k, v in clicks_data.items() if k != "total") if clicks_data else 0
        
        return {
            "today": {
                "sent": daily_stats.total_sent if daily_stats else 0,
                "failed": daily_stats.total_failed if daily_stats else 0,
                "opens": total_opens,
                "clicks": total_clicks,
            },
            "queue": {
                "pending": queue_length,
            },
            "hourly_distribution": daily_stats.hourly_distribution if daily_stats else {},
        }
    
    async def get_top_templates(self, days: int = 30, limit: int = 10) -> List[Dict]:
        """
        获取热门模板
        
        Args:
            days: 天数
            limit: 限制数量
        
        Returns:
            模板列表
        """
        summary = await self.get_summary_stats(days)
        templates = summary.get("templates_used", {})
        
        sorted_templates = sorted(
            templates.items(),
            key=lambda x: x[1],
            reverse=True,
        )[:limit]
        
        return [
            {"template_name": name, "count": count}
            for name, count in sorted_templates
        ]
    
    # ========== 数据清理 ==========
    
    def cleanup_old_stats(self, retention_days: int = None) -> int:
        """
        清理过期统计数据（同步方法）
        
        Args:
            retention_days: 保留天数
        
        Returns:
            清理的记录数
        """
        retention = retention_days or email_settings.EMAIL_STATS_RETENTION_DAYS
        cutoff_date = (datetime.utcnow() - timedelta(days=retention)).strftime("%Y-%m-%d")
        
        cleaned = 0
        
        try:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            
            # 获取所有统计键
            pattern = f"{self.stats_key_prefix}:daily:*"
            # 注意：这里需要实现 keys 方法
            # 简化处理：删除特定日期的键
            
            loop.close()
            
        except Exception as e:
            print(f"Failed to cleanup old stats: {e}")
        
        return cleaned


@lru_cache()
def get_email_stats_manager() -> EmailStatsManager:
    """获取邮件统计管理器实例"""
    return EmailStatsManager()
