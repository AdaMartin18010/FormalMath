"""
通知触发逻辑模块
定义各种业务场景下的邮件通知触发机制
"""
from typing import Dict, Any, Optional, List
from datetime import datetime, timedelta
from enum import Enum
from functools import lru_cache

from .email_service import get_email_service, EmailService
from .template_manager import get_template_manager, TemplateManager
from ..core.email_config import email_settings
from ..cache.redis_cache import redis_cache


class NotificationType(str, Enum):
    """通知类型枚举"""
    WELCOME = "welcome"
    VERIFICATION = "verification"
    PASSWORD_RESET = "password_reset"
    LEARNING_REMINDER = "learning_reminder"
    ACHIEVEMENT_UNLOCKED = "achievement_unlocked"
    LEARNING_PATH_COMPLETE = "learning_path_complete"
    WEEKLY_REPORT = "weekly_report"
    NEW_FOLLOWER = "new_follower"
    CHALLENGE_INVITATION = "challenge_invitation"
    SYSTEM_MAINTENANCE = "system_maintenance"
    SECURITY_ALERT = "security_alert"


class NotificationTrigger:
    """通知触发器"""
    
    def __init__(
        self,
        email_service: Optional[EmailService] = None,
        template_manager: Optional[TemplateManager] = None,
    ):
        self.email_service = email_service or get_email_service()
        self.template_manager = template_manager or get_template_manager()
    
    async def _should_send_notification(
        self,
        user_id: int,
        notification_type: NotificationType,
        cooldown_minutes: int = 60,
    ) -> bool:
        """
        检查是否应该发送通知（防重复）
        
        Args:
            user_id: 用户ID
            notification_type: 通知类型
            cooldown_minutes: 冷却时间（分钟）
        
        Returns:
            是否应该发送
        """
        key = f"notification_sent:{user_id}:{notification_type.value}"
        last_sent = await redis_cache.get(key)
        
        if last_sent is not None:
            return False
        
        # 设置发送标记
        await redis_cache.set(key, datetime.utcnow().isoformat(), ttl=cooldown_minutes * 60)
        return True
    
    async def _get_user_email_preferences(self, user_id: int) -> Dict[str, bool]:
        """
        获取用户的邮件偏好设置
        
        Args:
            user_id: 用户ID
        
        Returns:
            邮件偏好设置字典
        """
        key = f"user_email_prefs:{user_id}"
        prefs = await redis_cache.get(key)
        
        if prefs:
            import json
            return json.loads(prefs)
        
        # 默认设置
        default_prefs = {
            "welcome": True,
            "verification": True,
            "password_reset": True,
            "learning_reminder": True,
            "achievement_unlocked": True,
            "learning_path_complete": True,
            "weekly_report": True,
            "new_follower": True,
            "challenge_invitation": True,
            "system_maintenance": True,
            "security_alert": True,
            "marketing": False,
        }
        
        return default_prefs
    
    async def _is_notification_enabled(
        self,
        user_id: int,
        notification_type: NotificationType,
    ) -> bool:
        """检查用户是否启用了某类通知"""
        prefs = await self._get_user_email_preferences(user_id)
        return prefs.get(notification_type.value, True)
    
    # ========== 用户相关通知 ==========
    
    async def send_welcome_email(
        self,
        user_email: str,
        username: str,
        verification_link: str,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送欢迎邮件
        
        Args:
            user_email: 用户邮箱
            username: 用户名
            verification_link: 验证链接
            language: 语言
        """
        try:
            template_vars = {
                "username": username,
                "verification_link": verification_link,
            }
            
            rendered = self.template_manager.render_template(
                "welcome",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send welcome email to {user_email}: {e}")
            return None
    
    async def send_verification_email(
        self,
        user_email: str,
        username: str,
        verification_code: str,
        expires_minutes: int = 30,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送邮箱验证邮件
        
        Args:
            user_email: 用户邮箱
            username: 用户名
            verification_code: 验证码
            expires_minutes: 过期时间（分钟）
            language: 语言
        """
        try:
            template_vars = {
                "username": username,
                "verification_code": verification_code,
                "expires_minutes": expires_minutes,
            }
            
            rendered = self.template_manager.render_template(
                "verification",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send verification email to {user_email}: {e}")
            return None
    
    async def send_password_reset_email(
        self,
        user_email: str,
        username: str,
        reset_link: str,
        expires_hours: int = 24,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送密码重置邮件
        
        Args:
            user_email: 用户邮箱
            username: 用户名
            reset_link: 重置链接
            expires_hours: 过期时间（小时）
            language: 语言
        """
        try:
            template_vars = {
                "username": username,
                "reset_link": reset_link,
                "expires_hours": expires_hours,
            }
            
            rendered = self.template_manager.render_template(
                "password_reset",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send password reset email to {user_email}: {e}")
            return None
    
    async def send_security_alert(
        self,
        user_email: str,
        username: str,
        login_time: datetime,
        login_location: str,
        device_info: str,
        secure_account_link: str,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送安全警报邮件
        
        Args:
            user_email: 用户邮箱
            username: 用户名
            login_time: 登录时间
            login_location: 登录地点
            device_info: 设备信息
            secure_account_link: 账户安全链接
            language: 语言
        """
        try:
            template_vars = {
                "username": username,
                "login_time": login_time.strftime("%Y-%m-%d %H:%M:%S"),
                "login_location": login_location,
                "device_info": device_info,
                "secure_account_link": secure_account_link,
            }
            
            rendered = self.template_manager.render_template(
                "security_alert",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send security alert to {user_email}: {e}")
            return None
    
    # ========== 学习相关通知 ==========
    
    async def send_learning_reminder(
        self,
        user_id: int,
        user_email: str,
        username: str,
        streak_days: int,
        recommended_concepts: List[str],
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送学习提醒邮件
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            streak_days: 连续学习天数
            recommended_concepts: 推荐概念列表
            language: 语言
        """
        # 检查用户是否启用了学习提醒
        if not await self._is_notification_enabled(user_id, NotificationType.LEARNING_REMINDER):
            return None
        
        # 检查冷却时间（每天最多一次）
        if not await self._should_send_notification(user_id, NotificationType.LEARNING_REMINDER, 1440):
            return None
        
        try:
            concepts_text = "\n".join([f"• {concept}" for concept in recommended_concepts[:5]])
            
            template_vars = {
                "username": username,
                "streak_days": streak_days,
                "recommended_concepts": concepts_text,
            }
            
            rendered = self.template_manager.render_template(
                "learning_reminder",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send learning reminder to {user_email}: {e}")
            return None
    
    async def send_achievement_unlocked(
        self,
        user_id: int,
        user_email: str,
        username: str,
        achievement_name: str,
        achievement_description: str,
        badge_icon: str = "🏆",
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送成就解锁通知
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            achievement_name: 成就名称
            achievement_description: 成就描述
            badge_icon: 徽章图标
            language: 语言
        """
        # 检查用户是否启用了成就通知
        if not await self._is_notification_enabled(user_id, NotificationType.ACHIEVEMENT_UNLOCKED):
            return None
        
        try:
            template_vars = {
                "username": username,
                "achievement_name": achievement_name,
                "achievement_description": achievement_description,
                "badge_icon": badge_icon,
            }
            
            rendered = self.template_manager.render_template(
                "achievement_unlocked",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send achievement notification to {user_email}: {e}")
            return None
    
    async def send_learning_path_complete(
        self,
        user_id: int,
        user_email: str,
        username: str,
        path_name: str,
        completed_nodes: int,
        total_nodes: int,
        certificate_link: str,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送学习路径完成通知
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            path_name: 路径名称
            completed_nodes: 完成节点数
            total_nodes: 总节点数
            certificate_link: 证书链接
            language: 语言
        """
        # 检查用户是否启用了完成通知
        if not await self._is_notification_enabled(user_id, NotificationType.LEARNING_PATH_COMPLETE):
            return None
        
        try:
            template_vars = {
                "username": username,
                "path_name": path_name,
                "completed_nodes": completed_nodes,
                "total_nodes": total_nodes,
                "certificate_link": certificate_link,
            }
            
            rendered = self.template_manager.render_template(
                "learning_path_complete",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send completion notification to {user_email}: {e}")
            return None
    
    async def send_weekly_report(
        self,
        user_id: int,
        user_email: str,
        username: str,
        week_start: datetime,
        week_end: datetime,
        study_hours: float,
        concepts_learned: int,
        quizzes_completed: int,
        accuracy_rate: float,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送每周学习报告
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            week_start: 周开始时间
            week_end: 周结束时间
            study_hours: 学习小时数
            concepts_learned: 学习的概念数
            quizzes_completed: 完成的测验数
            accuracy_rate: 正确率
            language: 语言
        """
        # 检查用户是否启用了周报
        if not await self._is_notification_enabled(user_id, NotificationType.WEEKLY_REPORT):
            return None
        
        # 检查冷却时间（每周最多一次）
        if not await self._should_send_notification(user_id, NotificationType.WEEKLY_REPORT, 10080):
            return None
        
        try:
            template_vars = {
                "username": username,
                "week_start": week_start.strftime("%Y-%m-%d"),
                "week_end": week_end.strftime("%Y-%m-%d"),
                "study_hours": f"{study_hours:.1f}",
                "concepts_learned": concepts_learned,
                "quizzes_completed": quizzes_completed,
                "accuracy_rate": f"{accuracy_rate:.1%}",
            }
            
            rendered = self.template_manager.render_template(
                "weekly_report",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send weekly report to {user_email}: {e}")
            return None
    
    # ========== 社交相关通知 ==========
    
    async def send_new_follower_notification(
        self,
        user_id: int,
        user_email: str,
        username: str,
        follower_name: str,
        follower_profile_link: str,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送新关注者通知
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            follower_name: 关注者名称
            follower_profile_link: 关注者资料链接
            language: 语言
        """
        # 检查用户是否启用了关注通知
        if not await self._is_notification_enabled(user_id, NotificationType.NEW_FOLLOWER):
            return None
        
        # 检查冷却时间（每小时最多一次）
        if not await self._should_send_notification(user_id, NotificationType.NEW_FOLLOWER, 60):
            return None
        
        try:
            template_vars = {
                "username": username,
                "follower_name": follower_name,
                "follower_profile_link": follower_profile_link,
            }
            
            rendered = self.template_manager.render_template(
                "new_follower",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send follower notification to {user_email}: {e}")
            return None
    
    async def send_challenge_invitation(
        self,
        user_id: int,
        user_email: str,
        username: str,
        challenger_name: str,
        challenge_name: str,
        challenge_description: str,
        accept_link: str,
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送挑战邀请
        
        Args:
            user_id: 用户ID
            user_email: 用户邮箱
            username: 用户名
            challenger_name: 挑战者名称
            challenge_name: 挑战名称
            challenge_description: 挑战描述
            accept_link: 接受链接
            language: 语言
        """
        # 检查用户是否启用了挑战邀请
        if not await self._is_notification_enabled(user_id, NotificationType.CHALLENGE_INVITATION):
            return None
        
        try:
            template_vars = {
                "username": username,
                "challenger_name": challenger_name,
                "challenge_name": challenge_name,
                "challenge_description": challenge_description,
                "accept_link": accept_link,
            }
            
            rendered = self.template_manager.render_template(
                "challenge_invitation",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send challenge invitation to {user_email}: {e}")
            return None
    
    # ========== 系统通知 ==========
    
    async def send_system_maintenance_notice(
        self,
        user_email: str,
        maintenance_time: datetime,
        expected_duration: int,
        affected_services: List[str],
        language: str = None,
    ) -> Optional[Dict[str, Any]]:
        """
        发送系统维护通知
        
        Args:
            user_email: 用户邮箱
            maintenance_time: 维护时间
            expected_duration: 预计持续时间（分钟）
            affected_services: 受影响的服务列表
            language: 语言
        """
        try:
            services_text = "\n".join([f"• {service}" for service in affected_services])
            
            template_vars = {
                "maintenance_time": maintenance_time.strftime("%Y-%m-%d %H:%M"),
                "expected_duration": expected_duration,
                "affected_services": services_text,
            }
            
            rendered = self.template_manager.render_template(
                "system_maintenance",
                template_vars,
                language,
            )
            
            result = await self.email_service.send_email(
                to_addresses=user_email,
                subject=rendered["subject"],
                html_content=rendered["html"],
                text_content=rendered["text"],
            )
            
            return result
            
        except Exception as e:
            print(f"Failed to send maintenance notice to {user_email}: {e}")
            return None
    
    # ========== 批量通知 ==========
    
    async def send_bulk_notification(
        self,
        recipients: List[Dict[str, Any]],
        notification_type: NotificationType,
        template_vars_func,
        language: str = None,
    ) -> Dict[str, int]:
        """
        发送批量通知
        
        Args:
            recipients: 收件人列表，每项包含 user_email 等必要信息
            notification_type: 通知类型
            template_vars_func: 生成模板变量的函数
            language: 语言
        
        Returns:
            发送统计
        """
        stats = {"sent": 0, "failed": 0}
        
        for recipient in recipients:
            try:
                user_id = recipient.get("user_id")
                user_email = recipient.get("user_email")
                
                # 检查用户偏好
                if user_id and not await self._is_notification_enabled(user_id, notification_type):
                    continue
                
                # 生成模板变量
                template_vars = template_vars_func(recipient)
                
                # 渲染模板
                rendered = self.template_manager.render_template(
                    notification_type.value,
                    template_vars,
                    language,
                )
                
                # 发送邮件
                await self.email_service.send_email(
                    to_addresses=user_email,
                    subject=rendered["subject"],
                    html_content=rendered["html"],
                    text_content=rendered["text"],
                )
                
                stats["sent"] += 1
                
            except Exception as e:
                print(f"Failed to send bulk notification: {e}")
                stats["failed"] += 1
        
        return stats


@lru_cache()
def get_notification_trigger() -> NotificationTrigger:
    """获取通知触发器实例"""
    return NotificationTrigger()
