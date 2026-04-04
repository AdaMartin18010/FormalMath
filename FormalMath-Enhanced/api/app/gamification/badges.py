"""
徽章系统
多层级徽章、徽章收集、展示系统
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
from collections import defaultdict


class BadgeTier(str, Enum):
    """徽章等级"""
    BRONZE = "bronze"
    SILVER = "silver"
    GOLD = "gold"
    PLATINUM = "platinum"
    DIAMOND = "diamond"
    SPECIAL = "special"


class BadgeCategory(str, Enum):
    """徽章类别"""
    LEARNING = "learning"
    MASTERY = "mastery"
    SOCIAL = "social"
    STREAK = "streak"
    SPECIAL = "special"
    SEASONAL = "seasonal"


@dataclass
class Badge:
    """徽章定义"""
    badge_id: str
    name: str
    description: str
    tier: BadgeTier
    category: BadgeCategory
    
    # 解锁条件
    condition_type: str
    condition_value: float
    condition_params: Dict[str, Any] = field(default_factory=dict)
    
    # 视觉
    icon_url: Optional[str] = None
    animation_url: Optional[str] = None
    
    # 元数据
    points: int = 0
    is_limited: bool = False
    available_until: Optional[datetime] = None
    
    # 系列归属
    series_id: Optional[str] = None
    series_order: int = 0


@dataclass
class UserBadge:
    """用户徽章记录"""
    user_id: str
    badge: Badge
    unlocked_at: datetime
    progress_at_unlock: float
    is_new: bool = True
    showcased: bool = False


@dataclass
class BadgeSeries:
    """徽章系列"""
    series_id: str
    name: str
    description: str
    badges: List[str] = field(default_factory=list)  # badge_id列表
    reward_for_completion: Optional[Dict] = None


class BadgeSystem:
    """
    徽章系统
    
    管理徽章定义、解锁和用户收藏
    """
    
    # 等级积分
    TIER_POINTS = {
        BadgeTier.BRONZE: 10,
        BadgeTier.SILVER: 25,
        BadgeTier.GOLD: 50,
        BadgeTier.PLATINUM: 100,
        BadgeTier.DIAMOND: 200,
        BadgeTier.SPECIAL: 150
    }
    
    def __init__(self):
        self.badges: Dict[str, Badge] = {}
        self.series: Dict[str, BadgeSeries] = {}
        
        # 用户数据
        self.user_badges: Dict[str, List[UserBadge]] = defaultdict(list)
        self.user_progress: Dict[str, Dict[str, float]] = defaultdict(lambda: defaultdict(float))
        self.showcased_badges: Dict[str, List[str]] = defaultdict(list)
        
        # 初始化默认徽章
        self._init_default_badges()
    
    def _init_default_badges(self):
        """初始化默认徽章"""
        default_badges = [
            # 学习系列 - 铜
            Badge(
                badge_id='first_step',
                name='第一步',
                description='完成首次学习',
                tier=BadgeTier.BRONZE,
                category=BadgeCategory.LEARNING,
                condition_type='count',
                condition_value=1,
                condition_params={'target': 'sessions_completed'},
                points=self.TIER_POINTS[BadgeTier.BRONZE],
                series_id='learning_journey',
                series_order=1
            ),
            Badge(
                badge_id='steady_learner',
                name='稳定学习者',
                description='完成10次学习',
                tier=BadgeTier.BRONZE,
                category=BadgeCategory.LEARNING,
                condition_type='count',
                condition_value=10,
                condition_params={'target': 'sessions_completed'},
                points=self.TIER_POINTS[BadgeTier.BRONZE],
                series_id='learning_journey',
                series_order=2
            ),
            
            # 学习系列 - 银
            Badge(
                badge_id='dedicated_student',
                name='专注学生',
                description='完成50次学习',
                tier=BadgeTier.SILVER,
                category=BadgeCategory.LEARNING,
                condition_type='count',
                condition_value=50,
                condition_params={'target': 'sessions_completed'},
                points=self.TIER_POINTS[BadgeTier.SILVER],
                series_id='learning_journey',
                series_order=3
            ),
            
            # 学习系列 - 金
            Badge(
                badge_id='learning_master',
                name='学习大师',
                description='完成100次学习',
                tier=BadgeTier.GOLD,
                category=BadgeCategory.LEARNING,
                condition_type='count',
                condition_value=100,
                condition_params={'target': 'sessions_completed'},
                points=self.TIER_POINTS[BadgeTier.GOLD],
                series_id='learning_journey',
                series_order=4
            ),
            
            # 掌握系列
            Badge(
                badge_id='concept_collector_bronze',
                name='概念收集者',
                description='掌握5个概念',
                tier=BadgeTier.BRONZE,
                category=BadgeCategory.MASTERY,
                condition_type='count',
                condition_value=5,
                condition_params={'target': 'concepts_mastered'},
                points=self.TIER_POINTS[BadgeTier.BRONZE],
                series_id='mastery_path',
                series_order=1
            ),
            Badge(
                badge_id='concept_collector_silver',
                name='概念探索者',
                description='掌握25个概念',
                tier=BadgeTier.SILVER,
                category=BadgeCategory.MASTERY,
                condition_type='count',
                condition_value=25,
                condition_params={'target': 'concepts_mastered'},
                points=self.TIER_POINTS[BadgeTier.SILVER],
                series_id='mastery_path',
                series_order=2
            ),
            Badge(
                badge_id='concept_collector_gold',
                name='概念大师',
                description='掌握100个概念',
                tier=BadgeTier.GOLD,
                category=BadgeCategory.MASTERY,
                condition_type='count',
                condition_value=100,
                condition_params={'target': 'concepts_mastered'},
                points=self.TIER_POINTS[BadgeTier.GOLD],
                series_id='mastery_path',
                series_order=3
            ),
            Badge(
                badge_id='concept_collector_platinum',
                name='概念传奇',
                description='掌握500个概念',
                tier=BadgeTier.PLATINUM,
                category=BadgeCategory.MASTERY,
                condition_type='count',
                condition_value=500,
                condition_params={'target': 'concepts_mastered'},
                points=self.TIER_POINTS[BadgeTier.PLATINUM],
                series_id='mastery_path',
                series_order=4
            ),
            
            # 连续学习系列
            Badge(
                badge_id='streak_3',
                name='连续3天',
                description='连续学习3天',
                tier=BadgeTier.BRONZE,
                category=BadgeCategory.STREAK,
                condition_type='streak',
                condition_value=3,
                condition_params={'target': 'daily_streak'},
                points=self.TIER_POINTS[BadgeTier.BRONZE],
                series_id='streak_master',
                series_order=1
            ),
            Badge(
                badge_id='streak_7',
                name='一周坚持',
                description='连续学习7天',
                tier=BadgeTier.SILVER,
                category=BadgeCategory.STREAK,
                condition_type='streak',
                condition_value=7,
                condition_params={'target': 'daily_streak'},
                points=self.TIER_POINTS[BadgeTier.SILVER],
                series_id='streak_master',
                series_order=2
            ),
            Badge(
                badge_id='streak_30',
                name='月度冠军',
                description='连续学习30天',
                tier=BadgeTier.GOLD,
                category=BadgeCategory.STREAK,
                condition_type='streak',
                condition_value=30,
                condition_params={'target': 'daily_streak'},
                points=self.TIER_POINTS[BadgeTier.GOLD],
                series_id='streak_master',
                series_order=3
            ),
            Badge(
                badge_id='streak_100',
                name='百日毅力',
                description='连续学习100天',
                tier=BadgeTier.DIAMOND,
                category=BadgeCategory.STREAK,
                condition_type='streak',
                condition_value=100,
                condition_params={'target': 'daily_streak'},
                points=self.TIER_POINTS[BadgeTier.DIAMOND],
                series_id='streak_master',
                series_order=4
            ),
            
            # 社交系列
            Badge(
                badge_id='social_butterfly',
                name='社交蝴蝶',
                description='加入5个学习小组',
                tier=BadgeTier.SILVER,
                category=BadgeCategory.SOCIAL,
                condition_type='count',
                condition_value=5,
                condition_params={'target': 'groups_joined'},
                points=self.TIER_POINTS[BadgeTier.SILVER],
                series_id='social_network',
                series_order=1
            ),
            Badge(
                badge_id='helpful_hand',
                name='乐于助人',
                description='帮助其他学习者25次',
                tier=BadgeTier.GOLD,
                category=BadgeCategory.SOCIAL,
                condition_type='count',
                condition_value=25,
                condition_params={'target': 'help_given'},
                points=self.TIER_POINTS[BadgeTier.GOLD],
                series_id='social_network',
                series_order=2
            ),
            
            # 特殊徽章
            Badge(
                badge_id='perfect_score',
                name='完美得分',
                description='在一次练习中获得满分',
                tier=BadgeTier.SPECIAL,
                category=BadgeCategory.SPECIAL,
                condition_type='score',
                condition_value=100,
                condition_params={'target': 'exercise_score', 'exact': True},
                points=self.TIER_POINTS[BadgeTier.SPECIAL]
            ),
            Badge(
                badge_id='early_bird',
                name='早鸟',
                description='连续7天在早上8点前开始学习',
                tier=BadgeTier.SPECIAL,
                category=BadgeCategory.SPECIAL,
                condition_type='streak_condition',
                condition_value=7,
                condition_params={'target': 'early_study', 'before_hour': 8},
                points=self.TIER_POINTS[BadgeTier.SPECIAL]
            ),
            Badge(
                badge_id='night_owl',
                name='夜猫子',
                description='连续7天在晚上10点后学习',
                tier=BadgeTier.SPECIAL,
                category=BadgeCategory.SPECIAL,
                condition_type='streak_condition',
                condition_value=7,
                condition_params={'target': 'night_study', 'after_hour': 22},
                points=self.TIER_POINTS[BadgeTier.SPECIAL]
            ),
        ]
        
        for badge in default_badges:
            self.add_badge(badge)
        
        # 创建系列
        self._init_badge_series()
    
    def _init_badge_series(self):
        """初始化徽章系列"""
        series_definitions = [
            BadgeSeries(
                series_id='learning_journey',
                name='学习之旅',
                description='持续学习的见证',
                badges=['first_step', 'steady_learner', 'dedicated_student', 'learning_master'],
                reward_for_completion={
                    'title': '终身学习者',
                    'bonus_points': 500
                }
            ),
            BadgeSeries(
                series_id='mastery_path',
                name='掌握之路',
                description='知识掌握的里程碑',
                badges=['concept_collector_bronze', 'concept_collector_silver', 
                       'concept_collector_gold', 'concept_collector_platinum'],
                reward_for_completion={
                    'title': '知识守护者',
                    'bonus_points': 1000
                }
            ),
            BadgeSeries(
                series_id='streak_master',
                name='坚持大师',
                description='毅力的证明',
                badges=['streak_3', 'streak_7', 'streak_30', 'streak_100'],
                reward_for_completion={
                    'title': '毅力传奇',
                    'bonus_points': 2000
                }
            ),
            BadgeSeries(
                series_id='social_network',
                name='社交网络',
                description='学习社区的贡献者',
                badges=['social_butterfly', 'helpful_hand'],
                reward_for_completion={
                    'title': '社区之星',
                    'bonus_points': 300
                }
            ),
        ]
        
        for s in series_definitions:
            self.series[s.series_id] = s
    
    def add_badge(self, badge: Badge):
        """添加徽章"""
        self.badges[badge.badge_id] = badge
    
    def update_progress(
        self,
        user_id: str,
        target: str,
        value: float,
        is_increment: bool = True,
        context: Optional[Dict] = None
    ) -> List[Badge]:
        """
        更新用户进度
        
        Args:
            user_id: 用户ID
            target: 目标类型
            value: 值
            is_increment: 是否为增量
            context: 额外上下文
        
        Returns:
            新解锁的徽章列表
        """
        if is_increment:
            self.user_progress[user_id][target] += value
        else:
            self.user_progress[user_id][target] = value
        
        # 保存上下文特定进度
        if context:
            for key, val in context.items():
                self.user_progress[user_id][f'{target}_{key}'] = val
        
        return self._check_badges(user_id)
    
    def _check_badges(self, user_id: str) -> List[Badge]:
        """检查可解锁的徽章"""
        unlocked = []
        
        # 获取已解锁的徽章ID
        unlocked_ids = {
            ub.badge.badge_id
            for ub in self.user_badges[user_id]
        }
        
        now = datetime.utcnow()
        
        for badge_id, badge in self.badges.items():
            if badge_id in unlocked_ids:
                continue
            
            # 检查限时徽章
            if badge.is_limited and badge.available_until:
                if now > badge.available_until:
                    continue
            
            # 检查条件
            if self._check_badge_condition(user_id, badge):
                # 解锁徽章
                user_badge = UserBadge(
                    user_id=user_id,
                    badge=badge,
                    unlocked_at=now,
                    progress_at_unlock=self.user_progress[user_id].get(
                        badge.condition_params.get('target', ''), 0
                    ),
                    is_new=True
                )
                self.user_badges[user_id].append(user_badge)
                unlocked.append(badge)
        
        return unlocked
    
    def _check_badge_condition(self, user_id: str, badge: Badge) -> bool:
        """检查特定徽章条件"""
        target = badge.condition_params.get('target', '')
        current_value = self.user_progress[user_id].get(target, 0)
        
        if badge.condition_type == 'count':
            return current_value >= badge.condition_value
        
        elif badge.condition_type == 'streak':
            return current_value >= badge.condition_value
        
        elif badge.condition_type == 'score':
            if badge.condition_params.get('exact'):
                return current_value == badge.condition_value
            return current_value >= badge.condition_value
        
        elif badge.condition_type == 'streak_condition':
            # 特殊条件连续
            return current_value >= badge.condition_value
        
        return False
    
    def get_user_badges(self, user_id: str) -> Dict[str, Any]:
        """获取用户徽章"""
        user_badges = self.user_badges[user_id]
        
        # 按等级分类
        by_tier = defaultdict(list)
        by_category = defaultdict(list)
        total_points = 0
        
        for ub in user_badges:
            badge_info = {
                'badge_id': ub.badge.badge_id,
                'name': ub.badge.name,
                'description': ub.badge.description,
                'tier': ub.badge.tier.value,
                'category': ub.badge.category.value,
                'points': ub.badge.points,
                'unlocked_at': ub.unlocked_at.isoformat(),
                'is_new': ub.is_new,
                'series_id': ub.badge.series_id
            }
            
            by_tier[ub.badge.tier.value].append(badge_info)
            by_category[ub.badge.category.value].append(badge_info)
            total_points += ub.badge.points
        
        # 检查系列完成
        completed_series = []
        for series_id, series in self.series.items():
            series_badges = set(series.badges)
            user_badge_ids = {ub.badge.badge_id for ub in user_badges}
            
            if series_badges <= user_badge_ids:
                completed_series.append({
                    'series_id': series_id,
                    'name': series.name,
                    'reward': series.reward_for_completion
                })
        
        # 标记为已查看
        for ub in user_badges:
            ub.is_new = False
        
        return {
            'user_id': user_id,
            'total_badges': len(user_badges),
            'total_points': total_points,
            'by_tier': dict(by_tier),
            'by_category': dict(by_category),
            'completed_series': completed_series,
            'showcased': self.showcased_badges[user_id]
        }
    
    def get_badge_progress(self, user_id: str, badge_id: str) -> Optional[Dict]:
        """获取特定徽章进度"""
        if badge_id not in self.badges:
            return None
        
        badge = self.badges[badge_id]
        target = badge.condition_params.get('target', '')
        current = self.user_progress[user_id].get(target, 0)
        
        is_unlocked = any(
            ub.badge.badge_id == badge_id
            for ub in self.user_badges[user_id]
        )
        
        return {
            'badge_id': badge_id,
            'name': badge.name,
            'description': badge.description,
            'tier': badge.tier.value,
            'is_unlocked': is_unlocked,
            'current_progress': current,
            'target': badge.condition_value,
            'progress_percentage': min(100, int(100 * current / badge.condition_value)) if badge.condition_value > 0 else 0
        }
    
    def showcase_badge(self, user_id: str, badge_id: str) -> bool:
        """
        展示徽章
        
        用户可以选择徽章在个人资料中展示
        """
        # 检查是否拥有该徽章
        has_badge = any(
            ub.badge.badge_id == badge_id
            for ub in self.user_badges[user_id]
        )
        
        if not has_badge:
            return False
        
        # 限制展示数量
        if len(self.showcased_badges[user_id]) >= 6:
            # 移除最早展示的
            self.showcased_badges[user_id].pop(0)
        
        if badge_id not in self.showcased_badges[user_id]:
            self.showcased_badges[user_id].append(badge_id)
        
        return True
    
    def get_next_badges(self, user_id: str, limit: int = 5) -> List[Dict]:
        """获取即将解锁的徽章"""
        in_progress = []
        
        unlocked_ids = {
            ub.badge.badge_id
            for ub in self.user_badges[user_id]
        }
        
        for badge_id, badge in self.badges.items():
            if badge_id in unlocked_ids:
                continue
            
            target = badge.condition_params.get('target', '')
            current = self.user_progress[user_id].get(target, 0)
            
            if current > 0:
                progress = current / badge.condition_value if badge.condition_value > 0 else 0
                in_progress.append({
                    'badge_id': badge_id,
                    'name': badge.name,
                    'tier': badge.tier.value,
                    'progress': progress,
                    'current': current,
                    'target': badge.condition_value,
                    'points': badge.points
                })
        
        # 按进度排序
        in_progress.sort(key=lambda x: x['progress'], reverse=True)
        
        return in_progress[:limit]
    
    def get_rarity_stats(self, user_id: str) -> Dict[str, Any]:
        """获取稀有度统计"""
        user_badges = self.user_badges[user_id]
        
        tier_counts = defaultdict(int)
        for ub in user_badges:
            tier_counts[ub.badge.tier.value] += 1
        
        total_possible = len(self.badges)
        collected = len(user_badges)
        
        return {
            'total_collected': collected,
            'total_possible': total_possible,
            'completion_percentage': int(100 * collected / total_possible) if total_possible > 0 else 0,
            'by_tier': dict(tier_counts),
            'rarest_badge': self._get_rarest_badge(user_id)
        }
    
    def _get_rarest_badge(self, user_id: str) -> Optional[Dict]:
        """获取用户最稀有的徽章"""
        user_badges = self.user_badges[user_id]
        
        if not user_badges:
            return None
        
        # 按等级排序
        tier_order = [BadgeTier.DIAMOND, BadgeTier.PLATINUM, BadgeTier.GOLD,
                     BadgeTier.SILVER, BadgeTier.BRONZE, BadgeTier.SPECIAL]
        
        for tier in tier_order:
            badges_of_tier = [ub for ub in user_badges if ub.badge.tier == tier]
            if badges_of_tier:
                # 返回最近解锁的
                latest = max(badges_of_tier, key=lambda x: x.unlocked_at)
                return {
                    'badge_id': latest.badge.badge_id,
                    'name': latest.badge.name,
                    'tier': tier.value,
                    'unlocked_at': latest.unlocked_at.isoformat()
                }
        
        return None
