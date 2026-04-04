"""
竞赛系统与激励机制
挑战、排行榜、奖励
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from collections import defaultdict
import json


class CompetitionType(str, Enum):
    """竞赛类型"""
    INDIVIDUAL = "individual"      # 个人赛
    TEAM = "team"                  # 团队赛
    TIMED = "timed"                # 限时赛
    MARATHON = "marathon"          # 马拉松
    DAILY = "daily"                # 每日挑战
    WEEKLY = "weekly"              # 每周挑战


class AchievementCategory(str, Enum):
    """成就类别"""
    MASTERY = "mastery"            # 掌握成就
    CONSISTENCY = "consistency"    # 坚持成就
    SOCIAL = "social"              # 社交成就
    CHALLENGE = "challenge"        # 挑战成就
    EXPLORATION = "exploration"    # 探索成就
    CONTRIBUTION = "contribution"  # 贡献成就


@dataclass
class Achievement:
    """成就"""
    achievement_id: str
    name: str
    description: str
    category: AchievementCategory
    
    # 条件
    condition_type: str  # count, streak, score, unique
    condition_value: float
    condition_target: Optional[str] = None
    
    # 奖励
    points: int = 0
    badge_url: Optional[str] = None
    
    # 元数据
    rarity: str = 'common'  # common, rare, epic, legendary
    created_at: datetime = field(default_factory=datetime.utcnow)


@dataclass
class UserAchievement:
    """用户成就记录"""
    user_id: str
    achievement: Achievement
    unlocked_at: datetime
    progress_at_unlock: float


@dataclass
class Competition:
    """竞赛"""
    competition_id: str
    name: str
    description: str
    competition_type: CompetitionType
    
    # 时间
    start_time: datetime
    end_time: datetime
    
    # 参与
    participants: List[str] = field(default_factory=list)
    max_participants: Optional[int] = None
    
    # 规则
    rules: Dict[str, Any] = field(default_factory=dict)
    scoring_criteria: Dict[str, float] = field(default_factory=dict)
    
    # 奖励
    rewards: Dict[str, Any] = field(default_factory=dict)
    
    # 状态
    status: str = 'upcoming'  # upcoming, active, completed
    
    def is_active(self) -> bool:
        now = datetime.utcnow()
        return self.start_time <= now < self.end_time
    
    def is_completed(self) -> bool:
        return datetime.utcnow() >= self.end_time


@dataclass
class LeaderboardEntry:
    """排行榜条目"""
    rank: int
    user_id: str
    score: float
    metrics: Dict[str, float] = field(default_factory=dict)
    trend: int = 0  # 排名变化


class AchievementSystem:
    """
    成就系统
    
    管理成就定义、解锁和用户进度
    """
    
    def __init__(self):
        self.achievements: Dict[str, Achievement] = {}
        self.user_achievements: Dict[str, List[UserAchievement]] = defaultdict(list)
        self.user_progress: Dict[str, Dict[str, float]] = defaultdict(lambda: defaultdict(float))
        
        # 初始化默认成就
        self._init_default_achievements()
    
    def _init_default_achievements(self):
        """初始化默认成就"""
        default_achievements = [
            # 掌握成就
            Achievement(
                achievement_id='first_concept',
                name='初识数学',
                description='掌握第一个概念',
                category=AchievementCategory.MASTERY,
                condition_type='count',
                condition_value=1,
                condition_target='concepts_mastered',
                points=10,
                rarity='common'
            ),
            Achievement(
                achievement_id='concept_collector',
                name='概念收藏家',
                description='掌握10个概念',
                category=AchievementCategory.MASTERY,
                condition_type='count',
                condition_value=10,
                condition_target='concepts_mastered',
                points=50,
                rarity='rare'
            ),
            Achievement(
                achievement_id='master_scholar',
                name='学术大师',
                description='掌握50个概念',
                category=AchievementCategory.MASTERY,
                condition_type='count',
                condition_value=50,
                condition_target='concepts_mastered',
                points=200,
                rarity='epic'
            ),
            
            # 坚持成就
            Achievement(
                achievement_id='first_day',
                name='启程',
                description='完成第一天的学习',
                category=AchievementCategory.CONSISTENCY,
                condition_type='count',
                condition_value=1,
                condition_target='learning_days',
                points=5,
                rarity='common'
            ),
            Achievement(
                achievement_id='week_warrior',
                name='周战士',
                description='连续学习7天',
                category=AchievementCategory.CONSISTENCY,
                condition_type='streak',
                condition_value=7,
                condition_target='daily_learning',
                points=30,
                rarity='rare'
            ),
            Achievement(
                achievement_id='month_master',
                name='月度达人',
                description='连续学习30天',
                category=AchievementCategory.CONSISTENCY,
                condition_type='streak',
                condition_value=30,
                condition_target='daily_learning',
                points=100,
                rarity='epic'
            ),
            
            # 挑战成就
            Achievement(
                achievement_id='perfect_score',
                name='满分',
                description='在一次练习中获得满分',
                category=AchievementCategory.CHALLENGE,
                condition_type='score',
                condition_value=100,
                condition_target='exercise_score',
                points=20,
                rarity='rare'
            ),
            Achievement(
                achievement_id='speed_demon',
                name='速度之王',
                description='在限时挑战中提前50%完成',
                category=AchievementCategory.CHALLENGE,
                condition_type='score',
                condition_value=150,  # 时间效率得分
                condition_target='time_efficiency',
                points=30,
                rarity='rare'
            ),
            
            # 社交成就
            Achievement(
                achievement_id='team_player',
                name='团队合作',
                description='加入第一个学习小组',
                category=AchievementCategory.SOCIAL,
                condition_type='count',
                condition_value=1,
                condition_target='groups_joined',
                points=10,
                rarity='common'
            ),
            Achievement(
                achievement_id='helpful_peer',
                name='热心助人',
                description='帮助其他学习者10次',
                category=AchievementCategory.SOCIAL,
                condition_type='count',
                condition_value=10,
                condition_target='help_given',
                points=30,
                rarity='rare'
            ),
            
            # 探索成就
            Achievement(
                achievement_id='branch_explorer',
                name='分支探索者',
                description='探索3个不同的数学分支',
                category=AchievementCategory.EXPLORATION,
                condition_type='unique',
                condition_value=3,
                condition_target='branches_explored',
                points=40,
                rarity='rare'
            ),
            Achievement(
                achievement_id='deep_diver',
                name='深度潜水员',
                description='完成一个分支的高级内容',
                category=AchievementCategory.EXPLORATION,
                condition_type='count',
                condition_value=1,
                condition_target='advanced_branch_completed',
                points=60,
                rarity='epic'
            ),
        ]
        
        for achievement in default_achievements:
            self.achievements[achievement.achievement_id] = achievement
    
    def add_achievement(self, achievement: Achievement):
        """添加成就"""
        self.achievements[achievement.achievement_id] = achievement
    
    def update_progress(
        self,
        user_id: str,
        target: str,
        value: float,
        is_increment: bool = True
    ) -> List[Achievement]:
        """
        更新用户进度
        
        Args:
            user_id: 用户ID
            target: 目标类型
            value: 值
            is_increment: 是否为增量
        
        Returns:
            新解锁的成就列表
        """
        if is_increment:
            self.user_progress[user_id][target] += value
        else:
            self.user_progress[user_id][target] = value
        
        # 检查成就解锁
        return self._check_achievements(user_id)
    
    def _check_achievements(self, user_id: str) -> List[Achievement]:
        """检查可解锁的成就"""
        unlocked = []
        
        # 获取已解锁的成就ID
        unlocked_ids = {
            ua.achievement.achievement_id
            for ua in self.user_achievements[user_id]
        }
        
        for achievement_id, achievement in self.achievements.items():
            if achievement_id in unlocked_ids:
                continue
            
            # 检查条件
            if self._check_achievement_condition(user_id, achievement):
                # 解锁成就
                user_achievement = UserAchievement(
                    user_id=user_id,
                    achievement=achievement,
                    unlocked_at=datetime.utcnow(),
                    progress_at_unlock=self.user_progress[user_id].get(
                        achievement.condition_target, 0
                    )
                )
                self.user_achievements[user_id].append(user_achievement)
                unlocked.append(achievement)
        
        return unlocked
    
    def _check_achievement_condition(
        self,
        user_id: str,
        achievement: Achievement
    ) -> bool:
        """检查特定成就是否满足条件"""
        current_value = self.user_progress[user_id].get(
            achievement.condition_target, 0
        )
        
        return current_value >= achievement.condition_value
    
    def get_user_achievements(self, user_id: str) -> Dict[str, Any]:
        """获取用户成就"""
        unlocked = self.user_achievements[user_id]
        
        # 计算统计
        by_category = defaultdict(list)
        total_points = 0
        
        for ua in unlocked:
            by_category[ua.achievement.category.value].append({
                'achievement_id': ua.achievement.achievement_id,
                'name': ua.achievement.name,
                'description': ua.achievement.description,
                'rarity': ua.achievement.rarity,
                'points': ua.achievement.points,
                'unlocked_at': ua.unlocked_at.isoformat()
            })
            total_points += ua.achievement.points
        
        # 计算进度中的成就
        in_progress = []
        unlocked_ids = {ua.achievement.achievement_id for ua in unlocked}
        
        for achievement_id, achievement in self.achievements.items():
            if achievement_id in unlocked_ids:
                continue
            
            current = self.user_progress[user_id].get(
                achievement.condition_target, 0
            )
            progress = min(1.0, current / achievement.condition_value)
            
            if progress > 0:
                in_progress.append({
                    'achievement_id': achievement_id,
                    'name': achievement.name,
                    'progress': progress,
                    'current': current,
                    'target': achievement.condition_value
                })
        
        # 排序
        in_progress.sort(key=lambda x: x['progress'], reverse=True)
        
        return {
            'user_id': user_id,
            'total_points': total_points,
            'total_unlocked': len(unlocked),
            'total_available': len(self.achievements),
            'by_category': dict(by_category),
            'recent_unlocks': [
                {
                    'name': ua.achievement.name,
                    'unlocked_at': ua.unlocked_at.isoformat()
                }
                for ua in sorted(unlocked, key=lambda x: x.unlocked_at, reverse=True)[:5]
            ],
            'in_progress': in_progress[:5],
            'next_achievements': in_progress[:3]
        }
    
    def get_achievement_progress(
        self,
        user_id: str,
        achievement_id: str
    ) -> Optional[Dict]:
        """获取特定成就进度"""
        if achievement_id not in self.achievements:
            return None
        
        achievement = self.achievements[achievement_id]
        current = self.user_progress[user_id].get(
            achievement.condition_target, 0
        )
        
        # 检查是否已解锁
        is_unlocked = any(
            ua.achievement.achievement_id == achievement_id
            for ua in self.user_achievements[user_id]
        )
        
        return {
            'achievement_id': achievement_id,
            'name': achievement.name,
            'description': achievement.description,
            'category': achievement.category.value,
            'rarity': achievement.rarity,
            'points': achievement.points,
            'is_unlocked': is_unlocked,
            'current_progress': current,
            'target': achievement.condition_value,
            'progress_percentage': min(100, int(100 * current / achievement.condition_value))
        }


class CompetitionManager:
    """
    竞赛管理器
    
    管理竞赛创建、参与、计分和排行榜
    """
    
    def __init__(self):
        self.competitions: Dict[str, Competition] = {}
        self.scores: Dict[str, Dict[str, float]] = defaultdict(dict)
        self.user_competition_history: Dict[str, List[str]] = defaultdict(list)
    
    def create_competition(
        self,
        name: str,
        description: str,
        competition_type: CompetitionType,
        duration_hours: int,
        rules: Optional[Dict] = None,
        rewards: Optional[Dict] = None
    ) -> Competition:
        """
        创建竞赛
        
        Args:
            name: 名称
            description: 描述
            competition_type: 类型
            duration_hours: 持续时间（小时）
            rules: 规则
            rewards: 奖励
        
        Returns:
            创建的竞赛
        """
        competition_id = f"comp_{int(datetime.utcnow().timestamp())}_{random.randint(1000, 9999)}"
        
        now = datetime.utcnow()
        competition = Competition(
            competition_id=competition_id,
            name=name,
            description=description,
            competition_type=competition_type,
            start_time=now,
            end_time=now + timedelta(hours=duration_hours),
            rules=rules or {},
            rewards=rewards or {},
            status='active'
        )
        
        self.competitions[competition_id] = competition
        return competition
    
    def join_competition(
        self,
        competition_id: str,
        user_id: str
    ) -> Dict[str, Any]:
        """参加竞赛"""
        if competition_id not in self.competitions:
            return {'error': 'Competition not found'}
        
        competition = self.competitions[competition_id]
        
        if competition.is_completed():
            return {'error': 'Competition has ended'}
        
        if competition.max_participants and len(competition.participants) >= competition.max_participants:
            return {'error': 'Competition is full'}
        
        if user_id in competition.participants:
            return {'error': 'Already joined'}
        
        competition.participants.append(user_id)
        self.scores[competition_id][user_id] = 0
        self.user_competition_history[user_id].append(competition_id)
        
        return {
            'success': True,
            'competition_id': competition_id,
            'participant_count': len(competition.participants)
        }
    
    def submit_score(
        self,
        competition_id: str,
        user_id: str,
        score: float,
        metrics: Optional[Dict[str, float]] = None
    ) -> Dict[str, Any]:
        """提交成绩"""
        if competition_id not in self.competitions:
            return {'error': 'Competition not found'}
        
        competition = self.competitions[competition_id]
        
        if user_id not in competition.participants:
            return {'error': 'Not a participant'}
        
        if competition.is_completed():
            return {'error': 'Competition has ended'}
        
        # 更新分数（取最高）
        current_score = self.scores[competition_id].get(user_id, 0)
        new_score = max(current_score, score)
        self.scores[competition_id][user_id] = new_score
        
        return {
            'success': True,
            'submitted_score': score,
            'best_score': new_score,
            'rank': self._get_current_rank(competition_id, user_id)
        }
    
    def _get_current_rank(
        self,
        competition_id: str,
        user_id: str
    ) -> int:
        """获取当前排名"""
        scores = self.scores[competition_id]
        user_score = scores.get(user_id, 0)
        
        # 计算排名（分数高的排名靠前）
        rank = 1
        for uid, score in scores.items():
            if score > user_score:
                rank += 1
        
        return rank
    
    def get_leaderboard(
        self,
        competition_id: str,
        top_k: int = 10
    ) -> List[LeaderboardEntry]:
        """
        获取排行榜
        
        Args:
            competition_id: 竞赛ID
            top_k: 返回数量
        
        Returns:
            排行榜条目列表
        """
        if competition_id not in self.competitions:
            return []
        
        scores = self.scores[competition_id]
        
        # 排序
        sorted_scores = sorted(
            scores.items(),
            key=lambda x: x[1],
            reverse=True
        )
        
        # 构建排行榜
        leaderboard = []
        for rank, (user_id, score) in enumerate(sorted_scores[:top_k], 1):
            entry = LeaderboardEntry(
                rank=rank,
                user_id=user_id,
                score=score,
                metrics={}  # 可以从其他数据获取
            )
            leaderboard.append(entry)
        
        return leaderboard
    
    def get_competition_result(
        self,
        competition_id: str
    ) -> Dict[str, Any]:
        """获取竞赛结果"""
        if competition_id not in self.competitions:
            return {'error': 'Competition not found'}
        
        competition = self.competitions[competition_id]
        leaderboard = self.get_leaderboard(competition_id, top_k=100)
        
        return {
            'competition_id': competition_id,
            'name': competition.name,
            'type': competition.competition_type.value,
            'status': 'completed' if competition.is_completed() else 'active',
            'participant_count': len(competition.participants),
            'leaderboard': [
                {
                    'rank': entry.rank,
                    'user_id': entry.user_id,
                    'score': entry.score
                }
                for entry in leaderboard
            ],
            'rewards': competition.rewards
        }
    
    def create_daily_challenge(self) -> Competition:
        """创建每日挑战"""
        # 生成随机挑战内容
        challenge_types = ['speed', 'accuracy', 'streak', 'mastery']
        challenge_type = random.choice(challenge_types)
        
        descriptions = {
            'speed': '在尽可能短的时间内完成10道题目',
            'accuracy': '完成练习并达到95%以上的正确率',
            'streak': '连续答对5道题',
            'mastery': '完全掌握一个新概念'
        }
        
        competition = self.create_competition(
            name=f'每日挑战 - {datetime.utcnow().strftime("%m月%d日")}',
            description=descriptions[challenge_type],
            competition_type=CompetitionType.DAILY,
            duration_hours=24,
            rules={'challenge_type': challenge_type},
            rewards={
                'first_place': {'points': 100, 'badge': 'daily_champion'},
                'top_10': {'points': 50},
                'participation': {'points': 10}
            }
        )
        
        return competition
    
    def get_user_stats(self, user_id: str) -> Dict[str, Any]:
        """获取用户竞赛统计"""
        competitions_participated = self.user_competition_history[user_id]
        
        total_competitions = len(competitions_participated)
        wins = 0
        top_3 = 0
        total_score = 0
        
        for comp_id in competitions_participated:
            if comp_id in self.scores and user_id in self.scores[comp_id]:
                score = self.scores[comp_id][user_id]
                total_score += score
                
                rank = self._get_current_rank(comp_id, user_id)
                if rank == 1:
                    wins += 1
                if rank <= 3:
                    top_3 += 1
        
        return {
            'user_id': user_id,
            'total_competitions': total_competitions,
            'wins': wins,
            'top_3_finishes': top_3,
            'total_score': total_score,
            'average_score': total_score / total_competitions if total_competitions > 0 else 0,
            'win_rate': wins / total_competitions if total_competitions > 0 else 0
        }


class GamificationEngine:
    """
    游戏化引擎（整合层）
    
    整合成就系统和竞赛系统，提供统一的游戏化体验
    """
    
    def __init__(self):
        self.achievement_system = AchievementSystem()
        self.competition_manager = CompetitionManager()
        
        # 用户积分
        self.user_points: Dict[str, int] = defaultdict(int)
        
        # 用户等级
        self.user_levels: Dict[str, int] = defaultdict(int)
        self.level_thresholds = [0, 100, 300, 600, 1000, 1500, 2200, 3000, 4000, 5000]
    
    def process_learning_event(
        self,
        user_id: str,
        event_type: str,
        event_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        处理学习事件，更新游戏化状态
        
        Args:
            user_id: 用户ID
            event_type: 事件类型
            event_data: 事件数据
        
        Returns:
            更新结果（新成就、升级等）
        """
        result = {
            'user_id': user_id,
            'new_achievements': [],
            'points_earned': 0,
            'level_up': None
        }
        
        # 根据事件类型更新进度
        if event_type == 'concept_mastered':
            new_achievements = self.achievement_system.update_progress(
                user_id, 'concepts_mastered', 1
            )
            result['new_achievements'].extend(new_achievements)
            result['points_earned'] += 10
        
        elif event_type == 'daily_learning_completed':
            new_achievements = self.achievement_system.update_progress(
                user_id, 'learning_days', 1
            )
            result['new_achievements'].extend(new_achievements)
            result['points_earned'] += 5
        
        elif event_type == 'exercise_completed':
            score = event_data.get('score', 0)
            if score == 100:
                new_achievements = self.achievement_system.update_progress(
                    user_id, 'exercise_score', score, is_increment=False
                )
                result['new_achievements'].extend(new_achievements)
            result['points_earned'] += int(score / 10)
        
        elif event_type == 'help_given':
            new_achievements = self.achievement_system.update_progress(
                user_id, 'help_given', 1
            )
            result['new_earned'] = 0
            result['new_achievements'].extend(new_achievements)
            result['points_earned'] += 5
        
        # 更新积分
        self.user_points[user_id] += result['points_earned']
        
        # 检查升级
        old_level = self.user_levels[user_id]
        new_level = self._calculate_level(self.user_points[user_id])
        
        if new_level > old_level:
            self.user_levels[user_id] = new_level
            result['level_up'] = {
                'old_level': old_level,
                'new_level': new_level,
                'rewards': self._get_level_rewards(new_level)
            }
        
        return result
    
    def _calculate_level(self, points: int) -> int:
        """根据积分计算等级"""
        for level, threshold in enumerate(self.level_thresholds):
            if points < threshold:
                return level - 1 if level > 0 else 0
        return len(self.level_thresholds) - 1
    
    def _get_level_rewards(self, level: int) -> Dict[str, Any]:
        """获取等级奖励"""
        rewards = {
            'title': self._get_level_title(level),
            'features_unlocked': [],
            'bonus_points': level * 10
        }
        
        if level >= 3:
            rewards['features_unlocked'].append('custom_avatar')
        if level >= 5:
            rewards['features_unlocked'].append('advanced_analytics')
        if level >= 8:
            rewards['features_unlocked'].append('mentor_status')
        
        return rewards
    
    def _get_level_title(self, level: int) -> str:
        """获取等级称号"""
        titles = [
            '初学者',
            '探索者',
            '学习者',
            '实践者',
            '掌握者',
            '专家',
            '大师',
            '学者',
            '导师',
            '传奇'
        ]
        return titles[min(level, len(titles) - 1)]
    
    def get_user_gamification_summary(self, user_id: str) -> Dict[str, Any]:
        """获取用户游戏化摘要"""
        return {
            'user_id': user_id,
            'level': self.user_levels[user_id],
            'title': self._get_level_title(self.user_levels[user_id]),
            'current_points': self.user_points[user_id],
            'next_level_points': self.level_thresholds[
                min(self.user_levels[user_id] + 1, len(self.level_thresholds) - 1)
            ],
            'achievements': self.achievement_system.get_user_achievements(user_id),
            'competition_stats': self.competition_manager.get_user_stats(user_id)
        }
