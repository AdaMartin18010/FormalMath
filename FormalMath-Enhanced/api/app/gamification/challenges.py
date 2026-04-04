"""
挑战任务系统
日常挑战、周挑战、特殊挑战
"""
import random
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from collections import defaultdict


class ChallengeType(str, Enum):
    """挑战类型"""
    DAILY = "daily"
    WEEKLY = "weekly"
    SPECIAL = "special"
    STREAK = "streak"
    COMMUNITY = "community"


class ChallengeDifficulty(str, Enum):
    """挑战难度"""
    EASY = "easy"
    MEDIUM = "medium"
    HARD = "hard"
    EXPERT = "expert"


@dataclass
class ChallengeTask:
    """挑战任务"""
    task_id: str
    description: str
    target_type: str
    target_value: float
    current_value: float = 0
    is_completed: bool = False


@dataclass
class Challenge:
    """挑战定义"""
    challenge_id: str
    title: str
    description: str
    challenge_type: ChallengeType
    difficulty: ChallengeDifficulty
    
    # 任务列表
    tasks: List[ChallengeTask] = field(default_factory=list)
    
    # 时间
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    
    # 奖励
    points_reward: int = 0
    badge_reward: Optional[str] = None
    bonus_multiplier: float = 1.0
    
    # 元数据
    tags: List[str] = field(default_factory=list)
    required_level: int = 0
    
    def is_active(self) -> bool:
        now = datetime.utcnow()
        if self.start_time and now < self.start_time:
            return False
        if self.end_time and now > self.end_time:
            return False
        return True
    
    def get_progress(self) -> float:
        """获取整体进度"""
        if not self.tasks:
            return 0.0
        
        completed = sum(1 for t in self.tasks if t.is_completed)
        return completed / len(self.tasks)
    
    def is_fully_completed(self) -> bool:
        """检查是否全部完成"""
        return all(t.is_completed for t in self.tasks)


@dataclass
class UserChallenge:
    """用户挑战记录"""
    user_id: str
    challenge: Challenge
    accepted_at: datetime
    completed_at: Optional[datetime] = None
    task_progress: Dict[str, float] = field(default_factory=dict)
    
    def get_overall_progress(self) -> float:
        """获取整体进度"""
        if not self.challenge.tasks:
            return 0.0
        
        total_progress = 0
        for task in self.challenge.tasks:
            progress = self.task_progress.get(task.task_id, 0)
            total_progress += min(1.0, progress / task.target_value) if task.target_value > 0 else 0
        
        return total_progress / len(self.challenge.tasks)


class ChallengeSystem:
    """
    挑战系统
    
    生成、管理和跟踪挑战任务
    """
    
    # 难度奖励倍率
    DIFFICULTY_MULTIPLIERS = {
        ChallengeDifficulty.EASY: 1.0,
        ChallengeDifficulty.MEDIUM: 1.5,
        ChallengeDifficulty.HARD: 2.5,
        ChallengeDifficulty.EXPERT: 4.0
    }
    
    def __init__(self):
        self.challenges: Dict[str, Challenge] = {}
        self.user_challenges: Dict[str, List[UserChallenge]] = defaultdict(list)
        self.challenge_templates: List[Dict] = []
        
        # 每日/每周挑战跟踪
        self.current_daily: Optional[str] = None
        self.current_weekly: Optional[str] = None
        self.last_daily_update: Optional[datetime] = None
        self.last_weekly_update: Optional[datetime] = None
        
        # 初始化模板
        self._init_challenge_templates()
        
        # 生成初始挑战
        self._ensure_daily_challenge()
    
    def _init_challenge_templates(self):
        """初始化挑战模板"""
        self.challenge_templates = [
            # 日常挑战 - 简单
            {
                'type': ChallengeType.DAILY,
                'difficulty': ChallengeDifficulty.EASY,
                'title_templates': [
                    '今日学习',
                    '每日一练',
                    '知识巩固'
                ],
                'task_templates': [
                    {
                        'description': '完成{count}个概念的学习',
                        'target_type': 'concepts_studied',
                        'target_value_range': (1, 3)
                    },
                    {
                        'description': '完成{count}道练习题',
                        'target_type': 'exercises_completed',
                        'target_value_range': (3, 5)
                    },
                    {
                        'description': '学习{minutes}分钟',
                        'target_type': 'study_minutes',
                        'target_value_range': (15, 30)
                    }
                ]
            },
            
            # 日常挑战 - 中等
            {
                'type': ChallengeType.DAILY,
                'difficulty': ChallengeDifficulty.MEDIUM,
                'title_templates': [
                    '深度学习',
                    '技能提升',
                    '知识扩展'
                ],
                'task_templates': [
                    {
                        'description': '掌握{count}个新概念',
                        'target_type': 'concepts_mastered',
                        'target_value_range': (2, 4)
                    },
                    {
                        'description': '完成{count}道困难题目',
                        'target_type': 'hard_exercises',
                        'target_value_range': (2, 3)
                    },
                    {
                        'description': '正确率达到{percent}%',
                        'target_type': 'accuracy_rate',
                        'target_value_range': (80, 90)
                    }
                ]
            },
            
            # 周挑战
            {
                'type': ChallengeType.WEEKLY,
                'difficulty': ChallengeDifficulty.MEDIUM,
                'title_templates': [
                    '周度目标',
                    '一周突破',
                    '持续进步'
                ],
                'task_templates': [
                    {
                        'description': '本周掌握{count}个概念',
                        'target_type': 'weekly_concepts',
                        'target_value_range': (10, 15)
                    },
                    {
                        'description': '累计学习{minutes}分钟',
                        'target_type': 'weekly_minutes',
                        'target_value_range': (120, 180)
                    },
                    {
                        'description': '完成{count}天学习',
                        'target_type': 'active_days',
                        'target_value_range': (5, 7)
                    }
                ]
            },
            
            # 特殊挑战 - 连续
            {
                'type': ChallengeType.STREAK,
                'difficulty': ChallengeDifficulty.HARD,
                'title_templates': [
                    '连续挑战',
                    '毅力考验',
                    '坚持到底'
                ],
                'task_templates': [
                    {
                        'description': '连续{count}天完成所有日常任务',
                        'target_type': 'daily_completion_streak',
                        'target_value_range': (3, 7)
                    }
                ]
            },
            
            # 特殊挑战 - 精准
            {
                'type': ChallengeType.SPECIAL,
                'difficulty': ChallengeDifficulty.EXPERT,
                'title_templates': [
                    '完美挑战',
                    '精准大师',
                    '零失误'
                ],
                'task_templates': [
                    {
                        'description': '连续答对{count}道题',
                        'target_type': 'consecutive_correct',
                        'target_value_range': (10, 20)
                    },
                    {
                        'description': '一次练习获得满分',
                        'target_type': 'perfect_score',
                        'target_value_range': (1, 1)
                    }
                ]
            },
            
            # 社区挑战
            {
                'type': ChallengeType.COMMUNITY,
                'difficulty': ChallengeDifficulty.MEDIUM,
                'title_templates': [
                    '团队挑战',
                    '社区贡献',
                    '互助学习'
                ],
                'task_templates': [
                    {
                        'description': '帮助{count}位学习者',
                        'target_type': 'help_others',
                        'target_value_range': (3, 5)
                    },
                    {
                        'description': '参与{count}次小组讨论',
                        'target_type': 'group_discussions',
                        'target_value_range': (2, 3)
                    }
                ]
            }
        ]
    
    def _ensure_daily_challenge(self):
        """确保有每日挑战"""
        now = datetime.utcnow()
        
        # 检查是否需要更新每日挑战
        if (self.last_daily_update is None or 
            self.last_daily_update.date() != now.date()):
            self._generate_daily_challenge()
            self.last_daily_update = now
        
        # 检查每周挑战
        if (self.last_weekly_update is None or 
            (now - self.last_weekly_update).days >= 7):
            self._generate_weekly_challenge()
            self.last_weekly_update = now
    
    def _generate_daily_challenge(self) -> Challenge:
        """生成每日挑战"""
        # 随机选择模板
        templates = [
            t for t in self.challenge_templates
            if t['type'] == ChallengeType.DAILY
        ]
        
        if not templates:
            templates = [self.challenge_templates[0]]
        
        template = random.choice(templates)
        
        # 生成挑战
        challenge = self._create_challenge_from_template(
            template,
            ChallengeType.DAILY,
            duration_hours=24
        )
        
        self.challenges[challenge.challenge_id] = challenge
        self.current_daily = challenge.challenge_id
        
        return challenge
    
    def _generate_weekly_challenge(self) -> Challenge:
        """生成每周挑战"""
        templates = [
            t for t in self.challenge_templates
            if t['type'] == ChallengeType.WEEKLY
        ]
        
        if not templates:
            return None
        
        template = random.choice(templates)
        
        challenge = self._create_challenge_from_template(
            template,
            ChallengeType.WEEKLY,
            duration_hours=168  # 7天
        )
        
        self.challenges[challenge.challenge_id] = challenge
        self.current_weekly = challenge.challenge_id
        
        return challenge
    
    def _create_challenge_from_template(
        self,
        template: Dict,
        challenge_type: ChallengeType,
        duration_hours: int
    ) -> Challenge:
        """从模板创建挑战"""
        challenge_id = f"{challenge_type.value}_{int(datetime.utcnow().timestamp())}"
        
        # 选择标题
        title = random.choice(template['title_templates'])
        
        # 生成任务
        tasks = []
        num_tasks = random.randint(1, 3)
        selected_templates = random.sample(
            template['task_templates'],
            min(num_tasks, len(template['task_templates']))
        )
        
        for i, task_template in enumerate(selected_templates):
            min_val, max_val = task_template['target_value_range']
            target_value = random.randint(int(min_val), int(max_val))
            
            description = task_template['description'].format(
                count=target_value,
                minutes=target_value * 15,
                percent=target_value
            )
            
            task = ChallengeTask(
                task_id=f"{challenge_id}_task_{i}",
                description=description,
                target_type=task_template['target_type'],
                target_value=target_value
            )
            tasks.append(task)
        
        # 计算奖励
        base_points = len(tasks) * 10
        difficulty_mult = self.DIFFICULTY_MULTIPLIERS[template['difficulty']]
        points_reward = int(base_points * difficulty_mult)
        
        now = datetime.utcnow()
        
        return Challenge(
            challenge_id=challenge_id,
            title=title,
            description=f'完成以下任务以获得奖励',
            challenge_type=challenge_type,
            difficulty=template['difficulty'],
            tasks=tasks,
            start_time=now,
            end_time=now + timedelta(hours=duration_hours),
            points_reward=points_reward,
            bonus_multiplier=difficulty_mult
        )
    
    def get_available_challenges(
        self,
        user_id: str,
        user_level: int = 0
    ) -> List[Dict]:
        """
        获取可用挑战
        
        Args:
            user_id: 用户ID
            user_level: 用户等级
        
        Returns:
            可用挑战列表
        """
        self._ensure_daily_challenge()
        
        # 获取用户已接受的活跃挑战
        user_active = {
            uc.challenge.challenge_id
            for uc in self.user_challenges[user_id]
            if uc.completed_at is None
        }
        
        available = []
        
        # 优先返回当前每日/每周挑战
        for challenge_id in [self.current_daily, self.current_weekly]:
            if challenge_id and challenge_id in self.challenges:
                challenge = self.challenges[challenge_id]
                
                if challenge.is_active() and challenge_id not in user_active:
                    if challenge.required_level <= user_level:
                        available.append(self._format_challenge(challenge))
        
        return available
    
    def accept_challenge(
        self,
        user_id: str,
        challenge_id: str
    ) -> Dict[str, Any]:
        """
        接受挑战
        
        Args:
            user_id: 用户ID
            challenge_id: 挑战ID
        
        Returns:
            结果
        """
        if challenge_id not in self.challenges:
            return {'error': 'Challenge not found'}
        
        challenge = self.challenges[challenge_id]
        
        if not challenge.is_active():
            return {'error': 'Challenge is not active'}
        
        # 检查是否已接受
        existing = any(
            uc.challenge.challenge_id == challenge_id
            for uc in self.user_challenges[user_id]
        )
        
        if existing:
            return {'error': 'Already accepted this challenge'}
        
        # 创建用户挑战记录
        user_challenge = UserChallenge(
            user_id=user_id,
            challenge=challenge,
            accepted_at=datetime.utcnow()
        )
        
        self.user_challenges[user_id].append(user_challenge)
        
        return {
            'success': True,
            'challenge_id': challenge_id,
            'accepted_at': user_challenge.accepted_at.isoformat(),
            'deadline': challenge.end_time.isoformat() if challenge.end_time else None
        }
    
    def update_challenge_progress(
        self,
        user_id: str,
        target_type: str,
        value: float,
        is_increment: bool = True
    ) -> List[Dict]:
        """
        更新挑战进度
        
        Args:
            user_id: 用户ID
            target_type: 目标类型
            value: 值
            is_increment: 是否为增量
        
        Returns:
            完成的挑战列表
        """
        completed_challenges = []
        
        for user_challenge in self.user_challenges[user_id]:
            if user_challenge.completed_at:
                continue
            
            challenge = user_challenge.challenge
            
            # 检查是否过期
            if challenge.end_time and datetime.utcnow() > challenge.end_time:
                continue
            
            # 更新任务进度
            for task in challenge.tasks:
                if task.target_type == target_type:
                    if is_increment:
                        current = user_challenge.task_progress.get(task.task_id, 0)
                        user_challenge.task_progress[task.task_id] = current + value
                    else:
                        user_challenge.task_progress[task.task_id] = value
                    
                    # 检查任务完成
                    if not task.is_completed:
                        current_progress = user_challenge.task_progress.get(task.task_id, 0)
                        if current_progress >= task.target_value:
                            task.is_completed = True
            
            # 检查挑战完成
            if challenge.is_fully_completed() and not user_challenge.completed_at:
                user_challenge.completed_at = datetime.utcnow()
                completed_challenges.append({
                    'challenge_id': challenge.challenge_id,
                    'title': challenge.title,
                    'points_earned': challenge.points_reward,
                    'completed_at': user_challenge.completed_at.isoformat()
                })
        
        return completed_challenges
    
    def get_user_challenges(
        self,
        user_id: str,
        status: str = 'active'  # active, completed, all
    ) -> Dict[str, Any]:
        """
        获取用户挑战
        
        Args:
            user_id: 用户ID
            status: 状态过滤
        
        Returns:
            挑战列表
        """
        self._ensure_daily_challenge()
        
        user_challenges = self.user_challenges[user_id]
        
        if status == 'active':
            filtered = [
                uc for uc in user_challenges
                if uc.completed_at is None
            ]
        elif status == 'completed':
            filtered = [
                uc for uc in user_challenges
                if uc.completed_at is not None
            ]
        else:
            filtered = user_challenges
        
        return {
            'user_id': user_id,
            'active_count': sum(1 for uc in user_challenges if uc.completed_at is None),
            'completed_count': sum(1 for uc in user_challenges if uc.completed_at is not None),
            'challenges': [self._format_user_challenge(uc) for uc in filtered]
        }
    
    def _format_challenge(self, challenge: Challenge) -> Dict:
        """格式化挑战"""
        return {
            'challenge_id': challenge.challenge_id,
            'title': challenge.title,
            'description': challenge.description,
            'type': challenge.challenge_type.value,
            'difficulty': challenge.difficulty.value,
            'points_reward': challenge.points_reward,
            'end_time': challenge.end_time.isoformat() if challenge.end_time else None,
            'tasks': [
                {
                    'task_id': task.task_id,
                    'description': task.description,
                    'target_value': task.target_value
                }
                for task in challenge.tasks
            ]
        }
    
    def _format_user_challenge(self, user_challenge: UserChallenge) -> Dict:
        """格式化用户挑战"""
        challenge = user_challenge.challenge
        
        return {
            'challenge_id': challenge.challenge_id,
            'title': challenge.title,
            'type': challenge.challenge_type.value,
            'difficulty': challenge.difficulty.value,
            'accepted_at': user_challenge.accepted_at.isoformat(),
            'completed_at': user_challenge.completed_at.isoformat() if user_challenge.completed_at else None,
            'progress': user_challenge.get_overall_progress(),
            'points_reward': challenge.points_reward,
            'tasks': [
                {
                    'task_id': task.task_id,
                    'description': task.description,
                    'target': task.target_value,
                    'current': user_challenge.task_progress.get(task.task_id, 0),
                    'completed': task.is_completed
                }
                for task in challenge.tasks
            ],
            'time_remaining': self._calculate_time_remaining(challenge)
        }
    
    def _calculate_time_remaining(self, challenge: Challenge) -> Optional[int]:
        """计算剩余时间（分钟）"""
        if not challenge.end_time:
            return None
        
        remaining = challenge.end_time - datetime.utcnow()
        return max(0, int(remaining.total_seconds() / 60))
    
    def create_custom_challenge(
        self,
        title: str,
        tasks: List[Dict],
        duration_days: int = 7,
        difficulty: ChallengeDifficulty = ChallengeDifficulty.MEDIUM
    ) -> Challenge:
        """
        创建自定义挑战
        
        Args:
            title: 标题
            tasks: 任务列表
            duration_days: 持续天数
            difficulty: 难度
        
        Returns:
            创建的挑战
        """
        challenge_id = f"custom_{int(datetime.utcnow().timestamp())}"
        
        challenge_tasks = []
        for i, task_data in enumerate(tasks):
            task = ChallengeTask(
                task_id=f"{challenge_id}_task_{i}",
                description=task_data['description'],
                target_type=task_data['target_type'],
                target_value=task_data['target_value']
            )
            challenge_tasks.append(task)
        
        # 计算奖励
        base_points = len(tasks) * 15
        points_reward = int(base_points * self.DIFFICULTY_MULTIPLIERS[difficulty])
        
        now = datetime.utcnow()
        
        challenge = Challenge(
            challenge_id=challenge_id,
            title=title,
            description='自定义挑战',
            challenge_type=ChallengeType.SPECIAL,
            difficulty=difficulty,
            tasks=challenge_tasks,
            start_time=now,
            end_time=now + timedelta(days=duration_days),
            points_reward=points_reward
        )
        
        self.challenges[challenge_id] = challenge
        
        return challenge
    
    def get_challenge_statistics(self, user_id: str) -> Dict[str, Any]:
        """获取挑战统计"""
        user_challenges = self.user_challenges[user_id]
        
        completed = [uc for uc in user_challenges if uc.completed_at]
        active = [uc for uc in user_challenges if not uc.completed_at]
        
        total_points = sum(
            uc.challenge.points_reward for uc in completed
        )
        
        # 按类型统计
        by_type = defaultdict(int)
        for uc in completed:
            by_type[uc.challenge.challenge_type.value] += 1
        
        # 按难度统计
        by_difficulty = defaultdict(int)
        for uc in completed:
            by_difficulty[uc.challenge.difficulty.value] += 1
        
        return {
            'user_id': user_id,
            'total_challenges_accepted': len(user_challenges),
            'total_completed': len(completed),
            'total_active': len(active),
            'completion_rate': len(completed) / len(user_challenges) if user_challenges else 0,
            'total_points_earned': total_points,
            'by_type': dict(by_type),
            'by_difficulty': dict(by_difficulty),
            'current_streak': self._calculate_challenge_streak(user_id)
        }
    
    def _calculate_challenge_streak(self, user_id: str) -> int:
        """计算挑战完成连续天数"""
        completed = [
            uc for uc in self.user_challenges[user_id]
            if uc.completed_at
        ]
        
        if not completed:
            return 0
        
        # 按完成日期排序
        completion_dates = sorted([
            uc.completed_at.date()
            for uc in completed
        ], reverse=True)
        
        if not completion_dates:
            return 0
        
        # 计算连续天数
        streak = 1
        today = datetime.utcnow().date()
        
        # 如果今天没有完成，检查昨天
        if completion_dates[0] != today:
            if completion_dates[0] != today - timedelta(days=1):
                return 0
        
        for i in range(1, len(completion_dates)):
            if completion_dates[i] == completion_dates[i-1] - timedelta(days=1):
                streak += 1
            else:
                break
        
        return streak
