"""
游戏化模块
成就系统、进度徽章、挑战任务
"""
from .badges import BadgeSystem, Badge, BadgeTier
from .challenges import ChallengeSystem, Challenge, ChallengeType
from .progress_visualization import ProgressTracker, MilestoneManager

__all__ = [
    'BadgeSystem',
    'Badge',
    'BadgeTier',
    'ChallengeSystem',
    'Challenge',
    'ChallengeType',
    'ProgressTracker',
    'MilestoneManager',
]
