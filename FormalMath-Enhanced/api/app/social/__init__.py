"""
社交学习模块
包含学习小组推荐、同伴互助匹配、竞争激励机制
"""
from .peer_matching import PeerMatcher, StudyPartnerProfile
from .group_recommendation import GroupRecommender, StudyGroup
from .competition_system import CompetitionManager, AchievementSystem

__all__ = [
    'PeerMatcher',
    'StudyPartnerProfile',
    'GroupRecommender',
    'StudyGroup',
    'CompetitionManager',
    'AchievementSystem',
]
