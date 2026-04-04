"""
推荐系统模块
包含动态难度调整、自适应内容推荐、多目标优化
"""
from .adaptive_difficulty import AdaptiveDifficultyManager, DifficultyCalibration
from .content_recommender import ContentRecommender, RecommendationEngine
from .multi_objective import MultiObjectiveOptimizer, ObjectiveBalance

__all__ = [
    'AdaptiveDifficultyManager',
    'DifficultyCalibration',
    'ContentRecommender',
    'RecommendationEngine',
    'MultiObjectiveOptimizer',
    'ObjectiveBalance',
]
