"""
机器学习模块 - 认知模型增强 v2.0
包含知识追踪DNC、遗忘曲线建模、个体差异建模、知识图谱嵌入、路径规划
"""

# 基础模块
from .dnc_knowledge_tracing import DNCKnowledgeTracer, MultiHeadKnowledgeTracer, KnowledgeState
from .forgetting_curve import ForgettingCurveModel, SpacedRepetitionScheduler
from .individual_differences import IndividualDifferenceModel, LearningStyleProfile

# 新增优化模块
from .knowledge_graph_embedding import (
    KnowledgeGraphEmbedder,
    KnowledgeGraph,
    ConceptNode,
    RelationEdge,
    GraphEmbeddingModel
)
from .path_planner import (
    AStarPathPlanner,
    AdaptivePathPlanner,
    MultiObjectivePathOptimizer,
    LearningPath,
    PathNode,
    PathOptimizationGoal
)
from .goal_based_recommender import (
    GoalBasedRecommender,
    GoalAnalyzer,
    LearningGoal,
    GoalProgress,
    GoalType
)
from .dynamic_adapter import (
    DynamicRecommender,
    SignalDetector,
    StrategyAdapter,
    DifficultyAdjuster,
    AdaptationAction,
    AdaptationTrigger,
    LearningSignal
)
from .path_evaluator import (
    PathEvaluator,
    ABTestFramework,
    PathComparator,
    PathMetrics,
    ABTestResult
)
from .learning_engine import PersonalizedLearningEngine, get_learning_engine

__all__ = [
    # 基础模块
    'DNCKnowledgeTracer',
    'MultiHeadKnowledgeTracer',
    'KnowledgeState',
    'ForgettingCurveModel',
    'SpacedRepetitionScheduler',
    'IndividualDifferenceModel',
    'LearningStyleProfile',
    
    # 知识图谱
    'KnowledgeGraphEmbedder',
    'KnowledgeGraph',
    'ConceptNode',
    'RelationEdge',
    'GraphEmbeddingModel',
    
    # 路径规划
    'AStarPathPlanner',
    'AdaptivePathPlanner',
    'MultiObjectivePathOptimizer',
    'LearningPath',
    'PathNode',
    'PathOptimizationGoal',
    
    # 目标导向推荐
    'GoalBasedRecommender',
    'GoalAnalyzer',
    'LearningGoal',
    'GoalProgress',
    'GoalType',
    
    # 动态调整
    'DynamicRecommender',
    'SignalDetector',
    'StrategyAdapter',
    'DifficultyAdjuster',
    'AdaptationAction',
    'AdaptationTrigger',
    'LearningSignal',
    
    # 路径评估
    'PathEvaluator',
    'ABTestFramework',
    'PathComparator',
    'PathMetrics',
    'ABTestResult',
    
    # 学习引擎
    'PersonalizedLearningEngine',
    'get_learning_engine',
]
