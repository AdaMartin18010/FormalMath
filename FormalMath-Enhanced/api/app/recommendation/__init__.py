"""
推荐系统模块 v2.0
================

包含以下核心功能:
- 动态难度调整、自适应内容推荐
- 多目标优化、混合推荐算法
- A/B测试框架、性能评估报告

新增功能（v2.0）:
- 高级混合推荐器 (AdvancedHybridRecommender)
- 动态权重调整 (DynamicWeightAdjuster)
- 多样性增强 (DiversityEnhancer)
- 冷启动处理 (ColdStartHandler)
- 可解释性引擎 (ExplainabilityEngine)
- A/B测试框架 (ABTestingManager)
- 性能评估报告 (EvaluationReportGenerator)
"""

# 基础推荐器
from .adaptive_difficulty import AdaptiveDifficultyManager, DifficultyCalibration
from .content_recommender import ContentRecommender, RecommendationEngine
from .multi_objective import MultiObjectiveOptimizer, ObjectiveBalance

# 混合推荐器
from .hybrid_recommender import HybridRecommender, RecommendationResult
from .hybrid_recommender_optimized import (
    HybridRecommenderOptimized,
    DynamicWeightOptimizer,
    UserFeedback
)

# 新增高级推荐系统 v2.0
from .advanced_hybrid_recommender import (
    AdvancedHybridRecommender,
    DynamicWeightAdjuster,
    DiversityEnhancer,
    ColdStartHandler,
    ExplainabilityEngine,
    RecommenderType,
    UserAction,
    ColdStartLevel,
    RecommendationItem,
    ExplanationReport,
    get_advanced_recommender
)

# A/B测试框架
from .ab_testing_framework import (
    ABTestingManager,
    TestStatus,
    MetricType,
    AllocationMethod,
    Variant,
    Metric,
    TestResult,
    ABTest,
    create_default_manager,
    get_ab_testing_manager
)

# 性能评估报告
from .evaluation_report import (
    EvaluationReportGenerator,
    AccuracyMetrics,
    DiversityMetrics,
    CoverageMetrics,
    UserSatisfactionMetrics,
    PerformanceMetrics,
    ColdStartMetrics,
    EvaluationResult,
    create_evaluation_report
)

__version__ = "2.0.0"

__all__ = [
    # 版本信息
    '__version__',
    
    # 基础推荐器
    'AdaptiveDifficultyManager',
    'DifficultyCalibration',
    'ContentRecommender',
    'RecommendationEngine',
    'MultiObjectiveOptimizer',
    'ObjectiveBalance',
    
    # 混合推荐器
    'HybridRecommender',
    'RecommendationResult',
    'HybridRecommenderOptimized',
    'DynamicWeightOptimizer',
    'UserFeedback',
    
    # 高级推荐系统 v2.0
    'AdvancedHybridRecommender',
    'DynamicWeightAdjuster',
    'DiversityEnhancer',
    'ColdStartHandler',
    'ExplainabilityEngine',
    'RecommenderType',
    'UserAction',
    'ColdStartLevel',
    'RecommendationItem',
    'ExplanationReport',
    'get_advanced_recommender',
    
    # A/B测试框架
    'ABTestingManager',
    'TestStatus',
    'MetricType',
    'AllocationMethod',
    'Variant',
    'Metric',
    'TestResult',
    'ABTest',
    'create_default_manager',
    'get_ab_testing_manager',
    
    # 性能评估报告
    'EvaluationReportGenerator',
    'AccuracyMetrics',
    'DiversityMetrics',
    'CoverageMetrics',
    'UserSatisfactionMetrics',
    'PerformanceMetrics',
    'ColdStartMetrics',
    'EvaluationResult',
    'create_evaluation_report',
]
