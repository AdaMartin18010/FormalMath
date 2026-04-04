"""
机器学习模块 - 认知模型增强
包含知识追踪DNC、遗忘曲线建模、个体差异建模
"""
from .dnc_knowledge_tracing import DNCKnowledgeTracer, KnowledgeState
from .forgetting_curve import ForgettingCurveModel, SpacedRepetitionScheduler
from .individual_differences import IndividualDifferenceModel, LearningStyleProfile

__all__ = [
    'DNCKnowledgeTracer',
    'KnowledgeState',
    'ForgettingCurveModel',
    'SpacedRepetitionScheduler',
    'IndividualDifferenceModel',
    'LearningStyleProfile',
]
