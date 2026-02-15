# -*- coding: utf-8 -*-
"""
FormalMath Assessment System

形式化数学知识库评估系统

主要模块:
- assessment_system: 核心评估系统
- evaluation_criteria: 评价指标定义
- scoring_engine: 评分引擎
- feedback_generator: 反馈生成器
- report_generator: 报告生成器
"""

from .evaluation_criteria import (
    AssessmentType,
    EvaluationLevel,
    ConceptualUnderstanding,
    ProceduralFluency,
    StrategicCompetence,
    AdaptiveReasoning,
    ProductiveDisposition,
    MathematicalAbilityProfile,
    LearnerProfile,
    EvaluationCriteria
)

from .scoring_engine import (
    ScoringEngine,
    ScoringAlgorithm,
    WeightedScoringModel,
    ValueAddedScoringModel,
    PerformanceScoringModel,
    DivergentThinkingScoringModel,
    ProcessScoringModel
)

from .feedback_generator import (
    FeedbackType,
    FeedbackPriority,
    FeedbackItem,
    FeedbackReport,
    FeedbackGenerator,
    RealTimeFeedbackGenerator
)

from .report_generator import (
    ReportType,
    ReportFormat,
    ReportSection,
    AssessmentReport,
    ReportGenerator,
    ProgressReportGenerator,
    AbilityReportGenerator,
    ValueAddedReportGenerator,
    ReportExporter
)

from .assessment_system import (
    AssessmentConfig,
    AssessmentSession,
    AssessmentResult,
    FormalMathAssessmentSystem
)

__version__ = '1.0.0'
__author__ = 'FormalMath Team'

__all__ = [
    # 评估系统
    'FormalMathAssessmentSystem',
    'AssessmentConfig',
    'AssessmentSession',
    'AssessmentResult',
    
    # 评价指标
    'AssessmentType',
    'EvaluationLevel',
    'ConceptualUnderstanding',
    'ProceduralFluency',
    'StrategicCompetence',
    'AdaptiveReasoning',
    'ProductiveDisposition',
    'MathematicalAbilityProfile',
    'LearnerProfile',
    'EvaluationCriteria',
    
    # 评分引擎
    'ScoringEngine',
    'ScoringAlgorithm',
    'WeightedScoringModel',
    'ValueAddedScoringModel',
    'PerformanceScoringModel',
    'DivergentThinkingScoringModel',
    'ProcessScoringModel',
    
    # 反馈生成
    'FeedbackType',
    'FeedbackPriority',
    'FeedbackItem',
    'FeedbackReport',
    'FeedbackGenerator',
    'RealTimeFeedbackGenerator',
    
    # 报告生成
    'ReportType',
    'ReportFormat',
    'ReportSection',
    'AssessmentReport',
    'ReportGenerator',
    'ProgressReportGenerator',
    'AbilityReportGenerator',
    'ValueAddedReportGenerator',
    'ReportExporter'
]
