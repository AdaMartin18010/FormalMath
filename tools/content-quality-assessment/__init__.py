#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量评估系统
Content Quality Assessment System for FormalMath

该模块提供数学文档的自动化质量评估功能，包括：
- 完整性检查
- 准确性验证
- 可读性评估
- 国际化评估
- 学习效果预测

主要组件：
- ContentQualityAssessor: 质量评估器
- ReportGenerator: 报告生成器
- IssueExtractor: 问题提取器

使用示例：
    from content_quality_assessment import ContentQualityAssessor, ReportGenerator
    
    # 评估文档
    assessor = ContentQualityAssessor()
    result = assessor.assess_file("path/to/document.md")
    
    # 生成报告
    generator = ReportGenerator()
    generator.generate_html_report([result], assessor.get_summary())

版本：1.0.0
作者：FormalMath AI
"""

__version__ = '1.0.0'
__author__ = 'FormalMath AI'

from .quality_assessor import (
    ContentQualityAssessor,
    QualityAssessmentResult,
    CompletenessMetrics,
    AccuracyMetrics,
    ReadabilityMetrics,
    InternationalizationMetrics,
    LearningEffectMetrics,
    QualityLevel
)

from .report_generator import ReportGenerator

from .issue_extractor import (
    IssueExtractor,
    IssueItem,
    IssueCategory,
    BatchIssueProcessor
)

__all__ = [
    'ContentQualityAssessor',
    'QualityAssessmentResult',
    'CompletenessMetrics',
    'AccuracyMetrics',
    'ReadabilityMetrics',
    'InternationalizationMetrics',
    'LearningEffectMetrics',
    'QualityLevel',
    'ReportGenerator',
    'IssueExtractor',
    'IssueItem',
    'IssueCategory',
    'BatchIssueProcessor',
]
