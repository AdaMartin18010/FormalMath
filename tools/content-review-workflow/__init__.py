#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
内容审核工作流系统
Content Review Workflow System

提供完整的内容质量审核流程自动化功能。

主要组件:
- ContentReviewWorkflow: 主工作流控制器
- QualityChecker: 内容质量检查器
- ReviewTracker: 审核状态追踪系统
- ManualReviewWorkflow: 人工审核流程
- ReviewReportGenerator: 审核报告生成器

使用示例:
    from content_review_workflow import ContentReviewWorkflow
    
    workflow = ContentReviewWorkflow()
    result = workflow.submit_document("docs/test.md", "user1")
    print(f"文档ID: {result['document_id']}")
"""

__version__ = "1.0.0"
__author__ = "FormalMath Team"

# 导入主要组件
from .review_workflow import ContentReviewWorkflow
from .quality_checker import QualityChecker, QualityReport, Issue, Severity
from .review_tracker import ReviewTracker, ReviewStatus, ReviewRecord, ReviewEvent
from .manual_review import ManualReviewWorkflow, ReviewDecision
from .report_generator import ReviewReportGenerator

__all__ = [
    'ContentReviewWorkflow',
    'QualityChecker',
    'QualityReport',
    'Issue',
    'Severity',
    'ReviewTracker',
    'ReviewStatus',
    'ReviewRecord',
    'ReviewEvent',
    'ManualReviewWorkflow',
    'ReviewDecision',
    'ReviewReportGenerator',
]
