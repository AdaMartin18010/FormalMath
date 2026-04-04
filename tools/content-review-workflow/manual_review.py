#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
人工审核流程模块
Manual Review Module

提供人工审核的交互式流程和决策支持功能。
"""

import os
import sys
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass
from datetime import datetime
import json
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class ReviewDecision:
    """审核决策"""
    approved: bool
    reviewer: str
    timestamp: str
    comments: str
    suggestions: Optional[List[str]] = None
    required_changes: Optional[List[str]] = None


class ManualReviewWorkflow:
    """人工审核工作流"""
    
    def __init__(self, tracker=None, checker=None):
        """
        初始化人工审核工作流
        
        Args:
            tracker: 审核追踪器实例
            checker: 质量检查器实例
        """
        from review_tracker import ReviewTracker, ReviewStatus
        from quality_checker import QualityChecker
        
        self.tracker = tracker or ReviewTracker()
        self.checker = checker or QualityChecker()
        
        # 审核检查清单
        self.review_checklist = [
            {
                "id": "content_accuracy",
                "question": "内容准确性",
                "description": "数学概念、定理、公式是否准确无误？",
                "weight": 1.0
            },
            {
                "id": "completeness",
                "question": "内容完整性",
                "description": "是否包含定义、示例、证明（如适用）等必要内容？",
                "weight": 0.9
            },
            {
                "id": "clarity",
                "question": "表述清晰度",
                "description": "语言是否清晰、逻辑是否通顺？",
                "weight": 0.8
            },
            {
                "id": "terminology",
                "question": "术语规范性",
                "description": "数学术语是否符合项目标准？",
                "weight": 0.8
            },
            {
                "id": "formatting",
                "question": "格式规范性",
                "description": "Markdown格式、数学公式格式是否正确？",
                "weight": 0.6
            },
            {
                "id": "references",
                "question": "参考文献",
                "description": "是否有适当的参考文献和交叉引用？",
                "weight": 0.5
            },
            {
                "id": "originality",
                "question": "原创性",
                "description": "内容是否有足够的原创性，而非简单复制？",
                "weight": 0.7
            }
        ]
    
    def start_review(self, document_path: str, reviewer: str) -> Optional[str]:
        """
        开始审核流程
        
        Args:
            document_path: 文档路径
            reviewer: 审核员
            
        Returns:
            Optional[str]: 文档ID
        """
        from review_tracker import ReviewStatus
        
        # 获取或创建审核记录
        record = self.tracker.get_record_by_path(document_path)
        
        if record is None:
            logger.error(f"审核记录不存在，请先提交文档: {document_path}")
            return None
        
        doc_id = record.document_id
        
        # 更新状态为审核中
        self.tracker.update_status(
            doc_id,
            ReviewStatus.IN_REVIEW,
            reviewer,
            f"审核员 {reviewer} 开始审核"
        )
        
        logger.info(f"开始审核: {document_path} (ID: {doc_id})")
        return doc_id
    
    def perform_quality_check(self, document_path: str) -> Dict:
        """
        执行质量检查
        
        Args:
            document_path: 文档路径
            
        Returns:
            Dict: 质量检查报告
        """
        report = self.checker.check_document(document_path)
        return report.to_dict()
    
    def interactive_review(self, document_path: str, reviewer: str) -> ReviewDecision:
        """
        交互式审核流程（命令行交互）
        
        Args:
            document_path: 文档路径
            reviewer: 审核员
            
        Returns:
            ReviewDecision: 审核决策
        """
        print(f"\n{'='*60}")
        print(f"开始人工审核: {document_path}")
        print(f"审核员: {reviewer}")
        print(f"{'='*60}\n")
        
        # 1. 自动质量检查
        print("[1/3] 执行自动质量检查...")
        quality_report = self.perform_quality_check(document_path)
        
        print(f"\n质量得分: {quality_report['score']}/100")
        print(f"问题统计: {quality_report['summary']['errors']} 错误, "
              f"{quality_report['summary']['warnings']} 警告, "
              f"{quality_report['summary']['infos']} 信息")
        
        if quality_report['issues']:
            print("\n主要问题:")
            for issue in quality_report['issues'][:5]:
                print(f"  [{issue['severity'].upper()}] {issue['message']}")
        
        # 2. 人工检查清单
        print("\n[2/3] 人工检查清单")
        print("请根据以下标准进行评估 (1-5分，5分为最佳):\n")
        
        scores = {}
        for item in self.review_checklist:
            while True:
                try:
                    score = input(f"  {item['question']} [{item['description']}] (1-5): ")
                    score = int(score)
                    if 1 <= score <= 5:
                        scores[item['id']] = score * item['weight']
                        break
                    else:
                        print("    请输入1-5之间的数字")
                except ValueError:
                    print("    请输入有效的数字")
        
        weighted_score = sum(scores.values()) / sum(item['weight'] for item in self.review_checklist) * 20
        print(f"\n人工评估得分: {weighted_score:.1f}/100")
        
        # 3. 总体决策
        print("\n[3/3] 审核决策")
        print("综合质量得分 (自动70% + 人工30%): "
              f"{quality_report['score'] * 0.7 + weighted_score * 0.3:.1f}/100")
        
        while True:
            decision = input("\n决策 [approve/revise/reject]: ").lower().strip()
            if decision in ['approve', 'revise', 'reject']:
                break
            print("请输入: approve (通过), revise (需修改), 或 reject (拒绝)")
        
        comments = input("\n审核意见: ").strip()
        
        suggestions = []
        if decision in ['revise', 'reject']:
            print("\n请输入改进建议 (每行一条，输入空行结束):")
            while True:
                suggestion = input("  > ").strip()
                if not suggestion:
                    break
                suggestions.append(suggestion)
        
        approved = decision == 'approve'
        
        return ReviewDecision(
            approved=approved,
            reviewer=reviewer,
            timestamp=datetime.now().isoformat(),
            comments=comments,
            suggestions=suggestions if suggestions else None,
            required_changes=suggestions if decision == 'revise' else None
        )
    
    def submit_decision(self, document_id: str, decision: ReviewDecision) -> bool:
        """
        提交审核决策
        
        Args:
            document_id: 文档ID
            decision: 审核决策
            
        Returns:
            bool: 是否成功提交
        """
        from review_tracker import ReviewStatus
        
        if decision.approved:
            new_status = ReviewStatus.APPROVED
            comment = f"审核通过。{decision.comments}"
        elif decision.required_changes:
            new_status = ReviewStatus.NEEDS_REVISION
            comment = f"需要修改。{decision.comments}"
            if decision.suggestions:
                comment += f"\n改进建议: {', '.join(decision.suggestions)}"
        else:
            new_status = ReviewStatus.REJECTED
            comment = f"审核拒绝。{decision.comments}"
        
        success = self.tracker.update_status(
            document_id,
            new_status,
            decision.reviewer,
            comment
        )
        
        if success:
            logger.info(f"审核决策已提交: {document_id} -> {new_status.value}")
        
        return success
    
    def get_pending_reviews(self, reviewer: Optional[str] = None) -> List[Dict]:
        """
        获取待审核列表
        
        Args:
            reviewer: 审核员筛选
            
        Returns:
            List[Dict]: 待审核项目列表
        """
        from review_tracker import ReviewStatus
        
        records = self.tracker.query_records(
            status=ReviewStatus.IN_REVIEW,
            reviewer=reviewer
        )
        
        pending = []
        for record in records:
            # 获取质量报告
            quality = self.perform_quality_check(record.document_path)
            
            pending.append({
                "document_id": record.document_id,
                "document_path": record.document_path,
                "submitter": record.submitter,
                "submit_time": record.submit_time,
                "assigned_reviewer": record.assigned_reviewer,
                "quality_score": quality['score'],
                "issue_count": quality['summary']['errors'] + quality['summary']['warnings']
            })
        
        return pending
    
    def batch_review(self, document_paths: List[str], reviewer: str,
                    auto_threshold: float = 85.0) -> List[Tuple[str, ReviewDecision]]:
        """
        批量审核
        
        Args:
            document_paths: 文档路径列表
            reviewer: 审核员
            auto_threshold: 自动通过阈值（质量得分高于此值自动通过）
            
        Returns:
            List[Tuple[str, ReviewDecision]]: 审核结果列表
        """
        results = []
        
        for doc_path in document_paths:
            print(f"\n处理: {doc_path}")
            
            # 质量检查
            quality_report = self.perform_quality_check(doc_path)
            
            if quality_report['score'] >= auto_threshold and quality_report['summary']['errors'] == 0:
                # 自动通过
                print(f"  自动通过 (得分: {quality_report['score']})")
                decision = ReviewDecision(
                    approved=True,
                    reviewer=reviewer,
                    timestamp=datetime.now().isoformat(),
                    comments="自动审核通过：质量得分超过阈值且无错误"
                )
            else:
                # 需要人工审核
                print(f"  需要人工审核 (得分: {quality_report['score']})")
                decision = ReviewDecision(
                    approved=False,
                    reviewer=reviewer,
                    timestamp=datetime.now().isoformat(),
                    comments="需要人工审核",
                    required_changes=["请人工检查文档质量"]
                )
            
            # 获取文档ID并提交决策
            doc_id = self.tracker.get_record_by_path(doc_path)
            if doc_id:
                self.submit_decision(doc_id.document_id, decision)
            
            results.append((doc_path, decision))
        
        return results
    
    def generate_review_guidelines(self) -> str:
        """
        生成审核指南
        
        Returns:
            str: Markdown格式的审核指南
        """
        guidelines = ["# 内容审核指南\n"]
        
        guidelines.append("## 审核原则\n")
        guidelines.append("1. **准确性优先**: 数学内容的准确性是最重要的\n")
        guidelines.append("2. **建设性反馈**: 提供具体的改进建议\n")
        guidelines.append("3. **一致性**: 保持审核标准的一致性\n")
        guidelines.append("4. **及时性**: 尽快完成审核\n\n")
        
        guidelines.append("## 审核检查清单\n")
        for item in self.review_checklist:
            guidelines.append(f"### {item['question']} (权重: {item['weight']})\n")
            guidelines.append(f"{item['description']}\n")
            guidelines.append("- 5分: 优秀，无可挑剔\n")
            guidelines.append("- 4分: 良好，轻微瑕疵\n")
            guidelines.append("- 3分: 合格，需要改进\n")
            guidelines.append("- 2分: 较差，需要大幅修改\n")
            guidelines.append("- 1分: 不合格，无法接受\n\n")
        
        guidelines.append("## 决策标准\n")
        guidelines.append("- **通过**: 自动得分 ≥ 80 且人工得分 ≥ 70\n")
        guidelines.append("- **需修改**: 有明显问题但可修复\n")
        guidelines.append("- **拒绝**: 存在严重错误或不适合的内容\n")
        
        return ''.join(guidelines)


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(description='人工审核流程')
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 开始审核
    start_parser = subparsers.add_parser('start', help='开始审核')
    start_parser.add_argument('document_path', help='文档路径')
    start_parser.add_argument('--reviewer', '-r', required=True, help='审核员')
    
    # 交互式审核
    interactive_parser = subparsers.add_parser('interactive', help='交互式审核')
    interactive_parser.add_argument('document_path', help='文档路径')
    interactive_parser.add_argument('--reviewer', '-r', required=True, help='审核员')
    
    # 待审核列表
    pending_parser = subparsers.add_parser('pending', help='查看待审核列表')
    pending_parser.add_argument('--reviewer', '-r', help='审核员筛选')
    
    # 批量审核
    batch_parser = subparsers.add_parser('batch', help='批量审核')
    batch_parser.add_argument('directory', help='文档目录')
    batch_parser.add_argument('--reviewer', '-r', required=True, help='审核员')
    batch_parser.add_argument('--threshold', '-t', type=float, default=85.0, help='自动通过阈值')
    
    # 生成指南
    subparsers.add_parser('guidelines', help='生成审核指南')
    
    args = parser.parse_args()
    
    workflow = ManualReviewWorkflow()
    
    if args.command == 'start':
        doc_id = workflow.start_review(args.document_path, args.reviewer)
        if doc_id:
            print(f"审核已开始，文档ID: {doc_id}")
        else:
            print("审核启动失败")
    
    elif args.command == 'interactive':
        doc_id = workflow.start_review(args.document_path, args.reviewer)
        if doc_id:
            decision = workflow.interactive_review(args.document_path, args.reviewer)
            workflow.submit_decision(doc_id, decision)
            print(f"\n审核完成，决策: {'通过' if decision.approved else '未通过'}")
    
    elif args.command == 'pending':
        pending = workflow.get_pending_reviews(args.reviewer)
        print(f"待审核项目 ({len(pending)}):")
        for item in pending:
            print(f"  - {item['document_path']}")
            print(f"    提交者: {item['submitter']}, 质量得分: {item['quality_score']}")
    
    elif args.command == 'batch':
        import glob
        doc_paths = glob.glob(f"{args.directory}/**/*.md", recursive=True)
        results = workflow.batch_review(doc_paths, args.reviewer, args.threshold)
        print(f"\n批量审核完成，共处理 {len(results)} 个文档")
        approved = sum(1 for _, d in results if d.approved)
        print(f"通过: {approved}, 需审核: {len(results) - approved}")
    
    elif args.command == 'guidelines':
        guidelines = workflow.generate_review_guidelines()
        print(guidelines)
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
