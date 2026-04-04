#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
内容审核工作流主控模块
Content Review Workflow Main Controller

整合所有审核组件，提供完整的内容审核工作流。
"""

import os
import sys
import json
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# 确保可以导入同级模块
sys.path.insert(0, str(Path(__file__).parent))

from quality_checker import QualityChecker
from review_tracker import ReviewTracker, ReviewStatus
from manual_review import ManualReviewWorkflow, ReviewDecision
from report_generator import ReviewReportGenerator


class ContentReviewWorkflow:
    """内容审核工作流主控类"""
    
    def __init__(self, config_path: Optional[str] = None):
        """
        初始化审核工作流
        
        Args:
            config_path: 配置文件路径
        """
        self.config = self._load_config(config_path)
        self.checker = QualityChecker()
        self.tracker = ReviewTracker()
        self.manual_workflow = ManualReviewWorkflow(self.tracker, self.checker)
        self.report_generator = ReviewReportGenerator(self.tracker)
        
        # 审核阈值配置
        self.auto_approve_threshold = self.config.get('auto_approve_threshold', 90)
        self.auto_reject_threshold = self.config.get('auto_reject_threshold', 30)
    
    def _load_config(self, config_path: Optional[str]) -> Dict:
        """加载配置文件"""
        if config_path and Path(config_path).exists():
            with open(config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        
        # 默认配置
        default_config_path = Path(__file__).parent / "config.json"
        if default_config_path.exists():
            with open(default_config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        
        return {
            "auto_approve_threshold": 90,
            "auto_reject_threshold": 30,
            "notification_enabled": True,
            "review_levels": {
                "level_1_auto": {"auto": True, "min_score": 80},
                "level_2_semi": {"auto": False, "min_approvers": 1},
                "level_3_manual": {"auto": False, "min_approvers": 2}
            }
        }
    
    def submit_document(self, document_path: str, submitter: str,
                       review_level: str = "level_1_auto") -> Dict[str, Any]:
        """
        提交文档进行审核
        
        Args:
            document_path: 文档路径
            submitter: 提交者
            review_level: 审核级别
            
        Returns:
            Dict: 提交结果
        """
        logger.info(f"提交文档: {document_path}")
        
        # 1. 检查文档是否存在
        if not Path(document_path).exists():
            return {
                "success": False,
                "error": f"文档不存在: {document_path}"
            }
        
        # 2. 创建审核记录
        record = self.tracker.create_record(document_path, submitter, review_level)
        
        # 3. 自动质量检查
        quality_report = self.checker.check_document(document_path)
        
        result = {
            "success": True,
            "document_id": record.document_id,
            "document_path": document_path,
            "quality_score": quality_report.score,
            "status": record.current_status,
            "issues_count": len(quality_report.issues)
        }
        
        # 4. 根据审核级别和质量得分决定后续流程
        level_config = self.config.get('review_levels', {}).get(review_level, {})
        
        if level_config.get('auto', False):
            # 自动审核流程
            result.update(self._auto_review(record.document_id, quality_report))
        else:
            # 人工审核流程
            logger.info(f"进入人工审核流程: {record.document_id}")
            result["next_step"] = "等待人工审核"
            result["review_level"] = review_level
        
        return result
    
    def _auto_review(self, document_id: str, quality_report) -> Dict:
        """
        自动审核流程
        
        Args:
            document_id: 文档ID
            quality_report: 质量报告
            
        Returns:
            Dict: 审核结果
        """
        score = quality_report.score
        error_count = sum(1 for i in quality_report.issues if i.severity.name == "ERROR")
        
        result = {"auto_review": True}
        
        if score >= self.auto_approve_threshold and error_count == 0:
            # 先进入审核中状态
            self.tracker.update_status(
                document_id,
                ReviewStatus.IN_REVIEW,
                reviewer="auto",
                comment=f"自动审核中，质量得分: {score}"
            )
            # 然后批准
            self.tracker.update_status(
                document_id,
                ReviewStatus.APPROVED,
                reviewer="auto",
                comment=f"自动审核通过，质量得分: {score}"
            )
            result["decision"] = "approved"
            result["message"] = "文档已通过自动审核"
            
            # 自动发布
            self.publish_document(document_id)
            
        elif score < self.auto_reject_threshold or error_count > 3:
            # 先进入审核中状态
            self.tracker.update_status(
                document_id,
                ReviewStatus.IN_REVIEW,
                reviewer="auto",
                comment=f"自动审核中，质量得分: {score}, 错误数: {error_count}"
            )
            # 然后拒绝
            self.tracker.update_status(
                document_id,
                ReviewStatus.REJECTED,
                reviewer="auto",
                comment=f"自动审核拒绝，质量得分: {score}, 错误数: {error_count}"
            )
            result["decision"] = "rejected"
            result["message"] = "文档未通过自动审核，需要大幅修改"
            
        else:
            # 进入人工审核
            self.tracker.update_status(
                document_id,
                ReviewStatus.IN_REVIEW,
                reviewer="auto",
                comment=f"自动审核建议人工复核，质量得分: {score}"
            )
            result["decision"] = "needs_manual_review"
            result["message"] = "文档需要人工审核"
        
        return result
    
    def review_document(self, document_id: str, reviewer: str,
                       decision: str, comment: str = "") -> Dict[str, Any]:
        """
        审核文档
        
        Args:
            document_id: 文档ID
            reviewer: 审核员
            decision: 决策 (approve/revise/reject)
            comment: 审核意见
            
        Returns:
            Dict: 审核结果
        """
        logger.info(f"人工审核: {document_id} by {reviewer}")
        
        record = self.tracker.get_record(document_id)
        if not record:
            return {"success": False, "error": "文档不存在"}
        
        # 创建审核决策
        if decision == "approve":
            new_status = ReviewStatus.APPROVED
            approved = True
        elif decision == "revise":
            new_status = ReviewStatus.NEEDS_REVISION
            approved = False
        else:  # reject
            new_status = ReviewStatus.REJECTED
            approved = False
        
        review_decision = ReviewDecision(
            approved=approved,
            reviewer=reviewer,
            timestamp=datetime.now().isoformat(),
            comments=comment
        )
        
        # 提交决策
        success = self.manual_workflow.submit_decision(document_id, review_decision)
        
        if success and new_status == ReviewStatus.APPROVED:
            # 如果通过，自动发布
            self.publish_document(document_id)
        
        return {
            "success": success,
            "document_id": document_id,
            "new_status": new_status.value if success else record.current_status,
            "reviewer": reviewer
        }
    
    def publish_document(self, document_id: str) -> bool:
        """
        发布文档
        
        Args:
            document_id: 文档ID
            
        Returns:
            bool: 是否成功发布
        """
        record = self.tracker.get_record(document_id)
        if not record:
            return False
        
        # 只有已批准的文档才能发布
        if record.current_status != ReviewStatus.APPROVED.value:
            logger.warning(f"文档未批准，无法发布: {document_id}")
            return False
        
        # 更新状态为已发布
        success = self.tracker.update_status(
            document_id,
            ReviewStatus.PUBLISHED,
            comment="文档已发布"
        )
        
        if success:
            logger.info(f"文档已发布: {document_id}")
            # 这里可以添加额外的发布逻辑，如更新索引、通知等
        
        return success
    
    def revise_document(self, document_id: str, submitter: str) -> Dict[str, Any]:
        """
        重新提交修改后的文档
        
        Args:
            document_id: 文档ID
            submitter: 提交者
            
        Returns:
            Dict: 重新提交结果
        """
        record = self.tracker.get_record(document_id)
        if not record:
            return {"success": False, "error": "文档不存在"}
        
        # 只有需要修改或已拒绝的文档才能重新提交
        if record.current_status not in [ReviewStatus.NEEDS_REVISION.value, ReviewStatus.REJECTED.value]:
            return {"success": False, "error": "文档状态不允许重新提交"}
        
        # 更新状态为待审核
        success = self.tracker.update_status(
            document_id,
            ReviewStatus.PENDING,
            comment=f"文档已修改，重新提交 by {submitter}"
        )
        
        if success:
            # 重新执行审核流程
            return self.submit_document(record.document_path, submitter, record.review_level)
        
        return {"success": False, "error": "状态更新失败"}
    
    def get_document_status(self, document_id: str) -> Optional[Dict]:
        """
        获取文档审核状态
        
        Args:
            document_id: 文档ID
            
        Returns:
            Optional[Dict]: 文档状态信息
        """
        record = self.tracker.get_record(document_id)
        if not record:
            return None
        
        # 获取质量报告
        quality = self.checker.check_document(record.document_path)
        
        return {
            "document_id": record.document_id,
            "document_path": record.document_path,
            "current_status": record.current_status,
            "submitter": record.submitter,
            "submit_time": record.submit_time,
            "assigned_reviewer": record.assigned_reviewer,
            "quality_score": quality.score,
            "event_history": [
                {
                    "timestamp": e.timestamp,
                    "status": e.status,
                    "action": e.action,
                    "reviewer": e.reviewer,
                    "comment": e.comment
                }
                for e in record.events
            ]
        }
    
    def get_pending_list(self, reviewer: Optional[str] = None) -> List[Dict]:
        """
        获取待审核列表
        
        Args:
            reviewer: 审核员筛选
            
        Returns:
            List[Dict]: 待审核项目列表
        """
        records = self.tracker.query_records(
            status=ReviewStatus.PENDING,
            reviewer=reviewer
        )
        
        pending = []
        for record in records:
            quality = self.checker.check_document(record.document_path)
            pending.append({
                "document_id": record.document_id,
                "document_path": record.document_path,
                "submitter": record.submitter,
                "submit_time": record.submit_time,
                "quality_score": quality.score,
                "issue_count": len(quality.issues)
            })
        
        return pending
    
    def run_batch_review(self, directory: str, reviewer: str,
                        pattern: str = "*.md") -> Dict[str, Any]:
        """
        批量审核目录中的文档
        
        Args:
            directory: 目录路径
            reviewer: 审核员
            pattern: 文件匹配模式
            
        Returns:
            Dict: 批量审核结果
        """
        import glob
        
        doc_paths = glob.glob(f"{directory}/**/{pattern}", recursive=True)
        
        results = {
            "total": len(doc_paths),
            "submitted": 0,
            "auto_approved": 0,
            "needs_manual": 0,
            "failed": 0,
            "details": []
        }
        
        for doc_path in doc_paths:
            try:
                # 提交文档
                submit_result = self.submit_document(doc_path, "batch_submit")
                
                if submit_result["success"]:
                    results["submitted"] += 1
                    
                    if submit_result.get("auto_review"):
                        if submit_result.get("decision") == "approved":
                            results["auto_approved"] += 1
                        elif submit_result.get("decision") == "needs_manual_review":
                            results["needs_manual"] += 1
                    
                    results["details"].append({
                        "path": doc_path,
                        "document_id": submit_result["document_id"],
                        "status": submit_result["status"],
                        "quality_score": submit_result["quality_score"]
                    })
                else:
                    results["failed"] += 1
                    results["details"].append({
                        "path": doc_path,
                        "error": submit_result.get("error", "未知错误")
                    })
                    
            except Exception as e:
                logger.error(f"处理文档失败 {doc_path}: {e}")
                results["failed"] += 1
        
        return results
    
    def generate_report(self, report_type: str, output_path: str,
                       **kwargs) -> bool:
        """
        生成审核报告
        
        Args:
            report_type: 报告类型 (summary/document/reviewer/trend)
            output_path: 输出路径
            **kwargs: 额外参数
            
        Returns:
            bool: 是否成功生成
        """
        try:
            if report_type == "summary":
                report = self.report_generator.generate_summary_report(
                    kwargs.get('days', 7)
                )
            elif report_type == "document":
                report = self.report_generator.generate_document_report(
                    kwargs.get('document_id')
                )
                if not report:
                    return False
            elif report_type == "reviewer":
                report = self.report_generator.generate_reviewer_report(
                    kwargs.get('reviewer'),
                    kwargs.get('days', 30)
                )
            elif report_type == "trend":
                report = self.report_generator.generate_trend_report(
                    kwargs.get('days', 30)
                )
            else:
                logger.error(f"未知的报告类型: {report_type}")
                return False
            
            # 确定输出格式
            fmt = kwargs.get('format', 'json')
            if fmt == 'html':
                self.report_generator.export_to_html(report, output_path)
            elif fmt == 'md':
                self.report_generator.export_to_markdown(report, output_path)
            else:
                with open(output_path, 'w', encoding='utf-8') as f:
                    json.dump(report, f, ensure_ascii=False, indent=2)
            
            logger.info(f"报告已生成: {output_path}")
            return True
            
        except Exception as e:
            logger.error(f"生成报告失败: {e}")
            return False


def main():
    """命令行入口"""
    parser = argparse.ArgumentParser(
        description='内容审核工作流',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 提交文档
  python review_workflow.py submit docs/test.md --submitter user1
  
  # 审核文档
  python review_workflow.py review <doc_id> --reviewer reviewer1 --decision approve
  
  # 查看待审核列表
  python review_workflow.py pending
  
  # 批量审核
  python review_workflow.py batch docs/ --reviewer reviewer1
  
  # 生成报告
  python review_workflow.py report summary --output report.html --format html
        """
    )
    
    parser.add_argument('--config', '-c', help='配置文件路径')
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 提交文档
    submit_parser = subparsers.add_parser('submit', help='提交文档进行审核')
    submit_parser.add_argument('document_path', help='文档路径')
    submit_parser.add_argument('--submitter', '-s', required=True, help='提交者')
    submit_parser.add_argument('--level', '-l', default='level_1_auto', help='审核级别')
    
    # 审核文档
    review_parser = subparsers.add_parser('review', help='审核文档')
    review_parser.add_argument('document_id', help='文档ID')
    review_parser.add_argument('--reviewer', '-r', required=True, help='审核员')
    review_parser.add_argument('--decision', '-d', required=True,
                              choices=['approve', 'revise', 'reject'], help='审核决策')
    review_parser.add_argument('--comment', '-c', default='', help='审核意见')
    
    # 查看状态
    status_parser = subparsers.add_parser('status', help='查看文档审核状态')
    status_parser.add_argument('document_id', help='文档ID')
    
    # 待审核列表
    pending_parser = subparsers.add_parser('pending', help='查看待审核列表')
    pending_parser.add_argument('--reviewer', '-r', help='审核员筛选')
    
    # 批量审核
    batch_parser = subparsers.add_parser('batch', help='批量审核')
    batch_parser.add_argument('directory', help='文档目录')
    batch_parser.add_argument('--reviewer', '-r', required=True, help='审核员')
    batch_parser.add_argument('--pattern', '-p', default='*.md', help='文件匹配模式')
    
    # 生成报告
    report_parser = subparsers.add_parser('report', help='生成审核报告')
    report_parser.add_argument('report_type', choices=['summary', 'document', 'reviewer', 'trend'],
                              help='报告类型')
    report_parser.add_argument('--output', '-o', required=True, help='输出路径')
    report_parser.add_argument('--format', '-f', choices=['json', 'html', 'md'], default='json',
                              help='输出格式')
    report_parser.add_argument('--days', '-d', type=int, help='统计天数')
    report_parser.add_argument('--reviewer', '-r', help='审核员（用于reviewer报告）')
    report_parser.add_argument('--document-id', help='文档ID（用于document报告）')
    
    # 重新提交
    revise_parser = subparsers.add_parser('revise', help='重新提交修改后的文档')
    revise_parser.add_argument('document_id', help='文档ID')
    revise_parser.add_argument('--submitter', '-s', required=True, help='提交者')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return
    
    workflow = ContentReviewWorkflow(args.config)
    
    if args.command == 'submit':
        result = workflow.submit_document(args.document_path, args.submitter, args.level)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    
    elif args.command == 'review':
        result = workflow.review_document(args.document_id, args.reviewer, args.decision, args.comment)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    
    elif args.command == 'status':
        result = workflow.get_document_status(args.document_id)
        if result:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        else:
            print("文档不存在")
    
    elif args.command == 'pending':
        result = workflow.get_pending_list(args.reviewer)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    
    elif args.command == 'batch':
        result = workflow.run_batch_review(args.directory, args.reviewer, args.pattern)
        print(json.dumps(result, ensure_ascii=False, indent=2))
    
    elif args.command == 'report':
        kwargs = {'format': args.format}
        if args.days:
            kwargs['days'] = args.days
        if args.reviewer:
            kwargs['reviewer'] = args.reviewer
        if args.document_id:
            kwargs['document_id'] = args.document_id
        
        success = workflow.generate_report(args.report_type, args.output, **kwargs)
        print(f"报告生成{'成功' if success else '失败'}")
    
    elif args.command == 'revise':
        result = workflow.revise_document(args.document_id, args.submitter)
        print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
