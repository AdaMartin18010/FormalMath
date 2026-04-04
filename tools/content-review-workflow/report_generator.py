#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
审核报告生成器
Review Report Generator

生成各种格式的审核报告和统计可视化。
"""

import json
import os
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime, timedelta
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ReviewReportGenerator:
    """审核报告生成器"""
    
    def __init__(self, tracker=None):
        """
        初始化报告生成器
        
        Args:
            tracker: 审核追踪器实例
        """
        if tracker is None:
            from review_tracker import ReviewTracker
            tracker = ReviewTracker()
        self.tracker = tracker
    
    def generate_summary_report(self, days: int = 7) -> Dict[str, Any]:
        """
        生成汇总报告
        
        Args:
            days: 统计天数
            
        Returns:
            Dict: 汇总报告数据
        """
        stats = self.tracker.get_statistics()
        
        # 计算趋势
        now = datetime.now()
        cutoff_date = now - timedelta(days=days)
        
        recent_records = []
        for record in self.tracker.records.values():
            submit_time = datetime.fromisoformat(record.submit_time)
            if submit_time >= cutoff_date:
                recent_records.append(record)
        
        # 计算审核效率
        completed_reviews = [
            r for r in recent_records 
            if r.current_status in ['approved', 'published', 'rejected']
        ]
        
        avg_review_time = 0
        if completed_reviews:
            total_hours = 0
            for r in completed_reviews:
                submit = datetime.fromisoformat(r.submit_time)
                # 找最后一个状态变更事件
                if r.events:
                    last_event = r.events[-1]
                    complete = datetime.fromisoformat(last_event.timestamp)
                    total_hours += (complete - submit).total_seconds() / 3600
            avg_review_time = total_hours / len(completed_reviews)
        
        report = {
            "report_type": "summary",
            "generated_at": now.isoformat(),
            "period_days": days,
            "overview": {
                "total_documents": stats["total"],
                "pending_count": stats["by_status"].get("pending", 0),
                "in_review_count": stats["by_status"].get("in_review", 0),
                "approved_count": stats["by_status"].get("approved", 0),
                "published_count": stats["by_status"].get("published", 0),
                "rejected_count": stats["by_status"].get("rejected", 0)
            },
            "activity": {
                "new_submissions": len(recent_records),
                "completed_reviews": len(completed_reviews),
                "average_review_time_hours": round(avg_review_time, 2)
            },
            "backlog": {
                "aging_items": len(stats.get("pending_aging", [])),
                "oldest_pending_hours": stats["pending_aging"][0]["wait_hours"] if stats.get("pending_aging") else 0
            },
            "reviewer_workload": stats["by_reviewer"]
        }
        
        return report
    
    def generate_document_report(self, document_id: str) -> Optional[Dict]:
        """
        生成单个文档的审核报告
        
        Args:
            document_id: 文档ID
            
        Returns:
            Optional[Dict]: 文档审核报告
        """
        record = self.tracker.get_record(document_id)
        if not record:
            return None
        
        # 计算审核时间线
        timeline = []
        for event in record.events:
            timeline.append({
                "time": event.timestamp,
                "status": event.status,
                "action": event.action,
                "reviewer": event.reviewer,
                "comment": event.comment
            })
        
        # 计算总审核时间
        total_review_time = "N/A"
        if len(record.events) >= 2:
            start = datetime.fromisoformat(record.events[0].timestamp)
            end = datetime.fromisoformat(record.events[-1].timestamp)
            total_review_time = f"{(end - start).total_seconds() / 3600:.2f} 小时"
        
        report = {
            "report_type": "document",
            "generated_at": datetime.now().isoformat(),
            "document": {
                "id": record.document_id,
                "path": record.document_path,
                "submitter": record.submitter,
                "submit_time": record.submit_time
            },
            "review": {
                "current_status": record.current_status,
                "assigned_reviewer": record.assigned_reviewer,
                "review_level": record.review_level,
                "total_review_time": total_review_time,
                "event_count": len(record.events)
            },
            "timeline": timeline
        }
        
        return report
    
    def generate_reviewer_report(self, reviewer: str, days: int = 30) -> Dict:
        """
        生成审核员工作报告
        
        Args:
            reviewer: 审核员
            days: 统计天数
            
        Returns:
            Dict: 审核员报告
        """
        now = datetime.now()
        cutoff_date = now - timedelta(days=days)
        
        # 收集该审核员相关的记录
        reviewer_records = []
        for record in self.tracker.records.values():
            if record.assigned_reviewer == reviewer:
                reviewer_records.append(record)
        
        # 统计审核活动
        approved_count = 0
        rejected_count = 0
        revision_count = 0
        total_review_time = 0
        
        for record in reviewer_records:
            if record.current_status == 'approved':
                approved_count += 1
            elif record.current_status == 'rejected':
                rejected_count += 1
            elif record.current_status == 'needs_revision':
                revision_count += 1
        
        report = {
            "report_type": "reviewer",
            "generated_at": now.isoformat(),
            "period_days": days,
            "reviewer": reviewer,
            "statistics": {
                "total_assigned": len(reviewer_records),
                "approved": approved_count,
                "rejected": rejected_count,
                "needs_revision": revision_count,
                "pending": len([r for r in reviewer_records if r.current_status == 'in_review'])
            },
            "approval_rate": round(
                approved_count / (approved_count + rejected_count) * 100, 2
            ) if (approved_count + rejected_count) > 0 else 0,
            "recent_activity": []
        }
        
        # 添加最近活动
        for record in sorted(reviewer_records, key=lambda r: r.submit_time, reverse=True)[:10]:
            report["recent_activity"].append({
                "document_id": record.document_id,
                "document_path": record.document_path,
                "current_status": record.current_status,
                "submit_time": record.submit_time
            })
        
        return report
    
    def generate_trend_report(self, days: int = 30) -> Dict:
        """
        生成趋势报告
        
        Args:
            days: 统计天数
            
        Returns:
            Dict: 趋势报告
        """
        now = datetime.now()
        daily_stats = []
        
        for i in range(days):
            date = now - timedelta(days=i)
            date_str = date.strftime("%Y-%m-%d")
            
            # 统计当天的提交和审核
            submissions = 0
            completions = 0
            
            for record in self.tracker.records.values():
                submit_date = datetime.fromisoformat(record.submit_time).strftime("%Y-%m-%d")
                if submit_date == date_str:
                    submissions += 1
                
                # 检查当天是否有完成的审核
                for event in record.events:
                    event_date = datetime.fromisoformat(event.timestamp).strftime("%Y-%m-%d")
                    if event_date == date_str and event.status in ['approved', 'rejected']:
                        completions += 1
                        break
            
            daily_stats.append({
                "date": date_str,
                "submissions": submissions,
                "completions": completions
            })
        
        daily_stats.reverse()  # 按时间正序
        
        return {
            "report_type": "trend",
            "generated_at": now.isoformat(),
            "period_days": days,
            "daily_statistics": daily_stats,
            "totals": {
                "total_submissions": sum(d["submissions"] for d in daily_stats),
                "total_completions": sum(d["completions"] for d in daily_stats)
            }
        }
    
    def export_to_html(self, report: Dict, output_path: str):
        """
        导出报告为HTML格式
        
        Args:
            report: 报告数据
            output_path: 输出路径
        """
        html_content = self._generate_html(report)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        logger.info(f"HTML报告已导出: {output_path}")
    
    def export_to_markdown(self, report: Dict, output_path: str):
        """
        导出报告为Markdown格式
        
        Args:
            report: 报告数据
            output_path: 输出路径
        """
        md_content = self._generate_markdown(report)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(md_content)
        
        logger.info(f"Markdown报告已导出: {output_path}")
    
    def _generate_html(self, report: Dict) -> str:
        """生成HTML报告"""
        report_type = report.get("report_type", "unknown")
        
        html_parts = [
            "<!DOCTYPE html>",
            "<html lang=\"zh-CN\">",
            "<head>",
            "  <meta charset=\"UTF-8\">",
            "  <title>审核报告</title>",
            "  <style>",
            "    body { font-family: Arial, sans-serif; margin: 40px; background: #f5f5f5; }",
            "    .container { max-width: 1200px; margin: 0 auto; background: white; padding: 30px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }",
            "    h1 { color: #333; border-bottom: 2px solid #4CAF50; padding-bottom: 10px; }",
            "    h2 { color: #555; margin-top: 30px; }",
            "    .metric { display: inline-block; margin: 10px 20px 10px 0; padding: 15px 20px; background: #f9f9f9; border-radius: 4px; }",
            "    .metric-value { font-size: 24px; font-weight: bold; color: #4CAF50; }",
            "    .metric-label { color: #666; font-size: 14px; }",
            "    table { width: 100%; border-collapse: collapse; margin: 20px 0; }",
            "    th, td { padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }",
            "    th { background: #4CAF50; color: white; }",
            "    tr:hover { background: #f5f5f5; }",
            "    .status-pass { color: #4CAF50; }",
            "    .status-fail { color: #f44336; }",
            "    .status-pending { color: #ff9800; }",
            "  </style>",
            "</head>",
            "<body>",
            "  <div class=\"container\">",
            f"    <h1>审核报告 - {report_type.upper()}</h1>",
            f"    <p>生成时间: {report.get('generated_at', 'N/A')}</p>"
        ]
        
        if report_type == "summary":
            # 汇总报告HTML
            overview = report.get("overview", {})
            html_parts.extend([
                "    <h2>概览</h2>",
                "    <div class=\"metric\">",
                f"      <div class=\"metric-value\">{overview.get('total_documents', 0)}</div>",
                "      <div class=\"metric-label\">总文档数</div>",
                "    </div>",
                "    <div class=\"metric\">",
                f"      <div class=\"metric-value\">{overview.get('published_count', 0)}</div>",
                "      <div class=\"metric-label\">已发布</div>",
                "    </div>",
                "    <div class=\"metric\">",
                f"      <div class=\"metric-value\">{overview.get('pending_count', 0)}</div>",
                "      <div class=\"metric-label\">待审核</div>",
                "    </div>"
            ])
        
        elif report_type == "document":
            # 文档报告HTML
            doc = report.get("document", {})
            review = report.get("review", {})
            html_parts.extend([
                "    <h2>文档信息</h2>",
                f"    <p><strong>文档路径:</strong> {doc.get('path', 'N/A')}</p>",
                f"    <p><strong>提交者:</strong> {doc.get('submitter', 'N/A')}</p>",
                f"    <p><strong>当前状态:</strong> <span class=\"status-{review.get('current_status', 'unknown')}\">{review.get('current_status', 'N/A')}</span></p>",
                f"    <p><strong>审核员:</strong> {review.get('assigned_reviewer', '未分配')}</p>",
                "    <h2>审核时间线</h2>",
                "    <table>",
                "      <tr><th>时间</th><th>状态</th><th>操作</th><th>审核员</th></tr>"
            ])
            for event in report.get("timeline", []):
                html_parts.append(
                    f"      <tr><td>{event['time']}</td><td>{event['status']}</td>"
                    f"<td>{event['action']}</td><td>{event.get('reviewer', '-')}</td></tr>"
                )
            html_parts.append("    </table>")
        
        html_parts.extend([
            "  </div>",
            "</body>",
            "</html>"
        ])
        
        return '\n'.join(html_parts)
    
    def _generate_markdown(self, report: Dict) -> str:
        """生成Markdown报告"""
        report_type = report.get("report_type", "unknown")
        lines = [f"# 审核报告 - {report_type.upper()}\n"]
        lines.append(f"**生成时间**: {report.get('generated_at', 'N/A')}\n")
        
        if report_type == "summary":
            overview = report.get("overview", {})
            lines.append("## 概览\n")
            lines.append(f"- 总文档数: {overview.get('total_documents', 0)}\n")
            lines.append(f"- 已发布: {overview.get('published_count', 0)}\n")
            lines.append(f"- 待审核: {overview.get('pending_count', 0)}\n")
            lines.append(f"- 审核中: {overview.get('in_review_count', 0)}\n")
            lines.append(f"- 已拒绝: {overview.get('rejected_count', 0)}\n")
            
            activity = report.get("activity", {})
            lines.append("\n## 活动统计\n")
            lines.append(f"- 新提交: {activity.get('new_submissions', 0)}\n")
            lines.append(f"- 完成审核: {activity.get('completed_reviews', 0)}\n")
            lines.append(f"- 平均审核时间: {activity.get('average_review_time_hours', 0)} 小时\n")
        
        elif report_type == "document":
            doc = report.get("document", {})
            review = report.get("review", {})
            lines.append("## 文档信息\n")
            lines.append(f"- 文档路径: {doc.get('path', 'N/A')}\n")
            lines.append(f"- 提交者: {doc.get('submitter', 'N/A')}\n")
            lines.append(f"- 当前状态: {review.get('current_status', 'N/A')}\n")
            lines.append(f"- 审核员: {review.get('assigned_reviewer', '未分配')}\n")
            lines.append(f"- 总审核时间: {review.get('total_review_time', 'N/A')}\n")
            
            lines.append("\n## 审核时间线\n")
            lines.append("| 时间 | 状态 | 操作 | 审核员 |\n")
            lines.append("|------|------|------|--------|\n")
            for event in report.get("timeline", []):
                lines.append(f"| {event['time']} | {event['status']} | {event['action']} | {event.get('reviewer', '-')} |\n")
        
        return ''.join(lines)


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(description='审核报告生成器')
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 汇总报告
    summary_parser = subparsers.add_parser('summary', help='生成汇总报告')
    summary_parser.add_argument('--days', '-d', type=int, default=7, help='统计天数')
    summary_parser.add_argument('--output', '-o', required=True, help='输出路径')
    summary_parser.add_argument('--format', '-f', choices=['json', 'html', 'md'], default='json', help='输出格式')
    
    # 文档报告
    doc_parser = subparsers.add_parser('document', help='生成文档报告')
    doc_parser.add_argument('document_id', help='文档ID')
    doc_parser.add_argument('--output', '-o', required=True, help='输出路径')
    doc_parser.add_argument('--format', '-f', choices=['json', 'html', 'md'], default='json', help='输出格式')
    
    # 审核员报告
    reviewer_parser = subparsers.add_parser('reviewer', help='生成审核员报告')
    reviewer_parser.add_argument('reviewer', help='审核员名称')
    reviewer_parser.add_argument('--days', '-d', type=int, default=30, help='统计天数')
    reviewer_parser.add_argument('--output', '-o', required=True, help='输出路径')
    reviewer_parser.add_argument('--format', '-f', choices=['json', 'html', 'md'], default='json', help='输出格式')
    
    # 趋势报告
    trend_parser = subparsers.add_parser('trend', help='生成趋势报告')
    trend_parser.add_argument('--days', '-d', type=int, default=30, help='统计天数')
    trend_parser.add_argument('--output', '-o', required=True, help='输出路径')
    trend_parser.add_argument('--format', '-f', choices=['json', 'html', 'md'], default='json', help='输出格式')
    
    args = parser.parse_args()
    
    generator = ReviewReportGenerator()
    
    if args.command == 'summary':
        report = generator.generate_summary_report(args.days)
    elif args.command == 'document':
        report = generator.generate_document_report(args.document_id)
        if not report:
            print(f"文档未找到: {args.document_id}")
            return
    elif args.command == 'reviewer':
        report = generator.generate_reviewer_report(args.reviewer, args.days)
    elif args.command == 'trend':
        report = generator.generate_trend_report(args.days)
    else:
        parser.print_help()
        return
    
    # 输出报告
    if args.format == 'json':
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
    elif args.format == 'html':
        generator.export_to_html(report, args.output)
    elif args.format == 'md':
        generator.export_to_markdown(report, args.output)
    
    print(f"报告已生成: {args.output}")


if __name__ == "__main__":
    main()
