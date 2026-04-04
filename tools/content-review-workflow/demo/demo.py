#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
内容审核工作流演示脚本

展示如何使用内容审核工作流系统。
"""

import sys
from pathlib import Path

# 添加父目录到路径
sys.path.insert(0, str(Path(__file__).parent.parent))

from review_workflow import ContentReviewWorkflow
import json


def print_separator(title):
    """打印分隔线"""
    print(f"\n{'='*60}")
    print(f" {title}")
    print(f"{'='*60}\n")


def main():
    print_separator("内容审核工作流演示")
    
    # 初始化工作流
    workflow = ContentReviewWorkflow()
    print("✓ 工作流系统初始化完成")
    
    # 1. 提交文档
    print_separator("步骤 1: 提交文档")
    doc_path = str(Path(__file__).parent / "example_document.md")
    
    result = workflow.submit_document(doc_path, "demo_user", "level_1_auto")
    print(f"提交结果:")
    print(json.dumps(result, indent=2, ensure_ascii=False))
    
    if not result.get("success"):
        print("提交失败，退出演示")
        return
    
    doc_id = result["document_id"]
    print(f"\n✓ 文档已提交，ID: {doc_id}")
    
    # 2. 查看文档状态
    print_separator("步骤 2: 查看审核状态")
    status = workflow.get_document_status(doc_id)
    print(f"当前状态: {status['current_status']}")
    print(f"质量得分: {status['quality_score']}")
    print(f"问题数量: {len(status.get('event_history', []))}")
    
    # 3. 如果是待审核状态，执行人工审核
    if status['current_status'] == 'in_review':
        print_separator("步骤 3: 人工审核")
        
        review_result = workflow.review_document(
            doc_id,
            "demo_reviewer",
            "approve",
            "内容完整，格式规范，通过审核"
        )
        print(f"审核结果:")
        print(json.dumps(review_result, indent=2, ensure_ascii=False))
        
        # 4. 再次查看状态
        print_separator("步骤 4: 查看最终状态")
        final_status = workflow.get_document_status(doc_id)
        print(f"最终状态: {final_status['current_status']}")
        print(f"\n完整事件历史:")
        for event in final_status['event_history']:
            print(f"  - [{event['timestamp']}] {event['action']}: {event['status']}")
    
    # 5. 生成报告
    print_separator("步骤 5: 生成审核报告")
    
    # 文档报告
    doc_report = workflow.report_generator.generate_document_report(doc_id)
    print(f"✓ 文档报告生成完成")
    print(f"  - 审核事件数: {doc_report['review']['event_count']}")
    print(f"  - 总审核时间: {doc_report['review']['total_review_time']}")
    
    # 汇总报告
    summary_report = workflow.report_generator.generate_summary_report(days=7)
    print(f"\n✓ 汇总报告生成完成")
    print(f"  - 总文档数: {summary_report['overview']['total_documents']}")
    print(f"  - 待审核: {summary_report['overview']['pending_count']}")
    print(f"  - 已发布: {summary_report['overview']['published_count']}")
    
    # 6. 查看待审核列表
    print_separator("步骤 6: 查看待审核列表")
    pending = workflow.get_pending_list()
    print(f"当前待审核文档数: {len(pending)}")
    for item in pending:
        print(f"  - {item['document_path']} (得分: {item['quality_score']})")
    
    print_separator("演示完成")
    print("""
演示展示了以下内容：
1. 文档提交和自动质量检查
2. 审核状态追踪
3. 人工审核流程
4. 报告生成
5. 待审核列表查询

更多信息请查看 README.md 和 WORKFLOW.md
""")


if __name__ == "__main__":
    main()
