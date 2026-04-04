#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量评估系统 - 演示脚本
Demonstration Script for Content Quality Assessment System

运行此脚本演示系统的各项功能
"""

import sys
from pathlib import Path

# 添加父目录到路径
sys.path.insert(0, str(Path(__file__).parent))

from quality_assessor import ContentQualityAssessor
from report_generator import ReportGenerator
from issue_extractor import IssueExtractor


def print_section(title):
    """打印章节标题"""
    print("\n" + "="*60)
    print(f"  {title}")
    print("="*60 + "\n")


def demo_single_file_assessment():
    """演示单个文件评估"""
    print_section("1. 单个文件评估演示")
    
    assessor = ContentQualityAssessor()
    
    # 评估样本文档
    sample_file = Path(__file__).parent / "demo" / "sample_document.md"
    
    if not sample_file.exists():
        print(f"❌ 样本文档不存在: {sample_file}")
        return
    
    print(f"📄 正在评估: {sample_file.name}")
    result = assessor.assess_file(str(sample_file))
    
    # 打印结果
    print(f"\n📊 评估结果:")
    print(f"  文件名: {result.file_name}")
    print(f"  总体评分: {result.overall_score:.2f}/100")
    print(f"  质量等级: {result.quality_level}")
    
    print(f"\n📋 各维度评分:")
    print(f"  完整性: {result.completeness.overall_score:.2f}")
    print(f"    - 概念定义: {'✅' if result.completeness.has_concept_definition else '❌'}")
    print(f"    - 定理证明: {'✅' if result.completeness.has_theorem_proof else '❌'}")
    print(f"    - 示例: {'✅' if result.completeness.has_examples else '❌'}")
    print(f"    - 参考文献: {'✅' if result.completeness.has_references else '❌'}")
    print(f"    - MSC编码: {'✅' if result.completeness.has_msc_code else '❌'}")
    print(f"    - 定理数: {result.completeness.theorem_count}")
    print(f"    - 证明数: {result.completeness.proof_count}")
    print(f"    - 示例数: {result.completeness.example_count}")
    
    print(f"  准确性: {result.accuracy.overall_score:.2f}")
    print(f"    - 公式语法错误: {result.accuracy.math_formula_syntax_errors}")
    print(f"    - 引用错误: {result.accuracy.citation_errors}")
    print(f"    - 失效链接: {len(result.accuracy.broken_links)}")
    
    print(f"  可读性: {result.readability.overall_score:.2f}")
    print(f"    - 平均句长: {result.readability.avg_sentence_length:.1f} 字")
    print(f"    - 段落长度: {result.readability.avg_paragraph_length:.1f} 句")
    print(f"    - 复杂词比例: {result.readability.complex_word_ratio:.1%}")
    
    print(f"  国际化: {result.internationalization.overall_score:.2f}")
    print(f"    - 英文术语: {'✅' if result.internationalization.has_english_terms else '❌'}")
    print(f"    - 术语一致性: {result.internationalization.term_consistency_score:.2f}")
    
    print(f"  学习效果: {result.learning_effect.overall_score:.2f}")
    print(f"    - 预估难度: {result.learning_effect.estimated_difficulty}")
    print(f"    - 预估时长: {result.learning_effect.estimated_study_time} 分钟")
    print(f"    - 掌握概率: {result.learning_effect.mastery_probability:.1%}")
    
    if result.issues:
        print(f"\n⚠️  发现 {len(result.issues)} 个问题:")
        for issue in result.issues:
            icon = {'high': '🔴', 'medium': '🟡', 'low': '🔵'}.get(issue['severity'], '⚪')
            print(f"  {icon} [{issue['severity'].upper()}] {issue['description']}")
    else:
        print("\n✅ 未发现问题")
    
    if result.recommendations:
        print(f"\n💡 改进建议:")
        for rec in result.recommendations:
            print(f"  - {rec}")
    
    return result


def demo_batch_assessment():
    """演示批量评估"""
    print_section("2. 批量评估演示")
    
    # 评估docs目录下的一个子目录
    target_dir = Path(__file__).parent.parent.parent / "docs" / "01-基础数学" / "集合论"
    
    if not target_dir.exists():
        print(f"⚠️  目标目录不存在，跳过批量评估演示")
        print(f"   期望路径: {target_dir}")
        return None
    
    print(f"📁 正在评估目录: {target_dir}")
    
    assessor = ContentQualityAssessor()
    results = assessor.assess_directory(str(target_dir))
    
    summary = assessor.get_summary()
    
    print(f"\n📊 批量评估摘要:")
    print(f"  评估文件数: {summary['total_files']}")
    print(f"  平均分数: {summary['average_score']:.2f}")
    print(f"  最高分数: {summary['max_score']:.2f}")
    print(f"  最低分数: {summary['min_score']:.2f}")
    print(f"  高优先级问题: {summary['high_priority_issues']}")
    
    print(f"\n📈 质量分布:")
    for level, count in summary['quality_distribution'].items():
        icon = {
            'EXCELLENT': '🟢', 'GOOD': '🔵', 'ACCEPTABLE': '🟡',
            'NEEDS_IMPROVEMENT': '🟠', 'POOR': '🔴'
        }.get(level, '⚪')
        print(f"  {icon} {level}: {count}")
    
    return results, summary


def demo_report_generation(results, summary):
    """演示报告生成"""
    print_section("3. 报告生成演示")
    
    if not results:
        print("⚠️  没有评估结果，跳过报告生成")
        return
    
    output_dir = Path(__file__).parent / "demo" / "output"
    output_dir.mkdir(parents=True, exist_ok=True)
    
    generator = ReportGenerator(output_dir=str(output_dir))
    
    # 生成HTML报告
    print("📝 生成HTML报告...")
    html_path = generator.generate_html_report(results, summary, "demo_report.html")
    print(f"   ✅ 已保存: {html_path}")
    
    # 生成Markdown报告
    print("📝 生成Markdown报告...")
    md_path = generator.generate_markdown_report(results, summary, "demo_report.md")
    print(f"   ✅ 已保存: {md_path}")
    
    # 生成JSON报告
    print("📝 生成JSON报告...")
    json_path = generator.generate_json_report(results, summary, "demo_report.json")
    print(f"   ✅ 已保存: {json_path}")
    
    # 生成CSV报告
    print("📝 生成CSV报告...")
    csv_path = generator.generate_csv_report(results, "demo_report.csv")
    print(f"   ✅ 已保存: {csv_path}")
    
    print(f"\n📂 所有报告已保存至: {output_dir}")


def demo_issue_extraction(results):
    """演示问题提取"""
    print_section("4. 问题提取演示")
    
    if not results:
        print("⚠️  没有评估结果，跳过问题提取")
        return
    
    extractor = IssueExtractor()
    
    print("🔍 正在从评估结果中提取问题...")
    for result in results:
        extractor.extract_from_result(result.__dict__)
    
    print(f"\n📋 提取到 {len(extractor.issues)} 个问题")
    
    # 分析模式
    patterns = extractor.analyze_patterns()
    
    print(f"\n📊 严重程度分布:")
    for severity, count in patterns['severity_distribution'].items():
        icon = {'high': '🔴', 'medium': '🟡', 'low': '🔵'}.get(severity, '⚪')
        print(f"  {icon} {severity}: {count}")
    
    print(f"\n📊 类型分布:")
    for issue_type, count in patterns['type_distribution'].items():
        print(f"  - {issue_type}: {count}")
    
    # 生成行动计划
    action_plan = extractor.generate_action_plan()
    
    print(f"\n📅 行动计划:")
    for phase_name, stats in action_plan['phase_stats'].items():
        print(f"  {phase_name}:")
        print(f"    - 问题数: {stats['issue_count']}")
        print(f"    - 预估工时: {stats['estimated_hours']} 小时")
        print(f"    - 高严重问题: {stats['high_severity_count']}")
    
    print(f"\n⏱️  预估总工时: {action_plan['total_estimated_hours']} 小时")
    
    # 生成问题清单报告
    output_dir = Path(__file__).parent / "demo" / "output"
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print("\n📝 生成问题清单报告...")
    report_path = extractor.generate_issue_report(str(output_dir / "demo_issues.md"))
    print(f"   ✅ 已保存: {report_path}")
    
    json_path = extractor.export_issues_json(str(output_dir / "demo_issues.json"))
    print(f"   ✅ 已保存: {json_path}")


def main():
    """主函数"""
    print("""
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     FormalMath 内容质量评估系统 - 功能演示                   ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
    """)
    
    # 1. 单个文件评估
    single_result = demo_single_file_assessment()
    
    # 2. 批量评估
    batch_results = None
    summary = None
    
    target_dir = Path(__file__).parent.parent.parent / "docs" / "01-基础数学" / "集合论"
    if target_dir.exists():
        batch_results, summary = demo_batch_assessment()
    else:
        print("\n⚠️  未找到项目文档目录，使用单文件结果进行后续演示")
        batch_results = [single_result] if single_result else []
        from quality_assessor import ContentQualityAssessor
        assessor = ContentQualityAssessor()
        summary = assessor.get_summary() if hasattr(assessor, 'results') else {
            'total_files': 1,
            'average_score': single_result.overall_score if single_result else 0,
            'max_score': single_result.overall_score if single_result else 0,
            'min_score': single_result.overall_score if single_result else 0,
            'quality_distribution': {single_result.quality_level: 1} if single_result else {},
            'high_priority_issues': len(single_result.issues) if single_result else 0
        }
    
    # 3. 报告生成
    demo_report_generation(batch_results or ([single_result] if single_result else []), summary)
    
    # 4. 问题提取
    demo_issue_extraction(batch_results or ([single_result] if single_result else []))
    
    print("""
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     演示完成！                                               ║
║     请查看 demo/output/ 目录下的生成文件                     ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
    """)


if __name__ == '__main__':
    main()
