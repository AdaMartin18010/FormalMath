#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量评估系统 - 主入口
Main Entry Point for Content Quality Assessment System

功能：提供统一的命令行接口，整合所有评估功能
作者：FormalMath AI
版本：1.0.0
"""

import argparse
import sys
import os
from pathlib import Path
from datetime import datetime

# 确保可以导入本地模块
sys.path.insert(0, str(Path(__file__).parent))

from quality_assessor import ContentQualityAssessor
from report_generator import ReportGenerator
from issue_extractor import IssueExtractor, BatchIssueProcessor
from config import config, get_config


def print_banner():
    """打印程序横幅"""
    banner = """
╔══════════════════════════════════════════════════════════════╗
║                                                              ║
║     FormalMath 内容质量评估系统                              ║
║     Content Quality Assessment System                        ║
║                                                              ║
║     版本: 1.0.0                                              ║
║     作者: FormalMath AI                                      ║
║                                                              ║
╚══════════════════════════════════════════════════════════════╝
    """
    print(banner)


def cmd_assess(args):
    """执行评估命令"""
    print(f"🔍 正在评估: {args.path}")
    
    assessor = ContentQualityAssressor(project_root=args.project_root)
    
    if os.path.isfile(args.path):
        result = assessor.assess_file(args.path)
        results = [result]
        print(f"✅ 完成单个文件评估: {result.file_name}")
    else:
        pattern = args.pattern if args.pattern else "**/*.md"
        results = assessor.assess_directory(args.path, pattern)
        print(f"✅ 完成目录评估: {len(results)} 个文件")
    
    summary = assessor.get_summary()
    
    # 显示摘要
    print("\n📊 评估摘要:")
    print(f"  文件总数: {summary.get('total_files', len(results))}")
    print(f"  平均分数: {summary.get('average_score', 0):.2f}")
    print(f"  最高分数: {summary.get('max_score', 0):.2f}")
    print(f"  最低分数: {summary.get('min_score', 0):.2f}")
    
    if 'quality_distribution' in summary:
        print("\n  质量分布:")
        for level, count in sorted(summary['quality_distribution'].items()):
            icon = {
                'EXCELLENT': '🟢', 'GOOD': '🔵', 'ACCEPTABLE': '🟡',
                'NEEDS_IMPROVEMENT': '🟠', 'POOR': '🔴'
            }.get(level, '⚪')
            print(f"    {icon} {level}: {count}")
    
    # 保存结果
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    if args.format in ['json', 'all']:
        import json
        from dataclasses import asdict
        output_file = output_dir / f"assessment_{timestamp}.json"
        data = {
            'metadata': {
                'generated_at': datetime.now().isoformat(),
                'path': args.path,
                'total_files': len(results)
            },
            'summary': summary,
            'results': [asdict(r) for r in results]
        }
        output_file.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')
        print(f"\n💾 JSON报告已保存: {output_file}")
    
    if args.format in ['html', 'all']:
        generator = ReportGenerator(output_dir=str(output_dir))
        output_file = generator.generate_html_report(results, summary, f"assessment_{timestamp}.html")
        print(f"💾 HTML报告已保存: {output_file}")
    
    if args.format in ['markdown', 'md', 'all']:
        generator = ReportGenerator(output_dir=str(output_dir))
        output_file = generator.generate_markdown_report(results, summary, f"assessment_{timestamp}.md")
        print(f"💾 Markdown报告已保存: {output_file}")
    
    if args.format in ['csv', 'all']:
        generator = ReportGenerator(output_dir=str(output_dir))
        output_file = generator.generate_csv_report(results, f"assessment_{timestamp}.csv")
        print(f"💾 CSV报告已保存: {output_file}")
    
    # 如果指定了提取问题
    if args.extract_issues:
        print("\n🔍 正在提取问题...")
        extractor = IssueExtractor()
        for result in results:
            extractor.extract_from_result(result.__dict__)
        
        issue_file = output_dir / f"issues_{timestamp}.md"
        extractor.generate_issue_report(str(issue_file))
        print(f"💾 问题清单已保存: {issue_file}")
        
        json_file = output_dir / f"issues_{timestamp}.json"
        extractor.export_issues_json(str(json_file))
        print(f"💾 问题JSON已保存: {json_file}")
    
    # 返回退出码
    if summary.get('high_priority_issues', 0) > 0 and args.fail_on_issues:
        return 1
    return 0


def cmd_extract(args):
    """执行问题提取命令"""
    print(f"🔍 正在从评估结果中提取问题: {args.input}")
    
    extractor = IssueExtractor()
    processor = BatchIssueProcessor(extractor)
    
    try:
        processor.process_assessment_results(args.input)
    except FileNotFoundError as e:
        print(f"❌ 错误: {e}")
        return 1
    
    # 生成问题清单
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    if args.format in ['markdown', 'md', 'all']:
        report_file = output_dir / f"issue_report_{timestamp}.md"
        extractor.generate_issue_report(str(report_file))
        print(f"💾 Markdown问题报告已保存: {report_file}")
    
    if args.format in ['json', 'all']:
        json_file = output_dir / f"issues_{timestamp}.json"
        extractor.export_issues_json(str(json_file))
        print(f"💾 JSON问题清单已保存: {json_file}")
    
    # 打印统计
    patterns = extractor.analyze_patterns()
    print("\n📊 问题统计:")
    print(f"  总问题数: {len(extractor.issues)}")
    print(f"  影响文件: {patterns['file_patterns']['total_affected_files']}")
    print(f"  高优先级: {patterns['severity_distribution'].get('high', 0)}")
    
    action_plan = extractor.generate_action_plan()
    print(f"\n⏱️  预估修复工时: {action_plan['total_estimated_hours']} 小时")
    
    return 0


def cmd_config(args):
    """执行配置查看/修改命令"""
    if args.show:
        print("=== 当前配置 ===\n")
        print("评估维度权重:")
        for dim, weight in config.WEIGHTS.items():
            print(f"  {dim}: {weight*100:.0f}%")
        
        print("\n质量等级阈值:")
        for level, threshold in sorted(config.QUALITY_THRESHOLDS.items(), key=lambda x: -x[1]):
            print(f"  {level}: ≥{threshold}")
        
        print(f"\n数学术语数量: {len(config.MATH_TERMS)}")
        print(f"符号变体数量: {len(config.NOTATION_VARIANTS)}")
        
    return 0


def main():
    """主函数"""
    print_banner()
    
    parser = argparse.ArgumentParser(
        description='FormalMath 内容质量评估系统',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例用法:
  # 评估单个文件
  python main.py assess docs/example.md

  # 评估目录并生成所有格式报告
  python main.py assess docs/ -f all --extract-issues

  # 从已有结果提取问题
  python main.py extract results.json -o reports/

  # 查看配置
  python main.py config --show
        """
    )
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # assess 命令
    assess_parser = subparsers.add_parser('assess', help='评估文档质量')
    assess_parser.add_argument('path', help='要评估的文件或目录路径')
    assess_parser.add_argument('-o', '--output-dir', default='output',
                               help='输出目录 (默认: output)')
    assess_parser.add_argument('-f', '--format', default='json',
                               choices=['json', 'html', 'markdown', 'csv', 'all'],
                               help='输出格式 (默认: json)')
    assess_parser.add_argument('-p', '--pattern', default='**/*.md',
                               help='文件匹配模式 (默认: **/*.md)')
    assess_parser.add_argument('--project-root', default='.',
                               help='项目根目录 (默认: 当前目录)')
    assess_parser.add_argument('--extract-issues', action='store_true',
                               help='同时提取问题清单')
    assess_parser.add_argument('--fail-on-issues', action='store_true',
                               help='发现问题时返回非零退出码')
    
    # extract 命令
    extract_parser = subparsers.add_parser('extract', help='从评估结果提取问题')
    extract_parser.add_argument('input', help='评估结果JSON文件')
    extract_parser.add_argument('-o', '--output-dir', default='output',
                                help='输出目录 (默认: output)')
    extract_parser.add_argument('-f', '--format', default='markdown',
                                choices=['markdown', 'json', 'all'],
                                help='输出格式 (默认: markdown)')
    
    # config 命令
    config_parser = subparsers.add_parser('config', help='查看或修改配置')
    config_parser.add_argument('--show', action='store_true',
                               help='显示当前配置')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return 1
    
    # 执行对应命令
    commands = {
        'assess': cmd_assess,
        'extract': cmd_extract,
        'config': cmd_config,
    }
    
    if args.command in commands:
        return commands[args.command](args)
    else:
        parser.print_help()
        return 1


if __name__ == '__main__':
    sys.exit(main())
