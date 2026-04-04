#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 质量评估报告生成器
Quality Assessment Report Generator for FormalMath

功能：生成多种格式的质量评估报告
作者：FormalMath AI
版本：1.0.0
"""

import json
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any
from quality_assessor import QualityAssessmentResult


class ReportGenerator:
    """报告生成器"""
    
    def __init__(self, output_dir: str = "output"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
    def _get_css_styles(self) -> str:
        """获取CSS样式（使用字符串拼接避免format冲突）"""
        styles = """
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6; color: #333; background: #f5f7fa; padding: 20px;
        }
        .container { max-width: 1400px; margin: 0 auto; }
        .header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white; padding: 40px; border-radius: 12px;
            margin-bottom: 30px; box-shadow: 0 4px 6px rgba(0,0,0,0.1);
        }
        .header h1 { font-size: 2.5em; margin-bottom: 10px; }
        .header .meta { opacity: 0.9; font-size: 1.1em; }
        .summary-cards {
            display: grid; grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px; margin-bottom: 30px;
        }
        .summary-card {
            background: white; padding: 25px; border-radius: 12px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.05); transition: transform 0.2s;
        }
        .summary-card:hover { transform: translateY(-2px); box-shadow: 0 4px 8px rgba(0,0,0,0.1); }
        .summary-card .value { font-size: 2.5em; font-weight: bold; color: #667eea; margin-bottom: 5px; }
        .summary-card .label { color: #666; font-size: 0.95em; }
        .chart-section {
            background: white; padding: 30px; border-radius: 12px;
            margin-bottom: 30px; box-shadow: 0 2px 4px rgba(0,0,0,0.05);
        }
        .chart-section h2 { margin-bottom: 20px; color: #333; }
        .quality-distribution { display: flex; gap: 10px; flex-wrap: wrap; }
        .quality-badge { padding: 10px 20px; border-radius: 20px; font-weight: 500; color: white; }
        .quality-EXCELLENT { background: #10b981; }
        .quality-GOOD { background: #3b82f6; }
        .quality-ACCEPTABLE { background: #f59e0b; }
        .quality-NEEDS_IMPROVEMENT { background: #f97316; }
        .quality-POOR { background: #ef4444; }
        .files-section {
            background: white; padding: 30px; border-radius: 12px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.05);
        }
        .file-card {
            border: 1px solid #e5e7eb; border-radius: 8px; padding: 20px;
            margin-bottom: 15px; transition: all 0.2s;
        }
        .file-card:hover { border-color: #667eea; box-shadow: 0 2px 8px rgba(102,126,234,0.1); }
        .file-header {
            display: flex; justify-content: space-between; align-items: center;
            margin-bottom: 15px;
        }
        .file-name { font-weight: 600; color: #1f2937; font-size: 1.1em; }
        .score-badge { padding: 5px 15px; border-radius: 15px; font-weight: 600; font-size: 0.9em; }
        .metrics-grid {
            display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px; margin-bottom: 15px;
        }
        .metric-item { background: #f9fafb; padding: 12px; border-radius: 6px; }
        .metric-name { font-size: 0.85em; color: #6b7280; margin-bottom: 4px; }
        .metric-value { font-weight: 600; color: #1f2937; }
        .progress-bar { height: 6px; background: #e5e7eb; border-radius: 3px; margin-top: 8px; overflow: hidden; }
        .progress-fill { height: 100%; border-radius: 3px; transition: width 0.3s ease; }
        .progress-fill.high { background: #10b981; }
        .progress-fill.medium { background: #f59e0b; }
        .progress-fill.low { background: #ef4444; }
        .issues-section { margin-top: 15px; padding-top: 15px; border-top: 1px solid #e5e7eb; }
        .issue-item { display: flex; align-items: flex-start; gap: 10px; padding: 8px 0; }
        .issue-severity {
            padding: 2px 8px; border-radius: 4px; font-size: 0.75em;
            font-weight: 600; text-transform: uppercase;
        }
        .severity-high { background: #fee2e2; color: #dc2626; }
        .severity-medium { background: #fef3c7; color: #d97706; }
        .severity-low { background: #dbeafe; color: #2563eb; }
        .issue-content { flex: 1; }
        .issue-description { color: #374151; margin-bottom: 2px; }
        .issue-suggestion { color: #6b7280; font-size: 0.9em; }
        .recommendations {
            margin-top: 15px; padding: 15px; background: #f0fdf4;
            border-radius: 6px; border-left: 4px solid #10b981;
        }
        .recommendations h4 { color: #166534; margin-bottom: 10px; }
        .recommendations ul { list-style: none; padding-left: 0; }
        .recommendations li { padding: 5px 0; padding-left: 20px; position: relative; color: #15803d; }
        .recommendations li::before { content: "→"; position: absolute; left: 0; color: #22c55e; }
        .footer { text-align: center; padding: 30px; color: #6b7280; margin-top: 30px; }
        @media print { body { background: white; } .file-card { break-inside: avoid; } }
        """
        return styles
    
    def generate_html_report(self, results: List[QualityAssessmentResult], 
                            summary: Dict[str, Any], 
                            output_file: str = "quality_report.html") -> str:
        """生成HTML格式的质量报告"""
        
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        total_files = summary.get('total_files', len(results))
        avg_score = summary.get('average_score', 0)
        max_score = summary.get('max_score', 0)
        min_score = summary.get('min_score', 0)
        high_priority_issues = summary.get('high_priority_issues', 0)
        
        # 生成质量分布HTML
        quality_dist_html = ""
        for level, count in summary.get('quality_distribution', {}).items():
            quality_dist_html += f'<span class="quality-badge quality-{level}">{level}: {count}</span>'
        
        # 生成文件详情HTML
        file_details_html = ""
        for result in results:
            file_details_html += self._generate_file_card(result)
        
        # 构建HTML内容（使用字符串拼接而非format）
        html_parts = [
            '<!DOCTYPE html>',
            '<html lang="zh-CN">',
            '<head>',
            '    <meta charset="UTF-8">',
            '    <meta name="viewport" content="width=device-width, initial-scale=1.0">',
            '    <title>FormalMath 内容质量评估报告</title>',
            '    <style>',
            self._get_css_styles(),
            '    </style>',
            '</head>',
            '<body>',
            '    <div class="container">',
            '        <div class="header">',
            '            <h1>📊 FormalMath 内容质量评估报告</h1>',
            f'            <div class="meta"><p>生成时间: {timestamp}</p><p>评估文件数: {total_files}</p></div>',
            '        </div>',
            '        <div class="summary-cards">',
            f'            <div class="summary-card"><div class="value">{avg_score:.1f}</div><div class="label">平均质量分</div></div>',
            f'            <div class="summary-card"><div class="value">{max_score:.1f}</div><div class="label">最高分</div></div>',
            f'            <div class="summary-card"><div class="value">{min_score:.1f}</div><div class="label">最低分</div></div>',
            f'            <div class="summary-card"><div class="value">{high_priority_issues}</div><div class="label">高优先级问题</div></div>',
            '        </div>',
            '        <div class="chart-section">',
            '            <h2>📈 质量分布</h2>',
            f'            <div class="quality-distribution">{quality_dist_html}</div>',
            '        </div>',
            '        <div class="files-section">',
            '            <h2>📁 详细评估结果</h2>',
            file_details_html,
            '        </div>',
            '        <div class="footer">',
            '            <p>由 FormalMath 内容质量评估系统自动生成</p>',
            '            <p>FormalMath Content Quality Assessment System v1.0</p>',
            '        </div>',
            '    </div>',
            '</body>',
            '</html>'
        ]
        
        html_content = '\n'.join(html_parts)
        
        output_path = self.output_dir / output_file
        output_path.write_text(html_content, encoding='utf-8')
        return str(output_path)
    
    def _generate_file_card(self, result: QualityAssessmentResult) -> str:
        """生成单个文件评估卡片"""
        
        # 确定分数颜色
        if result.overall_score >= 80:
            score_class = "high"
            score_color = "#10b981"
        elif result.overall_score >= 60:
            score_class = "medium"
            score_color = "#f59e0b"
        else:
            score_class = "low"
            score_color = "#ef4444"
        
        card_parts = [
            '<div class="file-card">',
            '    <div class="file-header">',
            f'        <span class="file-name">{result.file_name}</span>',
            f'        <span class="score-badge" style="background: {score_color}20; color: {score_color};">{result.overall_score:.1f}分</span>',
            '    </div>',
            '    <div class="metrics-grid">',
        ]
        
        # 添加各维度指标
        metrics = [
            ('完整性', result.completeness.overall_score),
            ('准确性', result.accuracy.overall_score),
            ('可读性', result.readability.overall_score),
            ('国际化', result.internationalization.overall_score),
            ('学习效果', result.learning_effect.overall_score),
        ]
        
        for name, score in metrics:
            card_parts.append(f'''
                <div class="metric-item">
                    <div class="metric-name">{name}</div>
                    <div class="metric-value">{score:.1f}</div>
                    <div class="progress-bar">
                        <div class="progress-fill {score_class}" style="width: {score}%"></div>
                    </div>
                </div>''')
        
        card_parts.append('    </div>')
        
        # 添加问题列表
        if result.issues:
            card_parts.append('    <div class="issues-section"><h4>发现的问题</h4>')
            for issue in result.issues[:5]:  # 最多显示5个问题
                severity_class = f"severity-{issue['severity']}"
                card_parts.append(f'''
                <div class="issue-item">
                    <span class="issue-severity {severity_class}">{issue['severity']}</span>
                    <div class="issue-content">
                        <div class="issue-description">{issue['description']}</div>
                        <div class="issue-suggestion">建议: {issue['suggestion']}</div>
                    </div>
                </div>''')
            card_parts.append('    </div>')
        
        # 添加建议
        if result.recommendations:
            card_parts.append('    <div class="recommendations"><h4>改进建议</h4><ul>')
            for rec in result.recommendations[:3]:  # 最多显示3条建议
                card_parts.append(f'        <li>{rec}</li>')
            card_parts.append('    </ul></div>')
        
        card_parts.append('</div>')
        
        return '\n'.join(card_parts)
    
    def generate_markdown_report(self, results: List[QualityAssessmentResult],
                                 summary: Dict[str, Any],
                                 output_file: str = "quality_report.md") -> str:
        """生成Markdown格式的质量报告"""
        
        lines = [
            "# FormalMath 内容质量评估报告",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**评估文件数**: {summary.get('total_files', len(results))}",
            "",
            "## 📊 评估摘要",
            "",
            "| 指标 | 数值 |",
            "|------|------|",
            f"| 平均质量分 | {summary.get('average_score', 0):.2f} |",
            f"| 最高分 | {summary.get('max_score', 0):.2f} |",
            f"| 最低分 | {summary.get('min_score', 0):.2f} |",
            f"| 高优先级问题 | {summary.get('high_priority_issues', 0)} |",
            "",
            "### 质量等级分布",
            "",
        ]
        
        for level, count in summary.get('quality_distribution', {}).items():
            lines.append(f"- **{level}**: {count} 个文件")
        
        lines.extend(["", "## 📁 详细评估结果", ""])
        
        for result in results:
            # 质量等级徽章
            badge_color = {
                'EXCELLENT': '🟢',
                'GOOD': '🔵',
                'ACCEPTABLE': '🟡',
                'NEEDS_IMPROVEMENT': '🟠',
                'POOR': '🔴'
            }.get(result.quality_level, '⚪')
            
            lines.extend([
                f"### {badge_color} {result.file_name}",
                "",
                f"**总体评分**: {result.overall_score:.2f}/100",
                f"**质量等级**: {result.quality_level}",
                "",
                "#### 各维度评分",
                "",
                "| 维度 | 得分 | 权重 | 加权得分 |",
                "|------|------|------|----------|",
                f"| 完整性 | {result.completeness.overall_score:.2f} | 25% | {result.completeness.overall_score * 0.25:.2f} |",
                f"| 准确性 | {result.accuracy.overall_score:.2f} | 25% | {result.accuracy.overall_score * 0.25:.2f} |",
                f"| 可读性 | {result.readability.overall_score:.2f} | 20% | {result.readability.overall_score * 0.20:.2f} |",
                f"| 国际化 | {result.internationalization.overall_score:.2f} | 15% | {result.internationalization.overall_score * 0.15:.2f} |",
                f"| 学习效果 | {result.learning_effect.overall_score:.2f} | 15% | {result.learning_effect.overall_score * 0.15:.2f} |",
                "",
            ])
            
            # 完整性详情
            lines.extend([
                "#### 完整性详情",
                "",
                f"- 概念定义: {'✅' if result.completeness.has_concept_definition else '❌'}",
                f"- 定理证明: {'✅' if result.completeness.has_theorem_proof else '❌'}",
                f"- 示例: {'✅' if result.completeness.has_examples else '❌'}",
                f"- 参考文献: {'✅' if result.completeness.has_references else '❌'}",
                f"- MSC编码: {'✅' if result.completeness.has_msc_code else '❌'}",
                f"- 定理数量: {result.completeness.theorem_count}",
                f"- 证明数量: {result.completeness.proof_count}",
                f"- 示例数量: {result.completeness.example_count}",
                "",
            ])
            
            # 学习效果预测
            lines.extend([
                "#### 学习效果预测",
                "",
                f"- **预估难度**: {result.learning_effect.estimated_difficulty}",
                f"- **预估学习时长**: {result.learning_effect.estimated_study_time} 分钟",
                f"- **掌握概率**: {result.learning_effect.mastery_probability:.1%}",
                f"- **前置知识清晰度**: {result.learning_effect.prerequisite_clarity:.2f}",
                f"- **练习多样性**: {result.learning_effect.exercise_diversity:.2f}",
                "",
            ])
            
            # 问题列表
            if result.issues:
                lines.extend([
                    "#### 发现的问题",
                    "",
                ])
                for issue in result.issues:
                    severity_icon = {"high": "🔴", "medium": "🟡", "low": "🔵"}.get(issue['severity'], "⚪")
                    lines.append(f"- {severity_icon} **{issue['description']}**")
                    lines.append(f"  - 建议: {issue['suggestion']}")
                lines.append("")
            
            # 改进建议
            if result.recommendations:
                lines.extend([
                    "#### 改进建议",
                    "",
                ])
                for rec in result.recommendations:
                    lines.append(f"- 💡 {rec}")
                lines.append("")
            
            lines.append("---")
            lines.append("")
        
        output_path = self.output_dir / output_file
        output_path.write_text('\n'.join(lines), encoding='utf-8')
        return str(output_path)
    
    def generate_json_report(self, results: List[QualityAssessmentResult],
                            summary: Dict[str, Any],
                            output_file: str = "quality_report.json") -> str:
        """生成JSON格式的质量报告"""
        
        from dataclasses import asdict
        
        report_data = {
            'metadata': {
                'generated_at': datetime.now().isoformat(),
                'version': '1.0.0',
                'total_files': summary.get('total_files', len(results))
            },
            'summary': summary,
            'results': [asdict(r) for r in results]
        }
        
        output_path = self.output_dir / output_file
        output_path.write_text(
            json.dumps(report_data, ensure_ascii=False, indent=2),
            encoding='utf-8'
        )
        return str(output_path)
    
    def generate_csv_report(self, results: List[QualityAssessmentResult],
                           output_file: str = "quality_report.csv") -> str:
        """生成CSV格式的质量报告"""
        
        import csv
        
        output_path = self.output_dir / output_file
        
        with open(output_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            
            # 写入表头
            writer.writerow([
                '文件名', '文件路径', '总体评分', '质量等级',
                '完整性', '准确性', '可读性', '国际化', '学习效果',
                '定理数', '证明数', '示例数',
                '预估难度', '预估学习时长(分钟)', '掌握概率',
                '问题数量', '建议数量'
            ])
            
            # 写入数据
            for r in results:
                writer.writerow([
                    r.file_name,
                    r.file_path,
                    f"{r.overall_score:.2f}",
                    r.quality_level,
                    f"{r.completeness.overall_score:.2f}",
                    f"{r.accuracy.overall_score:.2f}",
                    f"{r.readability.overall_score:.2f}",
                    f"{r.internationalization.overall_score:.2f}",
                    f"{r.learning_effect.overall_score:.2f}",
                    r.completeness.theorem_count,
                    r.completeness.proof_count,
                    r.completeness.example_count,
                    r.learning_effect.estimated_difficulty,
                    r.learning_effect.estimated_study_time,
                    f"{r.learning_effect.mastery_probability:.2%}",
                    len(r.issues),
                    len(r.recommendations)
                ])
        
        return str(output_path)


def main():
    """主函数 - 示例用法"""
    from quality_assessor import ContentQualityAssessor
    
    # 评估示例
    assessor = ContentQualityAssessor()
    results = assessor.assess_directory("../../docs/01-基础数学/集合论")
    summary = assessor.get_summary()
    
    # 生成报告
    generator = ReportGenerator()
    
    html_path = generator.generate_html_report(results, summary)
    print(f"HTML报告已生成: {html_path}")
    
    md_path = generator.generate_markdown_report(results, summary)
    print(f"Markdown报告已生成: {md_path}")
    
    json_path = generator.generate_json_report(results, summary)
    print(f"JSON报告已生成: {json_path}")
    
    csv_path = generator.generate_csv_report(results)
    print(f"CSV报告已生成: {csv_path}")


if __name__ == '__main__':
    main()
