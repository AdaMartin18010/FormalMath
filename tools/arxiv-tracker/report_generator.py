"""
报告生成器模块

生成arXiv前沿跟踪的各类报告
"""

import json
import os
import logging
from typing import List, Dict, Optional
from datetime import datetime, timedelta
from pathlib import Path
import yaml

from arxiv_client import ArxivPaper
from relevance_scorer import RelevanceScore
from update_suggester import UpdateSuggestion, UpdateSuggester

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ReportGenerator:
    """报告生成器"""
    
    def __init__(self, config_path: str = "config.yaml"):
        """
        初始化报告生成器
        
        Args:
            config_path: 配置文件路径
        """
        with open(config_path, 'r', encoding='utf-8') as f:
            self.config = yaml.safe_load(f)
        
        self.report_config = self.config.get('report', {})
        self.storage_config = self.config.get('storage', {})
        
        # 确保输出目录存在
        self.report_dir = Path(self.storage_config.get('report_dir', './reports'))
        self.report_dir.mkdir(parents=True, exist_ok=True)
        
        # 跟踪的分类
        self.tracking_categories = {
            cat['id']: cat for cat in self.config.get('tracking_categories', [])
        }
    
    def generate_weekly_report(
        self,
        papers_by_category: Dict[str, List[tuple]],
        week_start: Optional[datetime] = None,
        output_format: str = "markdown"
    ) -> str:
        """
        生成周度报告
        
        Args:
            papers_by_category: {分类: [(论文, 评分), ...]}
            week_start: 周开始日期
            output_format: 输出格式 (markdown, json, html)
            
        Returns:
            报告文件路径
        """
        if week_start is None:
            week_start = datetime.now() - timedelta(days=7)
        
        week_end = week_start + timedelta(days=6)
        week_str = week_start.strftime("%Y-W%W")
        
        logger.info(f"生成周度报告: {week_str}")
        
        # 生成报告内容
        if output_format == "json":
            return self._generate_json_report(
                papers_by_category, week_start, week_end, week_str
            )
        elif output_format == "html":
            return self._generate_html_report(
                papers_by_category, week_start, week_end, week_str
            )
        else:
            return self._generate_markdown_report(
                papers_by_category, week_start, week_end, week_str
            )
    
    def _generate_markdown_report(
        self,
        papers_by_category: Dict[str, List[tuple]],
        week_start: datetime,
        week_end: datetime,
        week_str: str
    ) -> str:
        """生成Markdown格式报告"""
        lines = []
        
        # 报告标题
        lines.append("# FormalMath arXiv前沿跟踪周度报告")
        lines.append("")
        lines.append(f"**报告周期:** {week_start.strftime('%Y年%m月%d日')} - {week_end.strftime('%Y年%m月%d日')}")
        lines.append(f"**生成时间:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append("")
        
        # 执行摘要
        lines.append("## 📊 执行摘要")
        lines.append("")
        
        total_papers = sum(len(papers) for papers in papers_by_category.values())
        high_relevance = sum(
            1 for papers in papers_by_category.values()
            for _, s in papers if s.overall_score >= 0.7
        )
        medium_relevance = sum(
            1 for papers in papers_by_category.values()
            for _, s in papers if 0.4 <= s.overall_score < 0.7
        )
        
        lines.append(f"- **总论文数:** {total_papers}")
        lines.append(f"- **高相关性论文:** {high_relevance}")
        lines.append(f"- **中等相关性论文:** {medium_relevance}")
        lines.append(f"- **覆盖领域:** {len(papers_by_category)} 个")
        lines.append("")
        
        # 按分类统计
        lines.append("## 📚 按领域统计")
        lines.append("")
        lines.append("| 领域 | 英文名称 | 论文数 | 高相关 | 中相关 |")
        lines.append("|------|----------|--------|--------|--------|")
        
        for cat_id, cat_config in self.tracking_categories.items():
            papers = papers_by_category.get(cat_id, [])
            high = sum(1 for _, s in papers if s.overall_score >= 0.7)
            medium = sum(1 for _, s in papers if 0.4 <= s.overall_score < 0.7)
            
            lines.append(
                f"| {cat_config.get('name_zh', cat_id)} | "
                f"{cat_config.get('name', cat_id)} | "
                f"{len(papers)} | {high} | {medium} |"
            )
        
        lines.append("")
        
        # 高相关性论文
        lines.append("## 🔥 高相关性论文")
        lines.append("")
        
        all_high = []
        for cat_id, papers in papers_by_category.items():
            for paper, score in papers:
                if score.overall_score >= 0.7:
                    all_high.append((cat_id, paper, score))
        
        all_high.sort(key=lambda x: x[2].overall_score, reverse=True)
        
        for i, (cat_id, paper, score) in enumerate(all_high[:20], 1):
            cat_config = self.tracking_categories.get(cat_id, {})
            
            lines.append(f"### {i}. {paper.title}")
            lines.append("")
            lines.append(f"**作者:** {', '.join(paper.authors[:3])}{' et al.' if len(paper.authors) > 3 else ''}")
            lines.append(f"**领域:** {cat_config.get('name_zh', cat_id)} ({cat_id})")
            lines.append(f"**arXiv ID:** [{paper.arxiv_id}]({paper.abs_url})")
            lines.append(f"**相关性分数:** {score.overall_score:.2f}")
            lines.append(f"**发布日期:** {paper.published.strftime('%Y-%m-%d') if paper.published else 'N/A'}")
            lines.append("")
            
            # 摘要
            abstract = paper.abstract[:300] + "..." if len(paper.abstract) > 300 else paper.abstract
            lines.append(f"**摘要:** {abstract}")
            lines.append("")
            
            # 匹配详情
            if score.matched_keywords:
                lines.append(f"**匹配关键词:** {', '.join(list(score.matched_keywords.keys())[:5])}")
            if score.matched_concepts:
                concepts = [c.get('concept', '') for c in score.matched_concepts[:3]]
                lines.append(f"**相关概念:** {', '.join(concepts)}")
            lines.append("")
            lines.append("---")
            lines.append("")
        
        # 更新建议
        lines.append("## 💡 知识库更新建议")
        lines.append("")
        
        suggester = UpdateSuggester()
        all_papers = []
        for papers in papers_by_category.values():
            all_papers.extend(papers)
        
        suggestions = suggester.generate_suggestions(all_papers)
        
        for s in suggestions[:15]:
            lines.append(f"### [{s.priority.upper()}] {s.title}")
            lines.append("")
            lines.append(f"**类型:** {UpdateSuggester.SUGGESTION_TYPES.get(s.type, s.type)}")
            lines.append(f"**描述:** {s.description}")
            lines.append(f"**置信度:** {s.confidence:.2f}")
            if s.target_concept:
                lines.append(f"**目标概念:** {s.target_concept}")
            lines.append(f"**相关论文数:** {len(s.related_papers)}")
            lines.append("")
        
        # 热门话题
        lines.append("## 📈 热门话题")
        lines.append("")
        
        trending = suggester.identify_trending_topics(all_papers, top_n=10)
        for topic in trending:
            lines.append(f"- **{topic.topic}** - 出现 {topic.frequency} 次")
        
        lines.append("")
        
        # 报告结尾
        lines.append("---")
        lines.append("")
        lines.append("*本报告由 FormalMath arXiv前沿跟踪系统自动生成*")
        lines.append(f"*报告ID: arxiv-report-{week_str}*")
        
        # 保存报告
        content = "\n".join(lines)
        filename = f"weekly-report-{week_str}.md"
        filepath = self.report_dir / filename
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        logger.info(f"Markdown报告已保存: {filepath}")
        return str(filepath)
    
    def _generate_json_report(
        self,
        papers_by_category: Dict[str, List[tuple]],
        week_start: datetime,
        week_end: datetime,
        week_str: str
    ) -> str:
        """生成JSON格式报告"""
        report_data = {
            "report_type": "weekly",
            "week": week_str,
            "period": {
                "start": week_start.isoformat(),
                "end": week_end.isoformat()
            },
            "generated_at": datetime.now().isoformat(),
            "summary": {},
            "categories": {},
            "papers": []
        }
        
        # 汇总统计
        total = sum(len(papers) for papers in papers_by_category.values())
        high = sum(
            1 for papers in papers_by_category.values()
            for _, s in papers if s.overall_score >= 0.7
        )
        medium = sum(
            1 for papers in papers_by_category.values()
            for _, s in papers if 0.4 <= s.overall_score < 0.7
        )
        
        report_data["summary"] = {
            "total_papers": total,
            "high_relevance": high,
            "medium_relevance": medium,
            "categories_count": len(papers_by_category)
        }
        
        # 按分类数据
        for cat_id, papers in papers_by_category.items():
            cat_config = self.tracking_categories.get(cat_id, {})
            
            report_data["categories"][cat_id] = {
                "name": cat_config.get('name', cat_id),
                "name_zh": cat_config.get('name_zh', ''),
                "total": len(papers),
                "papers": [
                    {
                        "arxiv_id": p.arxiv_id,
                        "title": p.title,
                        "authors": p.authors,
                        "published": p.published.isoformat() if p.published else None,
                        "score": s.overall_score,
                        "keywords": list(s.matched_keywords.keys())[:5]
                    }
                    for p, s in papers
                ]
            }
        
        # 保存
        filename = f"weekly-report-{week_str}.json"
        filepath = self.report_dir / filename
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, ensure_ascii=False, indent=2)
        
        logger.info(f"JSON报告已保存: {filepath}")
        return str(filepath)
    
    def _generate_html_report(
        self,
        papers_by_category: Dict[str, List[tuple]],
        week_start: datetime,
        week_end: datetime,
        week_str: str
    ) -> str:
        """生成HTML格式报告"""
        # 简化的HTML模板
        html_parts = []
        
        html_parts.append("""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath arXiv前沿跟踪周度报告</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; max-width: 1200px; margin: 0 auto; padding: 20px; line-height: 1.6; }
        h1 { color: #2c3e50; border-bottom: 3px solid #3498db; padding-bottom: 10px; }
        h2 { color: #34495e; margin-top: 30px; }
        h3 { color: #2980b9; }
        .summary { background: #ecf0f1; padding: 15px; border-radius: 5px; margin: 20px 0; }
        .paper { background: #f8f9fa; padding: 15px; margin: 15px 0; border-left: 4px solid #3498db; }
        .high-score { border-left-color: #e74c3c; }
        .medium-score { border-left-color: #f39c12; }
        .meta { color: #7f8c8d; font-size: 0.9em; }
        .score { font-weight: bold; color: #e74c3c; }
        table { width: 100%; border-collapse: collapse; margin: 20px 0; }
        th, td { padding: 10px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background: #34495e; color: white; }
        .tag { display: inline-block; padding: 2px 8px; background: #3498db; color: white; border-radius: 3px; font-size: 0.85em; margin: 2px; }
    </style>
</head>
<body>
""")
        
        html_parts.append(f"""
    <h1>📚 FormalMath arXiv前沿跟踪周度报告</h1>
    <div class="summary">
        <p><strong>报告周期:</strong> {week_start.strftime('%Y年%m月%d日')} - {week_end.strftime('%Y年%m月%d日')}</p>
        <p><strong>生成时间:</strong> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
    </div>
""")
        
        # 统计
        total = sum(len(papers) for papers in papers_by_category.values())
        html_parts.append(f"""
    <h2>📊 统计概览</h2>
    <div class="summary">
        <p>总论文数: <strong>{total}</strong></p>
        <p>覆盖领域: <strong>{len(papers_by_category)}</strong> 个</p>
    </div>
""")
        
        # 论文列表
        html_parts.append("<h2>🔥 高相关性论文</h2>")
        
        all_papers = []
        for cat_id, papers in papers_by_category.items():
            for paper, score in papers:
                all_papers.append((cat_id, paper, score))
        
        all_papers.sort(key=lambda x: x[2].overall_score, reverse=True)
        
        for cat_id, paper, score in all_papers[:15]:
            cat_config = self.tracking_categories.get(cat_id, {})
            score_class = 'high-score' if score.overall_score >= 0.7 else 'medium-score'
            
            html_parts.append(f"""
    <div class="paper {score_class}">
        <h3>{paper.title}</h3>
        <p class="meta">作者: {', '.join(paper.authors[:3])}{' et al.' if len(paper.authors) > 3 else ''}</p>
        <p class="meta">领域: {cat_config.get('name_zh', cat_id)} | 分数: <span class="score">{score.overall_score:.2f}</span></p>
        <p>{paper.abstract[:250]}...</p>
        <p><a href="{paper.abs_url}" target="_blank">查看arXiv</a></p>
    </div>
""")
        
        html_parts.append("""
</body>
</html>
""")
        
        # 保存
        content = "\n".join(html_parts)
        filename = f"weekly-report-{week_str}.html"
        filepath = self.report_dir / filename
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        logger.info(f"HTML报告已保存: {filepath}")
        return str(filepath)
    
    def generate_suggestions_report(
        self,
        suggestions: List[UpdateSuggestion],
        output_format: str = "markdown"
    ) -> str:
        """
        生成更新建议报告
        
        Args:
            suggestions: 建议列表
            output_format: 输出格式
            
        Returns:
            报告文件路径
        """
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        if output_format == "json":
            filename = f"suggestions-{timestamp}.json"
            filepath = self.report_dir / filename
            
            data = {
                "generated_at": datetime.now().isoformat(),
                "suggestions_count": len(suggestions),
                "suggestions": [
                    {
                        "id": s.suggestion_id,
                        "type": s.type,
                        "type_name": UpdateSuggester.SUGGESTION_TYPES.get(s.type, s.type),
                        "title": s.title,
                        "description": s.description,
                        "priority": s.priority,
                        "confidence": s.confidence,
                        "target_concept": s.target_concept,
                        "target_branch": s.target_branch,
                        "related_papers": s.related_papers
                    }
                    for s in suggestions
                ]
            }
            
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            
        else:
            filename = f"suggestions-{timestamp}.md"
            filepath = self.report_dir / filename
            
            lines = [
                "# FormalMath 知识库更新建议",
                "",
                f"**生成时间:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                f"**建议总数:** {len(suggestions)}",
                "",
                "## 建议列表",
                ""
            ]
            
            for i, s in enumerate(suggestions, 1):
                lines.extend([
                    f"### {i}. [{s.priority.upper()}] {s.title}",
                    "",
                    f"- **类型:** {UpdateSuggester.SUGGESTION_TYPES.get(s.type, s.type)}",
                    f"- **描述:** {s.description}",
                    f"- **置信度:** {s.confidence:.2f}",
                    f"- **相关论文:** {len(s.related_papers)} 篇",
                    ""
                ])
                
                if s.related_papers:
                    lines.append("**相关论文:**")
                    for p in s.related_papers[:3]:
                        lines.append(f"- {p.get('title', 'N/A')}")
                    lines.append("")
                
                lines.append("---")
                lines.append("")
            
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write("\n".join(lines))
        
        logger.info(f"建议报告已保存: {filepath}")
        return str(filepath)


# 便捷函数
def generate_report(
    papers_by_category: Dict[str, List[tuple]],
    report_type: str = "weekly",
    output_format: str = "markdown",
    config_path: str = "config.yaml"
) -> str:
    """
    生成报告
    
    Args:
        papers_by_category: 按分类的论文数据
        report_type: 报告类型
        output_format: 输出格式
        config_path: 配置文件路径
        
    Returns:
        报告文件路径
    """
    generator = ReportGenerator(config_path)
    
    if report_type == "weekly":
        return generator.generate_weekly_report(papers_by_category, output_format=output_format)
    else:
        raise ValueError(f"不支持的报告类型: {report_type}")


if __name__ == "__main__":
    # 测试代码
    print("报告生成器测试模式")
    print(f"报告目录: {Path('./reports').absolute()}")
