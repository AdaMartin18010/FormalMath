# -*- coding: utf-8 -*-
"""
report_generator.py - FormalMath 评估系统报告生成器

实现各类评估报告的生成：
- 个人学习报告
- 能力评估报告
- 增值评价报告
- 群体分析报告
- 多格式导出（JSON, Markdown, HTML, PDF）
"""

import uuid
import json
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from enum import Enum
import base64
from io import BytesIO


# =============================================================================
# 枚举和数据类
# =============================================================================

class ReportFormat(str, Enum):
    """报告格式"""
    JSON = "json"
    MARKDOWN = "markdown"
    HTML = "html"
    PDF = "pdf"


@dataclass
class ReportSection:
    """报告章节"""
    title: str
    content: str
    data: Dict[str, Any] = field(default_factory=dict)
    chart_data: Optional[Dict] = None
    
    def to_dict(self) -> dict:
        return {
            "title": self.title,
            "content": self.content,
            "data": self.data,
            "chart_data": self.chart_data
        }


@dataclass
class ChartData:
    """图表数据"""
    chart_type: str  # radar, line, bar, pie
    title: str
    data: Dict[str, Any]
    options: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> dict:
        return {
            "chart_type": self.chart_type,
            "title": self.title,
            "data": self.data,
            "options": self.options
        }


# =============================================================================
# 图表生成器
# =============================================================================

class ChartGenerator:
    """图表数据生成器"""
    
    def create_radar_chart(
        self,
        title: str,
        dimensions: List[str],
        values: List[float],
        max_value: float = 100
    ) -> ChartData:
        """创建雷达图数据"""
        return ChartData(
            chart_type="radar",
            title=title,
            data={
                "indicators": [
                    {"name": dim, "max": max_value} 
                    for dim in dimensions
                ],
                "series": [{
                    "name": "得分",
                    "value": values
                }]
            },
            options={
                "color": ["#5470c6"],
                "radius": "70%"
            }
        )
    
    def create_line_chart(
        self,
        title: str,
        x_axis: List[str],
        series: List[Dict[str, Any]]
    ) -> ChartData:
        """创建折线图数据"""
        return ChartData(
            chart_type="line",
            title=title,
            data={
                "xAxis": {"type": "category", "data": x_axis},
                "series": series
            },
            options={
                "smooth": True,
                "areaStyle": {"opacity": 0.3}
            }
        )
    
    def create_bar_chart(
        self,
        title: str,
        categories: List[str],
        values: List[float],
        horizontal: bool = False
    ) -> ChartData:
        """创建柱状图数据"""
        return ChartData(
            chart_type="bar",
            title=title,
            data={
                "categories": categories,
                "values": values
            },
            options={
                "horizontal": horizontal,
                "color": "#5470c6"
            }
        )
    
    def create_pie_chart(
        self,
        title: str,
        data: List[Dict[str, Any]]
    ) -> ChartData:
        """创建饼图数据"""
        return ChartData(
            chart_type="pie",
            title=title,
            data={"data": data},
            options={
                "radius": ["40%", "70%"]
            }
        )


# =============================================================================
# 报告生成器基类
# =============================================================================

class BaseReportGenerator:
    """报告生成器基类"""
    
    def __init__(self):
        self.chart_generator = ChartGenerator()
    
    def create_section(self, title: str, content: str, data: Dict = None, chart: ChartData = None) -> ReportSection:
        """创建报告章节"""
        return ReportSection(
            title=title,
            content=content,
            data=data or {},
            chart_data=chart.to_dict() if chart else None
        )
    
    def format_score_bar(self, score: float, max_width: int = 20) -> str:
        """格式化分数条"""
        filled = int(score / 100 * max_width)
        empty = max_width - filled
        return f"{'█' * filled}{'░' * empty} {score:.1f}"
    
    def get_level_emoji(self, level: str) -> str:
        """获取等级表情"""
        emojis = {
            "expert": "🏆",
            "advanced": "🥇",
            "proficient": "🥈",
            "developing": "📈",
            "beginner": "🌱"
        }
        return emojis.get(level, "📊")
    
    def get_level_name(self, level: str) -> str:
        """获取等级名称"""
        names = {
            "expert": "专家",
            "advanced": "高级",
            "proficient": "熟练",
            "developing": "发展中",
            "beginner": "初级"
        }
        return names.get(level, "未知")


# =============================================================================
# 个人学习报告生成器
# =============================================================================

class PersonalReportGenerator(BaseReportGenerator):
    """个人学习报告生成器"""
    
    def generate(
        self,
        learner_id: str,
        learner_name: str,
        evaluation_history: List[Dict],
        current_ability: Dict[str, float],
        knowledge_state: Dict[str, float],
        behavior_summary: Dict[str, Any],
        period_days: int = 30
    ) -> Dict[str, Any]:
        """
        生成个人学习报告
        
        Args:
            learner_id: 学习者ID
            learner_name: 学习者姓名
            evaluation_history: 评价历史
            current_ability: 当前能力得分
            knowledge_state: 知识状态
            behavior_summary: 行为摘要
            period_days: 报告周期
        
        Returns:
            报告数据
        """
        sections = []
        charts = []
        
        # 1. 报告摘要
        summary_section = self._create_summary_section(
            learner_name, current_ability, evaluation_history
        )
        sections.append(summary_section)
        
        # 2. 能力分析
        ability_section, ability_chart = self._create_ability_section(current_ability)
        sections.append(ability_section)
        charts.append(ability_chart)
        
        # 3. 知识掌握
        knowledge_section = self._create_knowledge_section(knowledge_state)
        sections.append(knowledge_section)
        
        # 4. 学习趋势
        if len(evaluation_history) >= 2:
            trend_section, trend_chart = self._create_trend_section(evaluation_history)
            sections.append(trend_section)
            charts.append(trend_chart)
        
        # 5. 学习行为
        behavior_section = self._create_behavior_section(behavior_summary)
        sections.append(behavior_section)
        
        # 6. 建议与规划
        suggestion_section = self._create_suggestion_section(
            current_ability, knowledge_state
        )
        sections.append(suggestion_section)
        
        return {
            "report_id": str(uuid.uuid4()),
            "report_type": "personal_learning",
            "learner_id": learner_id,
            "learner_name": learner_name,
            "period_days": period_days,
            "generated_at": datetime.now().isoformat(),
            "sections": [s.to_dict() for s in sections],
            "charts": [c.to_dict() for c in charts],
            "summary": self._generate_overall_summary(current_ability, behavior_summary)
        }
    
    def _create_summary_section(
        self,
        learner_name: str,
        current_ability: Dict[str, float],
        evaluation_history: List[Dict]
    ) -> ReportSection:
        """创建摘要章节"""
        overall = sum(current_ability.values()) / len(current_ability) if current_ability else 0
        
        # 计算变化趋势
        change_text = ""
        if len(evaluation_history) >= 2:
            prev = evaluation_history[-2].get("overall_score", 0)
            curr = evaluation_history[-1].get("overall_score", 0)
            change = curr - prev
            if change > 0:
                change_text = f"📈 较上次提升 {change:.1f} 分"
            elif change < 0:
                change_text = f"📉 较上次下降 {abs(change):.1f} 分"
            else:
                change_text = "➡️ 与上次持平"
        
        content = f"""
## 学习概览

**学习者**: {learner_name}

**综合得分**: {overall:.1f}/100 {change_text}

**评价时间**: {datetime.now().strftime('%Y年%m月%d日')}

**本期学习评价**: {len(evaluation_history)} 次

### 总体评价

你在本报告周期的学习情况{'良好' if overall >= 60 else '需要加强'}，
{self._get_ability_summary(current_ability)}
"""
        
        return self.create_section("学习概览", content.strip(), {"overall_score": overall})
    
    def _create_ability_section(
        self, 
        current_ability: Dict[str, float]
    ) -> Tuple[ReportSection, ChartData]:
        """创建能力分析章节"""
        dimensions = list(current_ability.keys())
        values = list(current_ability.values())
        
        # 生成文字内容
        content = "## 能力维度分析\n\n"
        for dim, score in current_ability.items():
            content += f"- **{dim}**: {self.format_score_bar(score)}\n"
        
        content += f"\n### 强项与弱项\n\n"
        
        strengths = [k for k, v in current_ability.items() if v >= 70]
        weaknesses = [k for k, v in current_ability.items() if v < 60]
        
        if strengths:
            content += f"**✅ 强项**: {', '.join(strengths)}\n\n"
        if weaknesses:
            content += f"**📈 待提升**: {', '.join(weaknesses)}\n\n"
        
        section = self.create_section("能力分析", content)
        chart = self.chart_generator.create_radar_chart(
            "能力雷达图", dimensions, values
        )
        
        return section, chart
    
    def _create_knowledge_section(
        self, 
        knowledge_state: Dict[str, float]
    ) -> ReportSection:
        """创建知识掌握章节"""
        if not knowledge_state:
            return self.create_section("知识掌握", "暂无知识掌握数据。")
        
        mastered = sum(1 for v in knowledge_state.values() if v >= 80)
        developing = sum(1 for v in knowledge_state.values() if 60 <= v < 80)
        beginner = sum(1 for v in knowledge_state.values() if v < 60)
        
        avg_mastery = sum(knowledge_state.values()) / len(knowledge_state)
        
        content = f"""
## 知识掌握情况

- **概念总数**: {len(knowledge_state)}
- **已精通**: {mastered} 个 ({mastered/len(knowledge_state)*100:.1f}%)
- **掌握中**: {developing} 个 ({developing/len(knowledge_state)*100:.1f}%)
- **初学**: {beginner} 个 ({beginner/len(knowledge_state)*100:.1f}%)
- **平均掌握度**: {avg_mastery:.1f}%

### 掌握度详情

| 概念 | 掌握度 | 状态 |
|------|--------|------|
"""
        
        for concept, mastery in sorted(knowledge_state.items(), key=lambda x: -x[1])[:10]:
            status = "精通" if mastery >= 80 else "掌握中" if mastery >= 60 else "初学"
            content += f"| {concept} | {mastery:.1f}% | {status} |\n"
        
        return self.create_section(
            "知识掌握", 
            content.strip(),
            {"mastery_distribution": {"mastered": mastered, "developing": developing, "beginner": beginner}}
        )
    
    def _create_trend_section(
        self, 
        evaluation_history: List[Dict]
    ) -> Tuple[ReportSection, ChartData]:
        """创建趋势章节"""
        dates = [e.get("timestamp", "")[:10] for e in evaluation_history[-10:]]
        scores = [e.get("overall_score", 0) for e in evaluation_history[-10:]]
        
        content = f"""
## 学习趋势

以下是最近{len(dates)}次评估的得分变化：

```
分数
100 |                                                    
 80 |                                                    
 60 |                                                    
 40 |                                                    
 20 |                                                    
  0 |____________________________________________________
         {dates[0] if dates else 'N/A'}               {dates[-1] if dates else 'N/A'}
```

**趋势分析**: 
- 最高分: {max(scores):.1f}
- 最低分: {min(scores):.1f}
- 平均分: {sum(scores)/len(scores):.1f}
"""
        
        section = self.create_section("学习趋势", content)
        
        chart = self.chart_generator.create_line_chart(
            "学习趋势图",
            dates,
            [{"name": "综合得分", "data": scores}]
        )
        
        return section, chart
    
    def _create_behavior_section(
        self, 
        behavior_summary: Dict[str, Any]
    ) -> ReportSection:
        """创建行为分析章节"""
        total_time = behavior_summary.get("total_time", 0)
        sessions = behavior_summary.get("sessions", 0)
        exercises = behavior_summary.get("exercises_completed", 0)
        
        content = f"""
## 学习行为统计

| 指标 | 数值 |
|------|------|
| 学习时长 | {total_time // 60} 小时 {total_time % 60} 分钟 |
| 学习次数 | {sessions} 次 |
| 完成练习 | {exercises} 道 |
| 平均每次时长 | {(total_time / sessions):.0f} 分钟 |\n
### 学习习惯建议

{self._get_behavior_suggestions(behavior_summary)}
"""
        
        return self.create_section("学习行为", content.strip(), behavior_summary)
    
    def _create_suggestion_section(
        self,
        current_ability: Dict[str, float],
        knowledge_state: Dict[str, float]
    ) -> ReportSection:
        """创建建议章节"""
        # 识别弱项
        weak_areas = [k for k, v in current_ability.items() if v < 60]
        
        content = "## 学习建议与规划\n\n"
        
        if weak_areas:
            content += f"### 重点提升领域\n\n"
            for area in weak_areas[:3]:
                content += f"- **{area}**: 建议增加练习时间，夯实基础\n"
            content += "\n"
        
        content += f"""
### 下阶段目标

1. 保持优势领域，争取达到更高水平
2. 针对弱项制定专项提升计划
3. 每周进行一次自我评估，跟踪进步

### 推荐学习资源

- 在线练习平台
- 概念讲解视频
- 错题本整理
"""
        
        return self.create_section("学习建议", content.strip())
    
    def _generate_overall_summary(
        self,
        current_ability: Dict[str, float],
        behavior_summary: Dict[str, Any]
    ) -> str:
        """生成总体摘要"""
        overall = sum(current_ability.values()) / len(current_ability) if current_ability else 0
        sessions = behavior_summary.get("sessions", 0)
        
        return f"综合得分{overall:.1f}分，本期学习{sessions}次，整体表现{'良好' if overall >= 60 else '需要加强'}。"
    
    def _get_ability_summary(self, current_ability: Dict[str, float]) -> str:
        """获取能力摘要"""
        if not current_ability:
            return "暂无能力评估数据。"
        
        strengths = [k for k, v in current_ability.items() if v >= 70]
        if strengths:
            return f"你的{strengths[0]}较为突出，建议继续保持。"
        return "各项能力均衡发展，建议继续努力。"
    
    def _get_behavior_suggestions(self, behavior_summary: Dict[str, Any]) -> str:
        """获取行为建议"""
        sessions = behavior_summary.get("sessions", 0)
        if sessions < 3:
            return "建议增加学习频率，保持每天学习的习惯。"
        elif sessions < 7:
            return "学习频率较好，建议保持并适当增加每次学习时长。"
        return "学习频率很好，请继续保持！"


# =============================================================================
# 群体分析报告生成器
# =============================================================================

class GroupReportGenerator(BaseReportGenerator):
    """群体分析报告生成器"""
    
    def generate(
        self,
        group_id: str,
        group_name: str,
        member_count: int,
        aggregate_scores: Dict[str, float],
        distribution: Dict[str, int],
        comparison_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        生成群体分析报告
        
        Args:
            group_id: 群体ID
            group_name: 群体名称
            member_count: 成员数量
            aggregate_scores: 聚合得分
            distribution: 等级分布
            comparison_data: 对比数据
        
        Returns:
            报告数据
        """
        sections = []
        charts = []
        
        # 1. 群体概览
        overview = self._create_overview_section(
            group_name, member_count, aggregate_scores
        )
        sections.append(overview)
        
        # 2. 能力分析
        ability_section, ability_chart = self._create_group_ability_section(
            aggregate_scores
        )
        sections.append(ability_section)
        charts.append(ability_chart)
        
        # 3. 等级分布
        dist_section, dist_chart = self._create_distribution_section(distribution)
        sections.append(dist_section)
        charts.append(dist_chart)
        
        # 4. 对比分析
        if comparison_data:
            comparison = self._create_comparison_section(comparison_data)
            sections.append(comparison)
        
        # 5. 教学建议
        suggestions = self._create_teaching_suggestions(aggregate_scores, distribution)
        sections.append(suggestions)
        
        return {
            "report_id": str(uuid.uuid4()),
            "report_type": "group_analysis",
            "group_id": group_id,
            "group_name": group_name,
            "member_count": member_count,
            "generated_at": datetime.now().isoformat(),
            "sections": [s.to_dict() for s in sections],
            "charts": [c.to_dict() for c in charts]
        }
    
    def _create_overview_section(
        self,
        group_name: str,
        member_count: int,
        aggregate_scores: Dict[str, float]
    ) -> ReportSection:
        """创建概览章节"""
        overall = sum(aggregate_scores.values()) / len(aggregate_scores) if aggregate_scores else 0
        
        content = f"""
## 群体概览

**群体名称**: {group_name}

**成员数量**: {member_count} 人

**平均综合得分**: {overall:.1f}/100

**报告时间**: {datetime.now().strftime('%Y年%m月%d日')}

### 能力概况

| 维度 | 平均得分 |
|------|----------|
"""
        for dim, score in aggregate_scores.items():
            content += f"| {dim} | {score:.1f} |\n"
        
        return self.create_section("群体概览", content.strip())
    
    def _create_group_ability_section(
        self,
        aggregate_scores: Dict[str, float]
    ) -> Tuple[ReportSection, ChartData]:
        """创建群体能力章节"""
        dimensions = list(aggregate_scores.keys())
        values = list(aggregate_scores.values())
        
        content = "## 群体能力分析\n\n"
        for dim, score in aggregate_scores.items():
            content += f"- **{dim}**: {self.format_score_bar(score)}\n"
        
        section = self.create_section("能力分析", content)
        chart = self.chart_generator.create_radar_chart(
            "群体能力雷达图", dimensions, values
        )
        
        return section, chart
    
    def _create_distribution_section(
        self,
        distribution: Dict[str, int]
    ) -> Tuple[ReportSection, ChartData]:
        """创建分布章节"""
        content = "## 等级分布\n\n"
        content += "| 等级 | 人数 | 占比 |\n"
        content += "|------|------|------|\n"
        
        total = sum(distribution.values())
        pie_data = []
        
        for level, count in sorted(distribution.items(), key=lambda x: -x[1]):
            percentage = count / total * 100 if total > 0 else 0
            content += f"| {self.get_level_name(level)} | {count} | {percentage:.1f}% |\n"
            pie_data.append({
                "name": self.get_level_name(level),
                "value": count
            })
        
        section = self.create_section("等级分布", content)
        chart = self.chart_generator.create_pie_chart("等级分布图", pie_data)
        
        return section, chart
    
    def _create_comparison_section(
        self,
        comparison_data: Dict[str, Any]
    ) -> ReportSection:
        """创建对比章节"""
        content = "## 群体对比\n\n"
        content += "与去年同期/其他班级对比情况：\n\n"
        
        for metric, value in comparison_data.items():
            change = value.get("change", 0)
            symbol = "↑" if change > 0 else "↓" if change < 0 else "→"
            content += f"- **{metric}**: {symbol} {abs(change):.1f}%\n"
        
        return self.create_section("对比分析", content.strip(), comparison_data)
    
    def _create_teaching_suggestions(
        self,
        aggregate_scores: Dict[str, float],
        distribution: Dict[str, int]
    ) -> ReportSection:
        """创建教学建议"""
        # 识别群体弱项
        weak_areas = [k for k, v in aggregate_scores.items() if v < 60]
        
        content = "## 教学建议\n\n"
        
        if weak_areas:
            content += f"### 重点关注领域\n\n"
            for area in weak_areas:
                content += f"- {area}是群体的薄弱环节，建议加强教学\n"
            content += "\n"
        
        content += f"""
### 分层教学建议

- **优秀生**: 提供拓展性学习材料，培养创新思维
- **中等生**: 加强基础训练，提高解题能力
- **待提升生**: 一对一辅导，夯实基础知识

### 教学调整建议

1. 针对群体薄弱环节调整教学重点
2. 增加互动环节，提高学习参与度
3. 定期进行形成性评价，跟踪进步
"""
        
        return self.create_section("教学建议", content.strip())


# =============================================================================
# 报告导出器
# =============================================================================

class ReportExporter:
    """报告导出器"""
    
    def export(self, report_data: Dict[str, Any], format: ReportFormat) -> Dict[str, Any]:
        """
        导出报告
        
        Args:
            report_data: 报告数据
            format: 导出格式
        
        Returns:
            导出结果
        """
        if format == ReportFormat.JSON:
            return self._export_json(report_data)
        elif format == ReportFormat.MARKDOWN:
            return self._export_markdown(report_data)
        elif format == ReportFormat.HTML:
            return self._export_html(report_data)
        else:
            raise ValueError(f"不支持的格式: {format}")
    
    def _export_json(self, report_data: Dict) -> Dict:
        """导出为JSON"""
        return {
            "format": "json",
            "content": json.dumps(report_data, ensure_ascii=False, indent=2),
            "filename": f"{report_data['report_id']}.json"
        }
    
    def _export_markdown(self, report_data: Dict) -> Dict:
        """导出为Markdown"""
        md_content = f"# {report_data.get('report_type', 'Report').replace('_', ' ').title()}\n\n"
        md_content += f"**生成时间**: {report_data.get('generated_at', 'N/A')}\n\n"
        md_content += f"**报告ID**: {report_data.get('report_id', 'N/A')}\n\n"
        
        if 'learner_name' in report_data:
            md_content += f"**学习者**: {report_data['learner_name']}\n\n"
        
        if 'group_name' in report_data:
            md_content += f"**群体**: {report_data['group_name']}\n\n"
        
        md_content += "---\n\n"
        
        for section in report_data.get('sections', []):
            md_content += f"## {section.get('title', 'Section')}\n\n"
            md_content += f"{section.get('content', '')}\n\n"
        
        md_content += "---\n\n*本报告由 FormalMath 评估系统自动生成*\n"
        
        return {
            "format": "markdown",
            "content": md_content,
            "filename": f"{report_data['report_id']}.md"
        }
    
    def _export_html(self, report_data: Dict) -> Dict:
        """导出为HTML"""
        html = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{report_data.get('report_type', 'Report').replace('_', ' ').title()}</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            max-width: 900px;
            margin: 0 auto;
            padding: 20px;
            line-height: 1.6;
            color: #333;
        }}
        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }}
        h2 {{
            color: #34495e;
            margin-top: 30px;
            border-left: 4px solid #3498db;
            padding-left: 10px;
        }}
        table {{
            border-collapse: collapse;
            width: 100%;
            margin: 15px 0;
        }}
        th, td {{
            border: 1px solid #ddd;
            padding: 12px;
            text-align: left;
        }}
        th {{
            background-color: #3498db;
            color: white;
        }}
        tr:nth-child(even) {{
            background-color: #f2f2f2;
        }}
        .meta {{
            color: #7f8c8d;
            margin-bottom: 20px;
            padding: 15px;
            background: #ecf0f1;
            border-radius: 5px;
        }}
        .footer {{
            margin-top: 40px;
            padding-top: 20px;
            border-top: 1px solid #ddd;
            color: #95a5a6;
            font-size: 0.9em;
            text-align: center;
        }}
    </style>
</head>
<body>
    <h1>{report_data.get('report_type', 'Report').replace('_', ' ').title()}</h1>
    <div class="meta">
        <p><strong>报告ID</strong>: {report_data.get('report_id', 'N/A')}</p>
        <p><strong>生成时间</strong>: {report_data.get('generated_at', 'N/A')}</p>
"""
        
        if 'learner_name' in report_data:
            html += f"        <p><strong>学习者</strong>: {report_data['learner_name']}</p>\n"
        
        if 'group_name' in report_data:
            html += f"        <p><strong>群体</strong>: {report_data['group_name']}</p>\n"
        
        html += "    </div>\n"
        
        for section in report_data.get('sections', []):
            title = section.get('title', 'Section')
            content = section.get('content', '').replace('\n', '<br>')
            html += f"    <h2>{title}</h2>\n"
            html += f"    <p>{content}</p>\n"
        
        html += """
    <div class="footer">
        <p>本报告由 FormalMath 评估系统自动生成</p>
    </div>
</body>
</html>
"""
        
        return {
            "format": "html",
            "content": html,
            "filename": f"{report_data['report_id']}.html"
        }


# =============================================================================
# 主报告系统类
# =============================================================================

class ReportSystem:
    """报告系统主类"""
    
    def __init__(self):
        self.personal_generator = PersonalReportGenerator()
        self.group_generator = GroupReportGenerator()
        self.exporter = ReportExporter()
    
    def generate_personal_report(
        self,
        learner_id: str,
        learner_name: str,
        evaluation_history: List[Dict],
        current_ability: Dict[str, float],
        knowledge_state: Dict[str, float],
        behavior_summary: Dict[str, Any],
        period_days: int = 30
    ) -> Dict[str, Any]:
        """生成个人报告"""
        return self.personal_generator.generate(
            learner_id, learner_name, evaluation_history,
            current_ability, knowledge_state, behavior_summary, period_days
        )
    
    def generate_group_report(
        self,
        group_id: str,
        group_name: str,
        member_count: int,
        aggregate_scores: Dict[str, float],
        distribution: Dict[str, int],
        comparison_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """生成群体报告"""
        return self.group_generator.generate(
            group_id, group_name, member_count,
            aggregate_scores, distribution, comparison_data
        )
    
    def export_report(
        self,
        report_data: Dict[str, Any],
        format: ReportFormat
    ) -> Dict[str, Any]:
        """导出报告"""
        return self.exporter.export(report_data, format)
