# -*- coding: utf-8 -*-
"""
report_generator.py - FormalMath 评估系统报告生成器

本模块实现评估报告的生成和导出功能，包括：
- 学习进度报告
- 能力评估报告
- 增值评价报告
- 表现性评价报告
- 多格式导出（JSON, Markdown, HTML）
"""

import json
from typing import Dict, List, Optional, Any, Union
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from enum import Enum, auto
from pathlib import Path

from evaluation_criteria import (
    LearnerProfile, MathematicalAbilityProfile, EvaluationCriteria, EvaluationLevel
)
from scoring_engine import ScoringEngine
from feedback_generator import FeedbackGenerator, FeedbackReport


# =============================================================================
# 报告类型定义
# =============================================================================

class ReportType(Enum):
    """报告类型枚举"""
    PROGRESS = "progress"           # 学习进度报告
    ABILITY = "ability"             # 能力评估报告
    VALUE_ADDED = "value_added"     # 增值评价报告
    PERFORMANCE = "performance"     # 表现性评价报告
    COMPREHENSIVE = "comprehensive" # 综合评价报告
    SUMMATIVE = "summative"         # 总结性评价报告


class ReportFormat(Enum):
    """报告格式枚举"""
    JSON = "json"
    MARKDOWN = "md"
    HTML = "html"
    TEXT = "txt"


@dataclass
class ReportSection:
    """报告章节"""
    title: str
    content: str
    data: Dict[str, Any] = field(default_factory=dict)
    subsections: List['ReportSection'] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        def serialize_value(v):
            if isinstance(v, Enum):
                return v.name
            elif isinstance(v, datetime):
                return v.isoformat()
            elif isinstance(v, dict):
                return {k: serialize_value(val) for k, val in v.items()}
            elif isinstance(v, list):
                return [serialize_value(item) for item in v]
            return v
        
        return {
            'title': self.title,
            'content': self.content,
            'data': {k: serialize_value(v) for k, v in self.data.items()},
            'subsections': [s.to_dict() for s in self.subsections]
        }


@dataclass
class AssessmentReport:
    """评估报告基类"""
    report_id: str
    report_type: ReportType
    learner_id: str
    learner_name: str
    generated_at: datetime
    period_start: Optional[datetime] = None
    period_end: Optional[datetime] = None
    sections: List[ReportSection] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def add_section(self, section: ReportSection):
        """添加章节"""
        self.sections.append(section)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'report_id': self.report_id,
            'report_type': self.report_type.value if isinstance(self.report_type, Enum) else str(self.report_type),
            'learner_id': self.learner_id,
            'learner_name': self.learner_name,
            'generated_at': self.generated_at.isoformat(),
            'period_start': self.period_start.isoformat() if self.period_start else None,
            'period_end': self.period_end.isoformat() if self.period_end else None,
            'sections': [s.to_dict() for s in self.sections],
            'metadata': self._serialize_metadata(self.metadata)
        }
    
    def _serialize_metadata(self, metadata: Dict[str, Any]) -> Dict[str, Any]:
        """序列化元数据，处理不可序列化的类型"""
        result = {}
        for key, value in metadata.items():
            if isinstance(value, Enum):
                result[key] = value.name
            elif isinstance(value, datetime):
                result[key] = value.isoformat()
            elif isinstance(value, dict):
                result[key] = self._serialize_metadata(value)
            elif isinstance(value, list):
                result[key] = [
                    item.name if isinstance(item, Enum) else 
                    item.isoformat() if isinstance(item, datetime) else
                    item
                    for item in value
                ]
            else:
                result[key] = value
        return result
    
    def to_json(self, indent: int = 2) -> str:
        """转换为JSON字符串"""
        return json.dumps(self.to_dict(), indent=indent, ensure_ascii=False)


# =============================================================================
# 报告生成器基类
# =============================================================================

class BaseReportGenerator:
    """报告生成器基类"""
    
    def __init__(self):
        self.scoring_engine = ScoringEngine()
        self.feedback_generator = FeedbackGenerator()
    
    def generate_report_id(self, learner_id: str, report_type: ReportType) -> str:
        """生成报告ID"""
        timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
        return f"{report_type.value}_{learner_id}_{timestamp}"
    
    def create_section(self, title: str, content: str, data: Dict[str, Any] = None) -> ReportSection:
        """创建报告章节"""
        return ReportSection(
            title=title,
            content=content,
            data=data or {}
        )


# =============================================================================
# 学习进度报告生成器
# =============================================================================

class ProgressReportGenerator(BaseReportGenerator):
    """学习进度报告生成器"""
    
    def generate(
        self,
        learner_profile: LearnerProfile,
        learning_path: Dict[str, Any],
        period_days: int = 30
    ) -> AssessmentReport:
        """
        生成学习进度报告
        
        Args:
            learner_profile: 学习者档案
            learning_path: 学习路径
            period_days: 报告周期（天）
        
        Returns:
            学习进度报告
        """
        report_id = self.generate_report_id(learner_profile.learner_id, ReportType.PROGRESS)
        end_date = datetime.now()
        start_date = end_date - timedelta(days=period_days)
        
        report = AssessmentReport(
            report_id=report_id,
            report_type=ReportType.PROGRESS,
            learner_id=learner_profile.learner_id,
            learner_name=learner_profile.name,
            generated_at=end_date,
            period_start=start_date,
            period_end=end_date
        )
        
        # 生成报告内容
        report.add_section(self._create_summary_section(learner_profile))
        report.add_section(self._create_knowledge_section(learner_profile))
        report.add_section(self._create_completion_section(learner_profile, learning_path))
        report.add_section(self._create_activity_section(learner_profile, period_days))
        
        return report
    
    def _create_summary_section(self, learner_profile: LearnerProfile) -> ReportSection:
        """创建摘要章节"""
        overall_score = learner_profile.current_ability.calculate_overall_score()
        level = EvaluationCriteria.get_level(overall_score)
        
        content = f"""
## 学习概况

- **学习者**: {learner_profile.name}
- **当前综合得分**: {overall_score:.1f}/100
- **能力等级**: {self._get_level_name(level)}
- **报告生成时间**: {datetime.now().strftime('%Y年%m月%d日')}

### 五维能力雷达

| 维度 | 得分 | 等级 |
|------|------|------|
"""
        scores = learner_profile.current_ability.get_dimension_scores()
        for dim, score in scores.items():
            dim_level = EvaluationCriteria.get_level(score)
            content += f"| {dim} | {score:.1f} | {self._get_level_name(dim_level)} |\n"
        
        return self.create_section("学习概况", content, {'overall_score': overall_score})
    
    def _create_knowledge_section(self, learner_profile: LearnerProfile) -> ReportSection:
        """创建知识掌握章节"""
        knowledge_state = learner_profile.knowledge_state
        
        if not knowledge_state:
            content = "暂无知识掌握数据。"
        else:
            mastered = sum(1 for m in knowledge_state.values() if m >= 80)
            developing = sum(1 for m in knowledge_state.values() if 60 <= m < 80)
            beginner = sum(1 for m in knowledge_state.values() if m < 60)
            
            avg_mastery = sum(knowledge_state.values()) / len(knowledge_state)
            
            content = f"""
## 知识掌握情况

- **总概念数**: {len(knowledge_state)}
- **已精通**: {mastered} 个概念
- **掌握中**: {developing} 个概念
- **初学**: {beginner} 个概念
- **平均掌握度**: {avg_mastery:.1f}%

### 详细掌握度

"""
            for concept, mastery in sorted(knowledge_state.items(), key=lambda x: -x[1]):
                bar = "█" * int(mastery / 10) + "░" * (10 - int(mastery / 10))
                content += f"- {concept}: {bar} {mastery:.1f}%\n"
        
        return self.create_section("知识掌握", content, dict(knowledge_state))
    
    def _create_completion_section(
        self, 
        learner_profile: LearnerProfile, 
        learning_path: Dict[str, Any]
    ) -> ReportSection:
        """创建完成度章节"""
        total_items = len(learning_path.get('content_items', []))
        completed_items = sum(1 for m in learner_profile.knowledge_state.values() if m > 0)
        
        completion_rate = (completed_items / total_items * 100) if total_items > 0 else 0
        
        content = f"""
## 学习进度

- **总内容项**: {total_items}
- **已完成**: {completed_items}
- **完成率**: {completion_rate:.1f}%

### 进度条

{'█' * int(completion_rate / 10)}{'░' * (10 - int(completion_rate / 10))} {completion_rate:.1f}%

### 目标达成情况

"""
        goals = learning_path.get('goals', [])
        if goals:
            achieved = sum(1 for g in goals if g.get('achieved', False))
            content += f"- 已完成目标: {achieved}/{len(goals)}\n"
            for goal in goals:
                status = "✓" if goal.get('achieved') else "○"
                content += f"  {status} {goal.get('description', '未命名目标')}\n"
        else:
            content += "暂无学习目标数据。\n"
        
        return self.create_section("学习进度", content, {'completion_rate': completion_rate})
    
    def _create_activity_section(self, learner_profile: LearnerProfile, period_days: int) -> ReportSection:
        """创建学习活动章节"""
        history = learner_profile.learning_history
        
        # 统计活动数据
        total_sessions = len(history)
        total_time = sum(r.get('duration', 0) for r in history)
        
        content = f"""
## 学习活动统计

- **评估周期**: 最近 {period_days} 天
- **学习次数**: {total_sessions} 次
- **总学习时长**: {total_time // 60} 小时 {total_time % 60} 分钟
- **平均每次**: {(total_time / total_sessions):.0f} 分钟（如有学习记录）

### 学习趋势

根据你的学习记录，系统分析你的学习模式并提供个性化建议。
"""
        
        return self.create_section("学习活动", content, {
            'total_sessions': total_sessions,
            'total_time': total_time
        })
    
    def _get_level_name(self, level: EvaluationLevel) -> str:
        """获取等级名称"""
        names = {
            EvaluationLevel.EXPERT: "专家",
            EvaluationLevel.ADVANCED: "高级",
            EvaluationLevel.PROFICIENT: "熟练",
            EvaluationLevel.DEVELOPING: "发展中",
            EvaluationLevel.BEGINNER: "初级"
        }
        return names.get(level, "未知")


# =============================================================================
# 能力评估报告生成器
# =============================================================================

class AbilityReportGenerator(BaseReportGenerator):
    """能力评估报告生成器"""
    
    def generate(
        self,
        learner_profile: LearnerProfile,
        detailed: bool = True
    ) -> AssessmentReport:
        """
        生成能力评估报告
        
        Args:
            learner_profile: 学习者档案
            detailed: 是否生成详细报告
        
        Returns:
            能力评估报告
        """
        report_id = self.generate_report_id(learner_profile.learner_id, ReportType.ABILITY)
        
        report = AssessmentReport(
            report_id=report_id,
            report_type=ReportType.ABILITY,
            learner_id=learner_profile.learner_id,
            learner_name=learner_profile.name,
            generated_at=datetime.now()
        )
        
        # 评估数学能力
        assessment_result = self.scoring_engine.evaluate_mathematical_ability(
            learner_profile.current_ability
        )
        
        # 生成报告章节
        report.add_section(self._create_overview_section(assessment_result))
        report.add_section(self._create_dimension_details_section(assessment_result))
        report.add_section(self._create_strengths_weaknesses_section(assessment_result))
        
        if detailed:
            report.add_section(self._create_recommendations_section(assessment_result))
        
        return report
    
    def _create_overview_section(self, assessment_result: Dict[str, Any]) -> ReportSection:
        """创建概览章节"""
        overall_score = assessment_result['overall_score']
        level_desc = assessment_result['level_description']
        
        content = f"""
## 能力评估概览

### 综合评分

**{overall_score:.1f}/100**

{level_desc}

### 五维能力得分

```
概念理解:    {assessment_result['dimension_scores']['概念理解']:5.1f} {'█' * int(assessment_result['dimension_scores']['概念理解'] / 10)}
程序流畅性:  {assessment_result['dimension_scores']['程序流畅性']:5.1f} {'█' * int(assessment_result['dimension_scores']['程序流畅性'] / 10)}
策略能力:    {assessment_result['dimension_scores']['策略能力']:5.1f} {'█' * int(assessment_result['dimension_scores']['策略能力'] / 10)}
适应性推理:  {assessment_result['dimension_scores']['适应性推理']:5.1f} {'█' * int(assessment_result['dimension_scores']['适应性推理'] / 10)}
数学产出:    {assessment_result['dimension_scores']['数学产出']:5.1f} {'█' * int(assessment_result['dimension_scores']['数学产出'] / 10)}
```
"""
        return self.create_section("评估概览", content, assessment_result)
    
    def _create_dimension_details_section(self, assessment_result: Dict[str, Any]) -> ReportSection:
        """创建维度详情章节"""
        scores = assessment_result['dimension_scores']
        
        content = "## 各维度详细分析\n\n"
        
        dimension_descriptions = {
            '概念理解': {
                'description': '对数学概念、原理、关系的理解程度',
                'indicators': ['概念掌握度', '原理理解度', '关系把握度']
            },
            '程序流畅性': {
                'description': '执行数学程序的灵活、准确、高效程度',
                'indicators': ['准确性', '效率', '灵活性']
            },
            '策略能力': {
                'description': '制定和运用数学策略解决问题的能力',
                'indicators': ['问题分析', '策略制定', '策略执行']
            },
            '适应性推理': {
                'description': '进行逻辑思考、解释、论证的能力',
                'indicators': ['逻辑思维', '论证能力', '解释清晰度']
            },
            '数学产出': {
                'description': '将数学视为有意义、有价值、可掌握的学科的态度',
                'indicators': ['自信心', '坚持性', '欣赏度']
            }
        }
        
        for dim, score in scores.items():
            desc = dimension_descriptions.get(dim, {})
            level = EvaluationCriteria.get_level(score)
            level_name = self._get_level_name(level)
            
            content += f"""
### {dim} ({score:.1f}分 - {level_name})

**定义**: {desc.get('description', '')}

**评估指标**: {', '.join(desc.get('indicators', []))}

**评价**: {self._get_dimension_evaluation(dim, score)}

---
"""
        
        return self.create_section("维度详情", content, scores)
    
    def _create_strengths_weaknesses_section(self, assessment_result: Dict[str, Any]) -> ReportSection:
        """创建强项弱项章节"""
        strengths = assessment_result.get('strengths', [])
        weaknesses = assessment_result.get('weaknesses', [])
        
        content = "## 强项与待改进领域\n\n"
        
        if strengths:
            content += "### ✅ 强项\n\n"
            for strength in strengths:
                content += f"- **{strength}**: 这是你突出的能力，建议继续深入发展。\n"
        else:
            content += "### 强项\n\n正在全面发展中，建议均衡发展各维度能力。\n"
        
        content += "\n"
        
        if weaknesses:
            content += "### 📈 待改进领域\n\n"
            for weakness in weaknesses:
                content += f"- **{weakness}**: 建议重点提升此维度的能力。\n"
        else:
            content += "### 待改进领域\n\n各维度能力发展均衡，继续保持！\n"
        
        return self.create_section("强弱分析", content, {
            'strengths': strengths,
            'weaknesses': weaknesses
        })
    
    def _create_recommendations_section(self, assessment_result: Dict[str, Any]) -> ReportSection:
        """创建学习建议章节"""
        weaknesses = assessment_result.get('weaknesses', [])
        
        content = "## 个性化学习建议\n\n"
        content += "基于你的能力评估结果，系统为你推荐以下学习策略：\n\n"
        
        if weaknesses:
            content += "### 重点提升建议\n\n"
            for weakness in weaknesses[:3]:
                suggestions = self._get_suggestions_for_dimension(weakness)
                content += f"**{weakness}**:\n"
                for suggestion in suggestions:
                    content += f"- {suggestion}\n"
                content += "\n"
        
        content += """
### 通用学习建议

1. **制定学习计划**: 根据评估结果，有针对性地安排学习内容
2. **定期自测**: 使用系统的自我评估功能跟踪进步
3. **寻求帮助**: 遇到困难时及时向教师或同学求助
4. **反思总结**: 定期回顾学习内容，总结经验
"""
        
        return self.create_section("学习建议", content)
    
    def _get_dimension_evaluation(self, dimension: str, score: float) -> str:
        """获取维度评价"""
        if score >= 80:
            return "表现出色，可以挑战更高级的内容。"
        elif score >= 60:
            return "掌握良好，建议继续巩固和提升。"
        elif score >= 40:
            return "正在发展中，需要更多练习。"
        else:
            return "需要重点关注，建议从基础开始。"
    
    def _get_suggestions_for_dimension(self, dimension: str) -> List[str]:
        """获取维度的学习建议"""
        suggestions = {
            '概念理解': [
                "重新阅读相关概念的定义和定理",
                "制作概念卡片，进行概念辨析",
                "尝试用自己的话解释概念"
            ],
            '程序流畅性': [
                "进行专项计算练习",
                "注意解题步骤的规范性",
                "总结常用计算技巧"
            ],
            '策略能力': [
                "分析不同类型问题的解法",
                "学习常用的问题解决策略",
                "尝试一题多解"
            ],
            '适应性推理': [
                "练习数学证明",
                "学习逻辑推理方法",
                "解释你的思考过程"
            ],
            '数学产出': [
                "设定可实现的小目标",
                "记录学习中的成功体验",
                "寻找数学学习的乐趣"
            ]
        }
        return suggestions.get(dimension, ["持续练习，定期评估"])
    
    def _get_level_name(self, level: EvaluationLevel) -> str:
        """获取等级名称"""
        names = {
            EvaluationLevel.EXPERT: "专家",
            EvaluationLevel.ADVANCED: "高级",
            EvaluationLevel.PROFICIENT: "熟练",
            EvaluationLevel.DEVELOPING: "发展中",
            EvaluationLevel.BEGINNER: "初级"
        }
        return names.get(level, "未知")


# =============================================================================
# 增值评价报告生成器
# =============================================================================

class ValueAddedReportGenerator(BaseReportGenerator):
    """增值评价报告生成器"""
    
    def generate(
        self,
        learner_profile: LearnerProfile,
        period_days: int = 30
    ) -> AssessmentReport:
        """
        生成增值评价报告
        
        Args:
            learner_profile: 学习者档案
            period_days: 评估周期（天）
        
        Returns:
            增值评价报告
        """
        report_id = self.generate_report_id(learner_profile.learner_id, ReportType.VALUE_ADDED)
        end_date = datetime.now()
        start_date = end_date - timedelta(days=period_days)
        
        report = AssessmentReport(
            report_id=report_id,
            report_type=ReportType.VALUE_ADDED,
            learner_id=learner_profile.learner_id,
            learner_name=learner_profile.name,
            generated_at=end_date,
            period_start=start_date,
            period_end=end_date
        )
        
        # 计算增值数据
        value_added = self.scoring_engine.evaluate_value_added(learner_profile, period_days)
        
        report.add_section(self._create_value_added_overview(value_added))
        report.add_section(self._create_ability_value_added(value_added))
        report.add_section(self._create_knowledge_value_added(value_added))
        
        return report
    
    def _create_value_added_overview(self, value_added: Dict[str, Any]) -> ReportSection:
        """创建增值概览"""
        overall = value_added.get('overall_value_added', 0)
        
        trend = "📈 显著提升" if overall > 10 else "📊 稳步提升" if overall > 0 else "📉 需要关注"
        
        content = f"""
## 增值概览

### 总体增值

**{overall:+.1f} 分** {trend}

评估周期内，你的数学能力整体{'有所提升' if overall > 0 else '持平或下降'}。

### 关键指标

- **新掌握概念**: {value_added.get('new_concepts_count', 0)} 个
- **掌握度提升**: {value_added.get('mastery_improvement', 0):+.1f}%
"""
        
        return self.create_section("增值概览", content, value_added)
    
    def _create_ability_value_added(self, value_added: Dict[str, Any]) -> ReportSection:
        """创建能力增值章节"""
        ability_added = value_added.get('ability_value_added', {})
        
        content = "## 各能力维度增值\n\n"
        content += "| 维度 | 增值 | 趋势 |\n"
        content += "|------|------|------|\n"
        
        for dim, added in ability_added.items():
            trend = "↑" if added > 5 else "→" if added >= -5 else "↓"
            content += f"| {dim} | {added:+.1f} | {trend} |\n"
        
        content += "\n### 增值分析\n\n"
        
        positive = [dim for dim, val in ability_added.items() if val > 0]
        negative = [dim for dim, val in ability_added.items() if val < 0]
        
        if positive:
            content += f"**提升领域**: {', '.join(positive)}\n\n"
        if negative:
            content += f"**需关注领域**: {', '.join(negative)}\n\n"
        
        return self.create_section("能力增值", content, ability_added)
    
    def _create_knowledge_value_added(self, value_added: Dict[str, Any]) -> ReportSection:
        """创建知识增值章节"""
        knowledge_added = value_added.get('knowledge_value_added', {})
        
        content = "## 知识增值\n\n"
        
        if knowledge_added:
            content += "### 概念掌握度变化\n\n"
            for concept, change in sorted(knowledge_added.items(), key=lambda x: -x[1])[:10]:
                bar = "+" * int(abs(change) / 5) if change > 0 else "-" * int(abs(change) / 5)
                content += f"- {concept}: {change:+.1f}% {bar}\n"
        else:
            content += "暂无详细知识增值数据。\n"
        
        return self.create_section("知识增值", content, knowledge_added)


# =============================================================================
# 报告导出器
# =============================================================================

class ReportExporter:
    """报告导出器"""
    
    @staticmethod
    def export_to_json(report: AssessmentReport, filepath: str) -> str:
        """导出为JSON文件"""
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(report.to_json())
        return filepath
    
    @staticmethod
    def export_to_markdown(report: AssessmentReport, filepath: str) -> str:
        """导出为Markdown文件"""
        md_content = ReportExporter._convert_to_markdown(report)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(md_content)
        return filepath
    
    @staticmethod
    def _convert_to_markdown(report: AssessmentReport) -> str:
        """将报告转换为Markdown格式"""
        md = f"""# {report.report_type.value.upper()} 报告

**学习者**: {report.learner_name}  
**报告ID**: {report.report_id}  
**生成时间**: {report.generated_at.strftime('%Y年%m月%d日 %H:%M')}

"""
        if report.period_start and report.period_end:
            md += f"**评估周期**: {report.period_start.strftime('%Y-%m-%d')} 至 {report.period_end.strftime('%Y-%m-%d')}\n\n"
        
        for section in report.sections:
            md += section.content + "\n\n"
        
        md += "---\n\n*本报告由 FormalMath 评估系统自动生成*\n"
        
        return md
    
    @staticmethod
    def export_to_html(report: AssessmentReport, filepath: str) -> str:
        """导出为HTML文件"""
        html_content = ReportExporter._convert_to_html(report)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(html_content)
        return filepath
    
    @staticmethod
    def _convert_to_html(report: AssessmentReport) -> str:
        """将报告转换为HTML格式"""
        html = f"""<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>{report.report_type.value.upper()} 报告 - {report.learner_name}</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; max-width: 900px; margin: 0 auto; padding: 20px; line-height: 1.6; }}
        h1 {{ color: #2c3e50; border-bottom: 2px solid #3498db; padding-bottom: 10px; }}
        h2 {{ color: #34495e; margin-top: 30px; }}
        h3 {{ color: #7f8c8d; }}
        table {{ border-collapse: collapse; width: 100%; margin: 15px 0; }}
        th, td {{ border: 1px solid #ddd; padding: 12px; text-align: left; }}
        th {{ background-color: #3498db; color: white; }}
        tr:nth-child(even) {{ background-color: #f2f2f2; }}
        .meta {{ color: #7f8c8d; margin-bottom: 20px; }}
        .footer {{ margin-top: 40px; padding-top: 20px; border-top: 1px solid #ddd; color: #95a5a6; font-size: 0.9em; }}
    </style>
</head>
<body>
    <h1>{report.report_type.value.upper()} 报告</h1>
    <div class="meta">
        <p><strong>学习者</strong>: {report.learner_name}</p>
        <p><strong>报告ID</strong>: {report.report_id}</p>
        <p><strong>生成时间</strong>: {report.generated_at.strftime('%Y年%m月%d日 %H:%M')}</p>
    </div>
"""
        
        for section in report.sections:
            html += f"<h2>{section.title}</h2>\n"
            # 简单的Markdown到HTML转换
            content = section.content
            content = content.replace('\n\n', '</p>\n<p>')
            content = content.replace('\n', '<br>')
            html += f"<p>{content}</p>\n"
        
        html += """
    <div class="footer">
        <p>本报告由 FormalMath 评估系统自动生成</p>
    </div>
</body>
</html>
"""
        return html


# =============================================================================
# 报告生成器主类
# =============================================================================

class ReportGenerator:
    """
    报告生成器主类
    
    整合所有报告生成功能，提供统一的报告生成接口
    """
    
    def __init__(self):
        self.progress_generator = ProgressReportGenerator()
        self.ability_generator = AbilityReportGenerator()
        self.value_added_generator = ValueAddedReportGenerator()
        self.exporter = ReportExporter()
    
    def generate_report(
        self,
        report_type: ReportType,
        learner_profile: LearnerProfile,
        **kwargs
    ) -> AssessmentReport:
        """
        生成报告
        
        Args:
            report_type: 报告类型
            learner_profile: 学习者档案
            **kwargs: 额外参数
        
        Returns:
            评估报告
        """
        if report_type == ReportType.PROGRESS:
            return self.progress_generator.generate(
                learner_profile, 
                kwargs.get('learning_path', {}),
                kwargs.get('period_days', 30)
            )
        elif report_type == ReportType.ABILITY:
            return self.ability_generator.generate(
                learner_profile,
                kwargs.get('detailed', True)
            )
        elif report_type == ReportType.VALUE_ADDED:
            return self.value_added_generator.generate(
                learner_profile,
                kwargs.get('period_days', 30)
            )
        else:
            raise ValueError(f"不支持的报告类型: {report_type}")
    
    def export_report(
        self,
        report: AssessmentReport,
        format: ReportFormat,
        filepath: str
    ) -> str:
        """
        导出报告
        
        Args:
            report: 评估报告
            format: 导出格式
            filepath: 文件路径
        
        Returns:
            导出的文件路径
        """
        if format == ReportFormat.JSON:
            return self.exporter.export_to_json(report, filepath)
        elif format == ReportFormat.MARKDOWN:
            return self.exporter.export_to_markdown(report, filepath)
        elif format == ReportFormat.HTML:
            return self.exporter.export_to_html(report, filepath)
        else:
            raise ValueError(f"不支持的导出格式: {format}")


# 导出所有类和函数
__all__ = [
    'ReportType',
    'ReportFormat',
    'ReportSection',
    'AssessmentReport',
    'BaseReportGenerator',
    'ProgressReportGenerator',
    'AbilityReportGenerator',
    'ValueAddedReportGenerator',
    'ReportExporter',
    'ReportGenerator'
]
