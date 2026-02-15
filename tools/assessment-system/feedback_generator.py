# -*- coding: utf-8 -*-
"""
feedback_generator.py - FormalMath 评估系统反馈生成器

本模块实现个性化反馈生成功能，包括：
- 实时反馈生成
- 总结性反馈生成
- 学习建议生成
- 改进策略推荐
"""

from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum, auto

from evaluation_criteria import (
    MathematicalAbilityProfile, LearnerProfile, EvaluationLevel,
    AssessmentType, EvaluationCriteria
)
from scoring_engine import ScoringEngine


# =============================================================================
# 反馈类型定义
# =============================================================================

class FeedbackType(Enum):
    """反馈类型枚举"""
    REAL_TIME = auto()          # 实时反馈
    SUMMARY = auto()            # 总结反馈
    PROCESS = auto()            # 过程反馈
    VALUE_ADDED = auto()        # 增值反馈
    PERFORMANCE = auto()        # 表现性反馈
    DIVERGENT = auto()          # 发散思维反馈
    IMPROVEMENT = auto()        # 改进建议


class FeedbackPriority(Enum):
    """反馈优先级"""
    HIGH = "high"
    MEDIUM = "medium"
    LOW = "low"


@dataclass
class FeedbackItem:
    """反馈项"""
    type: FeedbackType
    priority: FeedbackPriority
    title: str
    content: str
    suggestions: List[str] = field(default_factory=list)
    resources: List[str] = field(default_factory=list)
    timestamp: datetime = field(default_factory=datetime.now)


@dataclass
class FeedbackReport:
    """反馈报告"""
    learner_id: str
    feedback_type: FeedbackType
    overall_feedback: str
    items: List[FeedbackItem] = field(default_factory=list)
    generated_at: datetime = field(default_factory=datetime.now)
    
    def add_item(self, item: FeedbackItem):
        """添加反馈项"""
        self.items.append(item)
    
    def get_high_priority_items(self) -> List[FeedbackItem]:
        """获取高优先级反馈项"""
        return [item for item in self.items if item.priority == FeedbackPriority.HIGH]
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典格式"""
        return {
            'learner_id': self.learner_id,
            'feedback_type': self.feedback_type.name,
            'overall_feedback': self.overall_feedback,
            'generated_at': self.generated_at.isoformat(),
            'items': [
                {
                    'type': item.type.name,
                    'priority': item.priority.value,
                    'title': item.title,
                    'content': item.content,
                    'suggestions': item.suggestions,
                    'resources': item.resources,
                    'timestamp': item.timestamp.isoformat()
                }
                for item in self.items
            ]
        }


# =============================================================================
# 反馈模板库
# =============================================================================

class FeedbackTemplates:
    """反馈模板库"""
    
    # 维度反馈模板
    DIMENSION_FEEDBACK = {
        '概念理解': {
            'excellent': [
                "你对数学概念的理解非常深入，能够准确把握概念的本质和内涵。",
                "你能够清晰地理解数学原理，并建立概念之间的联系。"
            ],
            'good': [
                "你对数学概念有较好的理解，建议进一步探索概念间的深层联系。",
                "你的概念理解较为扎实，可以尝试更多复杂的应用场景。"
            ],
            'developing': [
                "你对基本数学概念有初步理解，建议加强基础概念的深入学习。",
                "概念理解正在发展中，多做一些概念辨析的练习会有帮助。"
            ],
            'needs_improvement': [
                "建议重点加强数学基础概念的学习，从定义和定理开始。",
                "概念理解需要更多努力，建议多阅读教材并进行概念整理。"
            ]
        },
        '程序流畅性': {
            'excellent': [
                "你的计算和程序执行非常流畅，能够灵活选择合适的方法。",
                "你在数学程序应用方面表现出色，准确性和效率都很高。"
            ],
            'good': [
                "你的程序应用能力较好，在复杂问题上可以进一步提高效率。",
                "你能够熟练执行数学程序，建议多练习不同方法的比较。"
            ],
            'developing': [
                "程序执行正在发展中，建议加强基本运算和程序步骤的练习。",
                "你的程序应用能力正在形成，多练习有助于提高熟练度。"
            ],
            'needs_improvement': [
                "建议重点练习基本数学程序和运算步骤。",
                "程序流畅性需要加强，建议从基础练习开始，注重准确性。"
            ]
        },
        '策略能力': {
            'excellent': [
                "你具有出色的数学问题解决策略，能够灵活选择和组合方法。",
                "你的策略制定和执行能力非常强，能够处理复杂的数学问题。"
            ],
            'good': [
                "你有较好的策略选择能力，在复杂问题上可以进一步扩展策略库。",
                "你的策略能力正在发展中，建议多总结不同类型问题的解法。"
            ],
            'developing': [
                "策略能力正在形成中，建议多学习不同的问题解决方法。",
                "你可以通过分析更多例题来提高策略选择和制定能力。"
            ],
            'needs_improvement': [
                "建议系统学习数学问题解决方法，从基本策略开始。",
                "策略能力需要重点培养，建议多做例题分析和方法总结。"
            ]
        },
        '适应性推理': {
            'excellent': [
                "你的逻辑推理和论证能力非常出色，能够构建严密的证明。",
                "你具有强大的数学推理能力，善于解释和论证数学结论。"
            ],
            'good': [
                "你的推理能力较好，可以尝试更复杂的证明和论证。",
                "你能够进行有效的数学推理，建议多练习证明写作。"
            ],
            'developing': [
                "推理能力正在发展中，建议多进行逻辑思维和证明练习。",
                "你可以通过分析证明过程来提高推理和论证能力。"
            ],
            'needs_improvement': [
                "建议重点加强逻辑推理训练，从简单的逻辑推理题开始。",
                "适应性推理需要更多练习，建议学习基本的证明方法和技巧。"
            ]
        },
        '数学产出': {
            'excellent': [
                "你对数学学习充满热情和信心，具有良好的数学学习态度。",
                "你表现出积极的数学学习倾向，善于坚持和欣赏数学之美。"
            ],
            'good': [
                "你对数学有一定的兴趣和信心，可以继续培养更深的热爱。",
                "你的学习态度较好，建议多分享你的数学学习体验。"
            ],
            'developing': [
                "数学学习态度正在形成中，建议多发现数学的有趣之处。",
                "你可以通过更多的数学实践来建立对数学的信心。"
            ],
            'needs_improvement': [
                "建议尝试发现数学学习的乐趣，设定小目标建立信心。",
                "培养积极的数学学习态度很重要，可以从简单的成功体验开始。"
            ]
        }
    }
    
    # 等级描述
    LEVEL_DESCRIPTION = {
        EvaluationLevel.EXPERT: "专家水平",
        EvaluationLevel.ADVANCED: "高级水平",
        EvaluationLevel.PROFICIENT: "熟练水平",
        EvaluationLevel.DEVELOPING: "发展中",
        EvaluationLevel.BEGINNER: "初级水平"
    }


# =============================================================================
# 学习建议库
# =============================================================================

class LearningSuggestions:
    """学习建议库"""
    
    SUGGESTIONS = {
        '概念理解': {
            'general': [
                "阅读教材时注重概念的定义和背景",
                "尝试用自己的语言解释数学概念",
                "建立概念地图，连接相关概念"
            ],
            'improvement': [
                "从基础概念开始，逐步深入",
                "多做概念辨析和对比练习",
                "观看概念讲解视频，多角度理解"
            ],
            'advanced': [
                "研究概念的多种等价表述",
                "探索概念在不同领域的应用",
                "尝试自己定义新概念"
            ]
        },
        '程序流畅性': {
            'general': [
                "每天进行适量的计算练习",
                "注意程序步骤的规范书写",
                "总结常用计算技巧和方法"
            ],
            'improvement': [
                "从基础运算开始，提高准确性",
                "练习标准解题步骤",
                "使用计算工具验证结果"
            ],
            'advanced': [
                "探索多种解法并比较效率",
                "研究计算方法的优化",
                "学习算法设计和分析"
            ]
        },
        '策略能力': {
            'general': [
                "分析每道题的解题思路",
                "总结不同类型问题的解法",
                "尝试一题多解"
            ],
            'improvement': [
                "学习常见的问题解决策略",
                "分析错题，找出策略问题",
                "从简单问题开始练习策略选择"
            ],
            'advanced': [
                "研究高级解题策略",
                "尝试解决开放性问题",
                "创造新的解题方法"
            ]
        },
        '适应性推理': {
            'general': [
                "练习数学证明和论证",
                "学习不同的推理方法",
                "解释你的解题思路给他人"
            ],
            'improvement': [
                "从简单的逻辑推理开始",
                "学习基本的证明方法",
                "分析经典证明的思路"
            ],
            'advanced': [
                "尝试构造复杂的证明",
                "研究不同的证明策略",
                "探索非标准推理方法"
            ]
        },
        '数学产出': {
            'general': [
                "设定可实现的学习目标",
                "记录学习中的成功体验",
                "与他人分享数学学习的乐趣"
            ],
            'improvement': [
                "从简单任务开始建立信心",
                "寻找数学学习中的乐趣",
                "庆祝每个小进步"
            ],
            'advanced': [
                "帮助其他同学学习数学",
                "参与数学竞赛或研究",
                "探索数学的历史和文化"
            ]
        }
    }
    
    # 资源推荐
    RESOURCES = {
        '概念理解': [
            "《数学概念发展史》",
            "在线概念可视化工具",
            "概念地图制作软件"
        ],
        '程序流畅性': [
            "数学练习册",
            "在线计算练习平台",
            "符号计算软件"
        ],
        '策略能力': [
            "《怎样解题》(波利亚)",
            "数学竞赛题集",
            "问题解决策略指南"
        ],
        '适应性推理': [
            "《数学证明》教材",
            "逻辑推理训练题",
            "证明写作指南"
        ],
        '数学产出': [
            "数学史读物",
            "数学科普书籍",
            "数学学习社区"
        ]
    }


# =============================================================================
# 反馈生成器
# =============================================================================

class FeedbackGenerator:
    """
    反馈生成器
    
    根据评估结果生成个性化反馈和学习建议
    """
    
    def __init__(self):
        self.templates = FeedbackTemplates()
        self.suggestions = LearningSuggestions()
        self.scoring_engine = ScoringEngine()
    
    def generate_feedback(
        self,
        learner_profile: LearnerProfile,
        assessment_results: Dict[str, Any],
        feedback_type: FeedbackType = FeedbackType.SUMMARY
    ) -> FeedbackReport:
        """
        生成综合反馈
        
        Args:
            learner_profile: 学习者档案
            assessment_results: 评估结果
            feedback_type: 反馈类型
        
        Returns:
            反馈报告
        """
        report = FeedbackReport(
            learner_id=learner_profile.learner_id,
            feedback_type=feedback_type,
            overall_feedback=self._generate_overall_feedback(assessment_results)
        )
        
        # 生成各维度反馈
        dimension_feedback = self._generate_dimension_feedback(
            learner_profile.current_ability
        )
        for item in dimension_feedback:
            report.add_item(item)
        
        # 生成强项反馈
        strengths_feedback = self._generate_strengths_feedback(
            learner_profile.current_ability
        )
        report.add_item(strengths_feedback)
        
        # 生成改进建议
        improvement_feedback = self._generate_improvement_feedback(
            learner_profile.current_ability
        )
        report.add_item(improvement_feedback)
        
        return report
    
    def _generate_overall_feedback(self, assessment_results: Dict[str, Any]) -> str:
        """生成整体反馈"""
        overall_score = assessment_results.get('overall_score', 0)
        level = EvaluationCriteria.get_level(overall_score)
        level_desc = EvaluationCriteria.get_level_description(level)
        
        return f"你的综合数学能力得分为 {overall_score:.1f} 分，处于{self.templates.LEVEL_DESCRIPTION.get(level, '未知')}。{level_desc}"
    
    def _generate_dimension_feedback(
        self, 
        ability_profile: MathematicalAbilityProfile
    ) -> List[FeedbackItem]:
        """生成各维度反馈"""
        items = []
        scores = ability_profile.get_dimension_scores()
        
        for dimension, score in scores.items():
            feedback_content, category = self._get_dimension_feedback(dimension, score)
            suggestions = self._get_dimension_suggestions(dimension, category)
            resources = self.suggestions.RESOURCES.get(dimension, [])
            
            priority = self._score_to_priority(score)
            
            item = FeedbackItem(
                type=FeedbackType.SUMMARY,
                priority=priority,
                title=f"{dimension}评估",
                content=feedback_content,
                suggestions=suggestions,
                resources=resources[:2]  # 推荐前2个资源
            )
            items.append(item)
        
        return items
    
    def _get_dimension_feedback(self, dimension: str, score: float) -> Tuple[str, str]:
        """获取维度反馈内容和类别"""
        dim_templates = self.templates.DIMENSION_FEEDBACK.get(dimension, {})
        
        if score >= 80:
            category = 'excellent'
        elif score >= 60:
            category = 'good'
        elif score >= 40:
            category = 'developing'
        else:
            category = 'needs_improvement'
        
        templates = dim_templates.get(category, ["继续努力！"])
        import random
        return random.choice(templates), category
    
    def _get_dimension_suggestions(self, dimension: str, category: str) -> List[str]:
        """获取维度学习建议"""
        dim_suggestions = self.suggestions.SUGGESTIONS.get(dimension, {})
        
        if category == 'needs_improvement':
            return dim_suggestions.get('improvement', [])
        elif category == 'excellent':
            return dim_suggestions.get('advanced', [])
        else:
            return dim_suggestions.get('general', [])
    
    def _score_to_priority(self, score: float) -> FeedbackPriority:
        """将分数转换为优先级"""
        if score < 50:
            return FeedbackPriority.HIGH
        elif score < 70:
            return FeedbackPriority.MEDIUM
        else:
            return FeedbackPriority.LOW
    
    def _generate_strengths_feedback(
        self, 
        ability_profile: MathematicalAbilityProfile
    ) -> FeedbackItem:
        """生成强项反馈"""
        strengths = ability_profile.identify_strengths(threshold=70)
        
        if strengths:
            content = f"你的数学学习强项包括：{', '.join(strengths)}。建议继续保持并在这些领域深入发展。"
            suggestions = [
                f"在{strength}领域挑战更高级的内容" 
                for strength in strengths[:2]
            ]
            suggestions.append("尝试帮助其他同学，巩固你的优势")
        else:
            content = "你正在全面发展数学能力，建议均衡提升各维度能力。"
            suggestions = ["设定阶段性目标，逐步建立优势领域"]
        
        return FeedbackItem(
            type=FeedbackType.SUMMARY,
            priority=FeedbackPriority.MEDIUM,
            title="学习强项分析",
            content=content,
            suggestions=suggestions
        )
    
    def _generate_improvement_feedback(
        self, 
        ability_profile: MathematicalAbilityProfile
    ) -> FeedbackItem:
        """生成改进建议"""
        weaknesses = ability_profile.identify_weaknesses(threshold=60)
        
        if weaknesses:
            content = f"建议重点提升以下方面：{', '.join(weaknesses)}。我们为你准备了针对性的学习建议。"
            suggestions = []
            for weakness in weaknesses[:3]:
                dim_suggestions = self.suggestions.SUGGESTIONS.get(weakness, {})
                suggestions.extend(dim_suggestions.get('improvement', [])[:2])
        else:
            content = "你的数学能力发展较为均衡，建议继续保持并挑战更高目标。"
            suggestions = [
                "尝试综合应用多个维度的能力解决复杂问题",
                "探索数学在其他学科中的应用"
            ]
        
        return FeedbackItem(
            type=FeedbackType.IMPROVEMENT,
            priority=FeedbackPriority.HIGH if weaknesses else FeedbackPriority.LOW,
            title="改进建议",
            content=content,
            suggestions=suggestions
        )
    
    def generate_process_feedback(
        self,
        learner_id: str,
        process_scores: Dict[str, Any]
    ) -> FeedbackReport:
        """
        生成过程性反馈
        
        Args:
            learner_id: 学习者ID
            process_scores: 过程性评价分数
        
        Returns:
            过程性反馈报告
        """
        report = FeedbackReport(
            learner_id=learner_id,
            feedback_type=FeedbackType.PROCESS,
            overall_feedback="基于你的学习过程数据分析，以下是反馈建议："
        )
        
        # 参与度反馈
        participation = process_scores.get('participation', {})
        if participation.get('score', 0) < 60:
            item = FeedbackItem(
                type=FeedbackType.PROCESS,
                priority=FeedbackPriority.HIGH,
                title="学习参与度",
                content="你的学习参与度有提升空间，建议制定规律的学习计划。",
                suggestions=[
                    "设定固定的每日学习时间",
                    "使用番茄工作法提高专注度",
                    "记录学习日志，追踪进度"
                ]
            )
            report.add_item(item)
        
        # 主动性反馈
        initiative = process_scores.get('initiative', {})
        if initiative.get('score', 0) < 60:
            item = FeedbackItem(
                type=FeedbackType.PROCESS,
                priority=FeedbackPriority.MEDIUM,
                title="学习主动性",
                content="提高学习主动性可以帮助你更好地掌握知识。",
                suggestions=[
                    "提前预习即将学习的内容",
                    "在学习中主动提出问题",
                    "定期进行学习反思和总结"
                ]
            )
            report.add_item(item)
        
        # 进度反馈
        progress = process_scores.get('progress', {})
        if progress.get('score', 0) < 60:
            item = FeedbackItem(
                type=FeedbackType.PROCESS,
                priority=FeedbackPriority.HIGH,
                title="学习进度",
                content="你的学习进度需要关注，建议调整学习策略。",
                suggestions=[
                    "分解学习目标，设定阶段性里程碑",
                    "重点复习掌握不够牢固的内容",
                    "寻求教师或同学的帮助"
                ]
            )
            report.add_item(item)
        
        return report
    
    def generate_value_added_feedback(
        self,
        learner_id: str,
        value_added_data: Dict[str, Any]
    ) -> FeedbackReport:
        """
        生成增值反馈
        
        Args:
            learner_id: 学习者ID
            value_added_data: 增值评价数据
        
        Returns:
            增值反馈报告
        """
        overall_added = value_added_data.get('overall_value_added', 0)
        
        report = FeedbackReport(
            learner_id=learner_id,
            feedback_type=FeedbackType.VALUE_ADDED,
            overall_feedback=f"评估期间你的整体增值为 {overall_added:.1f} 分。"
        )
        
        # 分析能力增值
        ability_added = value_added_data.get('ability_value_added', {})
        positive_dims = [dim for dim, val in ability_added.items() if val > 0]
        negative_dims = [dim for dim, val in ability_added.items() if val < 0]
        
        if positive_dims:
            content = f"以下能力维度有明显提升：{', '.join(positive_dims)}。继续保持！"
            item = FeedbackItem(
                type=FeedbackType.VALUE_ADDED,
                priority=FeedbackPriority.LOW,
                title="能力提升",
                content=content,
                suggestions=["继续深入发展这些优势能力"]
            )
            report.add_item(item)
        
        if negative_dims:
            content = f"以下能力维度需要关注：{', '.join(negative_dims)}。建议调整学习重点。"
            item = FeedbackItem(
                type=FeedbackType.VALUE_ADDED,
                priority=FeedbackPriority.HIGH,
                title="需要关注的领域",
                content=content,
                suggestions=[
                    "增加相关维度的练习时间",
                    "寻求针对性辅导",
                    "调整学习方法"
                ]
            )
            report.add_item(item)
        
        # 新掌握概念反馈
        new_concepts = value_added_data.get('new_concepts_count', 0)
        item = FeedbackItem(
            type=FeedbackType.VALUE_ADDED,
            priority=FeedbackPriority.LOW,
            title="知识扩展",
            content=f"评估期间你新掌握了 {new_concepts} 个概念。",
            suggestions=["及时复习新学概念，建立知识联系"]
        )
        report.add_item(item)
        
        return report


# =============================================================================
# 实时反馈生成器
# =============================================================================

class RealTimeFeedbackGenerator:
    """
    实时反馈生成器
    
    在学习过程中提供即时反馈
    """
    
    def __init__(self):
        self.feedback_rules = self._load_feedback_rules()
    
    def _load_feedback_rules(self) -> List[Dict]:
        """加载反馈规则"""
        return [
            {
                'condition': lambda data: data.get('error_count', 0) > 3,
                'feedback': "检测到多次错误，建议回顾一下相关概念。",
                'priority': FeedbackPriority.HIGH
            },
            {
                'condition': lambda data: data.get('time_spent', 0) > 600,  # 10分钟
                'feedback': "这道题目花费了较长时间，如果需要可以查看提示。",
                'priority': FeedbackPriority.MEDIUM
            },
            {
                'condition': lambda data: data.get('hint_used', 0) == 0 and data.get('attempts', 0) > 2,
                'feedback': "遇到困难时，适当使用提示可以帮助你更好地学习。",
                'priority': FeedbackPriority.LOW
            },
            {
                'condition': lambda data: data.get('consecutive_correct', 0) >= 5,
                'feedback': "表现很棒！你已经连续答对多道题了。",
                'priority': FeedbackPriority.LOW
            }
        ]
    
    def generate_real_time_feedback(self, interaction_data: Dict[str, Any]) -> Optional[FeedbackItem]:
        """
        生成实时反馈
        
        Args:
            interaction_data: 交互数据
        
        Returns:
            反馈项（如果满足条件）
        """
        for rule in self.feedback_rules:
            if rule['condition'](interaction_data):
                return FeedbackItem(
                    type=FeedbackType.REAL_TIME,
                    priority=rule['priority'],
                    title="学习提示",
                    content=rule['feedback'],
                    suggestions=[]
                )
        return None
    
    def generate_answer_feedback(
        self, 
        is_correct: bool, 
        attempt_count: int,
        time_spent: float
    ) -> FeedbackItem:
        """
        生成答题反馈
        
        Args:
            is_correct: 是否正确
            attempt_count: 尝试次数
            time_spent: 花费时间（秒）
        
        Returns:
            反馈项
        """
        if is_correct:
            if attempt_count == 1:
                content = "正确！答得很好。"
                priority = FeedbackPriority.LOW
            else:
                content = f"正确！经过{attempt_count}次尝试终于答对了，坚持就是胜利！"
                priority = FeedbackPriority.LOW
        else:
            content = "答案不正确，再仔细思考一下。"
            priority = FeedbackPriority.MEDIUM
            
        suggestions = []
        if not is_correct:
            suggestions.append("重新审视题目条件")
            suggestions.append("检查计算过程")
            if attempt_count > 2:
                suggestions.append("可以尝试使用提示")
        
        return FeedbackItem(
            type=FeedbackType.REAL_TIME,
            priority=priority,
            title="答题反馈",
            content=content,
            suggestions=suggestions
        )


# 导出所有类和函数
__all__ = [
    'FeedbackType',
    'FeedbackPriority',
    'FeedbackItem',
    'FeedbackReport',
    'FeedbackTemplates',
    'LearningSuggestions',
    'FeedbackGenerator',
    'RealTimeFeedbackGenerator'
]
