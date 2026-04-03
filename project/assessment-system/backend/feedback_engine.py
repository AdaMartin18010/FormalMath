# -*- coding: utf-8 -*-
"""
feedback_engine.py - FormalMath 评估系统反馈引擎

实现智能反馈生成功能：
- 实时反馈
- 错误分析
- 改进建议生成
- 个性化学习建议
"""

import uuid
import random
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime
from dataclasses import dataclass, field
from enum import Enum


# =============================================================================
# 数据类定义
# =============================================================================

class FeedbackPriority(str, Enum):
    """反馈优先级"""
    HIGH = "high"
    MEDIUM = "medium"
    LOW = "low"


@dataclass
class FeedbackItem:
    """反馈项"""
    id: str
    type: str
    priority: FeedbackPriority
    title: str
    content: str
    suggestions: List[str] = field(default_factory=list)
    resources: List[str] = field(default_factory=list)
    related_concepts: List[str] = field(default_factory=list)
    created_at: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> dict:
        return {
            "id": self.id,
            "type": self.type,
            "priority": self.priority.value,
            "title": self.title,
            "content": self.content,
            "suggestions": self.suggestions,
            "resources": self.resources,
            "related_concepts": self.related_concepts,
            "created_at": self.created_at.isoformat()
        }


@dataclass
class ErrorAnalysis:
    """错误分析结果"""
    error_type: str
    concept_id: str
    severity: str  # high, medium, low
    root_cause: str
    suggestions: List[str]
    similar_errors_count: int = 0
    
    def to_dict(self) -> dict:
        return {
            "error_type": self.error_type,
            "concept_id": self.concept_id,
            "severity": self.severity,
            "root_cause": self.root_cause,
            "suggestions": self.suggestions,
            "similar_errors_count": self.similar_errors_count
        }


@dataclass
class ImprovementPlan:
    """改进计划"""
    learner_id: str
    target_areas: List[str]
    actions: List[Dict[str, Any]]
    timeline: str
    expected_outcomes: List[str]
    
    def to_dict(self) -> dict:
        return {
            "learner_id": self.learner_id,
            "target_areas": self.target_areas,
            "actions": self.actions,
            "timeline": self.timeline,
            "expected_outcomes": self.expected_outcomes
        }


# =============================================================================
# 反馈模板库
# =============================================================================

class FeedbackTemplates:
    """反馈模板库"""
    
    # 维度反馈模板
    DIMENSION_FEEDBACK = {
        "knowledge_mastery": {
            "excellent": [
                "你对数学知识的掌握非常扎实，概念理解深入透彻。",
                "你的知识基础牢固，能够准确运用各类数学概念和定理。"
            ],
            "good": [
                "你对数学知识有较好的掌握，建议进一步巩固薄弱环节。",
                "你的知识掌握程度不错，可以尝试更多综合性的应用。"
            ],
            "developing": [
                "你的数学知识正在逐步建立，建议加强基础概念的学习。",
                "知识掌握正在发展中，多做基础练习会有帮助。"
            ],
            "needs_improvement": [
                "建议重点复习基础概念和定理，打好数学基础。",
                "知识掌握需要加强，建议系统性地复习教材内容。"
            ]
        },
        "skill_proficiency": {
            "excellent": [
                "你的数学技能非常熟练，计算准确高效。",
                "你能够灵活运用各种数学方法和技巧解决问题。"
            ],
            "good": [
                "你的数学技能掌握较好，在复杂计算上可以进一步提高效率。",
                "技能运用较为熟练，建议多练习以提高速度。"
            ],
            "developing": [
                "数学技能正在发展中，建议加强基本运算训练。",
                "技能掌握需要更多练习，注重准确性和规范性。"
            ],
            "needs_improvement": [
                "建议重点练习基本数学技能，从简单题目开始。",
                "技能熟练度需要提升，建议制定专项训练计划。"
            ]
        },
        "problem_solving": {
            "excellent": [
                "你具有出色的问题分析和解决能力，思路清晰。",
                "你能够灵活运用多种策略解决复杂的数学问题。"
            ],
            "good": [
                "你的问题解决能力较好，可以尝试更具挑战性的题目。",
                "解题思路较为清晰，建议多总结不同题型的解法。"
            ],
            "developing": [
                "问题解决能力正在形成中，建议多分析典型例题。",
                "解题思路需要进一步培养，可以尝试一题多解。"
            ],
            "needs_improvement": [
                "建议系统学习解题方法，从理解题意开始。",
                "问题解决能力需要重点培养，建议多做基础题建立信心。"
            ]
        },
        "creative_thinking": {
            "excellent": [
                "你具有优秀的数学思维，能够提出独特的见解和解法。",
                "你的创造性思维让你在数学学习中脱颖而出。"
            ],
            "good": [
                "你有较好的数学思维，可以尝试更多开放性问题。",
                "思维较为活跃，建议多探索数学问题的不同角度。"
            ],
            "developing": [
                "数学思维正在发展中，建议多思考问题的多种解法。",
                "创造性思维需要培养，可以尝试提出自己的问题。"
            ],
            "needs_improvement": [
                "建议培养数学思维的灵活性，多进行发散性思考。",
                "创造性思维需要激发，可以从简单的变式练习开始。"
            ]
        }
    }
    
    # 等级反馈模板
    LEVEL_FEEDBACK = {
        "expert": "你已达到专家水平，可以尝试指导其他同学或进行数学研究。",
        "advanced": "你处于高级水平，可以挑战更复杂的数学问题和证明。",
        "proficient": "你已达到熟练水平，能够独立解决大部分数学问题。",
        "developing": "你正在快速发展中，继续保持这个学习节奏。",
        "beginner": "你处于起步阶段，稳扎稳打，基础会越来越牢固。"
    }
    
    # 增值反馈模板
    GROWTH_FEEDBACK = {
        "rapid": "你的进步非常快，学习方法很有效，请继续保持！",
        "steady": "你正在稳步提升，这种持续的努力会带来更大的收获。",
        "slow": "你的学习正在积累中，量变终将引起质变，不要放弃。",
        "stagnant": "近期进展较慢，建议调整学习策略或寻求帮助。",
        "declining": "发现学习有下滑趋势，建议及时找出原因并调整。"
    }
    
    # 鼓励语模板
    ENCOURAGEMENT_TEMPLATES = [
        "相信通过持续努力，你一定能够取得更大的进步！",
        "每一次练习都是进步的机会，继续加油！",
        "数学学习是一场马拉松，坚持下去就是胜利！",
        "你的努力一定会得到回报，相信自己！",
        "遇到困难不要怕，这正是成长的机会！"
    ]


# =============================================================================
# 学习建议库
# =============================================================================

class LearningSuggestions:
    """学习建议库"""
    
    SUGGESTIONS = {
        "knowledge_mastery": {
            "general": [
                "每天复习当天学习的概念，及时巩固记忆",
                "制作概念卡片，利用碎片时间复习",
                "尝试用自己的语言解释概念，检验理解程度"
            ],
            "improvement": [
                "重新阅读教材，重点关注定义和定理",
                "做概念辨析练习，区分相似概念",
                "向老师或同学请教不懂的地方"
            ],
            "advanced": [
                "研究概念之间的联系，构建知识网络",
                "探索概念在不同领域的应用",
                "尝试证明定理，深化理解"
            ]
        },
        "skill_proficiency": {
            "general": [
                "每天进行适量的计算练习，保持手感",
                "注意计算过程的规范性，减少粗心错误",
                "总结常用计算技巧，建立方法库"
            ],
            "improvement": [
                "从基础计算开始，逐步提高难度",
                "整理错题，分析错误原因",
                "限时练习，提高计算速度"
            ],
            "advanced": [
                "探索多种解法，比较优劣",
                "研究计算的简化技巧",
                "学习算法思维，优化解题过程"
            ]
        },
        "problem_solving": {
            "general": [
                "做题前先分析题目，明确已知和所求",
                "尝试多种解题思路，培养灵活性",
                "完成题目后反思，总结解题方法"
            ],
            "improvement": [
                "学习典型解题策略，如归纳法、反证法等",
                "分析错题，找出思路问题",
                "从简单问题开始，逐步建立信心"
            ],
            "advanced": [
                "挑战开放性问题，培养创新思维",
                "尝试改编题目，加深理解",
                "研究数学竞赛题目，拓展视野"
            ]
        },
        "creative_thinking": {
            "general": [
                "多问\"为什么\"，培养质疑精神",
                "尝试一题多解，拓展思维",
                "关注数学与现实生活的联系"
            ],
            "improvement": [
                "做一些趣味数学题，激发兴趣",
                "阅读数学史，了解数学发展过程",
                "参与数学讨论，听取不同观点"
            ],
            "advanced": [
                "尝试自己提出数学问题",
                "研究数学前沿问题",
                "参与数学建模或研究项目"
            ]
        }
    }
    
    # 推荐资源
    RESOURCES = {
        "knowledge_mastery": [
            {"name": "《数学概念手册》", "type": "book"},
            {"name": "Khan Academy - 数学基础", "type": "video"},
            {"name": "概念地图工具", "type": "tool"}
        ],
        "skill_proficiency": [
            {"name": "《数学计算技巧》", "type": "book"},
            {"name": "计算练习APP", "type": "app"},
            {"name": "符号计算软件", "type": "tool"}
        ],
        "problem_solving": [
            {"name": "《怎样解题》(波利亚)", "type": "book"},
            {"name": "数学竞赛题集", "type": "book"},
            {"name": "解题策略在线课程", "type": "video"}
        ],
        "creative_thinking": [
            {"name": "《数学与猜想》", "type": "book"},
            {"name": "数学思维训练课程", "type": "video"},
            {"name": "开放性问题集", "type": "exercise"}
        ]
    }


# =============================================================================
# 错误分析引擎
# =============================================================================

class ErrorAnalysisEngine:
    """错误分析引擎"""
    
    # 常见错误类型
    ERROR_TYPES = {
        "concept_misunderstanding": {
            "name": "概念理解错误",
            "causes": ["概念定义不清", "概念混淆", "理解片面"],
            "suggestions": [
                "重新学习概念定义",
                "做概念对比练习",
                "通过例子加深理解"
            ]
        },
        "calculation_error": {
            "name": "计算错误",
            "causes": ["粗心大意", "计算技能不熟练", "符号处理不当"],
            "suggestions": [
                "仔细检查计算过程",
                "加强基础计算练习",
                "使用草稿纸规范书写"
            ]
        },
        "logical_error": {
            "name": "逻辑错误",
            "causes": ["推理不严谨", "逻辑链条断裂", "前提假设错误"],
            "suggestions": [
                "学习基本逻辑规则",
                "分析证明过程",
                "多做逻辑推理练习"
            ]
        },
        "method_selection_error": {
            "name": "方法选择错误",
            "causes": ["对方法理解不深", "不会分析题目", "缺乏策略意识"],
            "suggestions": [
                "总结各类题目的解题方法",
                "学习题目分析方法",
                "建立解题策略库"
            ]
        },
        "careless_error": {
            "name": "粗心错误",
            "causes": ["注意力不集中", "审题不清", "检查不仔细"],
            "suggestions": [
                "培养专注的学习习惯",
                "仔细审题，标记关键信息",
                "养成检查的习惯"
            ]
        }
    }
    
    def analyze_error(
        self,
        question_id: str,
        user_answer: Any,
        correct_answer: Any,
        concept_id: str,
        error_history: List[Dict] = None
    ) -> ErrorAnalysis:
        """
        分析错误
        
        Args:
            question_id: 题目ID
            user_answer: 用户答案
            correct_answer: 正确答案
            concept_id: 相关概念ID
            error_history: 错误历史
        
        Returns:
            错误分析结果
        """
        # 判断错误类型
        error_type = self._classify_error(user_answer, correct_answer)
        
        # 获取错误类型信息
        type_info = self.ERROR_TYPES.get(error_type, self.ERROR_TYPES["careless_error"])
        
        # 统计类似错误
        similar_count = 0
        if error_history:
            similar_count = sum(
                1 for e in error_history 
                if e.get("error_type") == error_type
            )
        
        # 判定严重程度
        if similar_count >= 3:
            severity = "high"
        elif similar_count >= 1:
            severity = "medium"
        else:
            severity = "low"
        
        return ErrorAnalysis(
            error_type=type_info["name"],
            concept_id=concept_id,
            severity=severity,
            root_cause=random.choice(type_info["causes"]),
            suggestions=type_info["suggestions"],
            similar_errors_count=similar_count
        )
    
    def _classify_error(self, user_answer: Any, correct_answer: Any) -> str:
        """分类错误类型"""
        # 简化的错误分类逻辑
        if user_answer is None or user_answer == "":
            return "careless_error"
        
        # 如果答案类型完全不同，可能是概念错误
        if type(user_answer) != type(correct_answer):
            return "concept_misunderstanding"
        
        # 数值接近可能是计算错误
        if isinstance(user_answer, (int, float)) and isinstance(correct_answer, (int, float)):
            if abs(user_answer - correct_answer) < abs(correct_answer) * 0.1:
                return "calculation_error"
        
        # 默认返回方法选择错误
        return "method_selection_error"
    
    def generate_error_feedback(self, error_analysis: ErrorAnalysis) -> FeedbackItem:
        """生成错误反馈"""
        priority = FeedbackPriority.HIGH if error_analysis.severity == "high" else FeedbackPriority.MEDIUM
        
        content = f"""
检测到{error_analysis.error_type}。

可能原因：{error_analysis.root_cause}

这类错误你已出现{error_analysis.similar_errors_count + 1}次，建议重点关注。
"""
        
        return FeedbackItem(
            id=str(uuid.uuid4()),
            type="error_feedback",
            priority=priority,
            title=f"错误分析 - {error_analysis.error_type}",
            content=content.strip(),
            suggestions=error_analysis.suggestions,
            related_concepts=[error_analysis.concept_id]
        )


# =============================================================================
# 反馈生成器
# =============================================================================

class FeedbackGenerator:
    """反馈生成器"""
    
    def __init__(self):
        self.templates = FeedbackTemplates()
        self.suggestions = LearningSuggestions()
        self.error_engine = ErrorAnalysisEngine()
    
    def generate_assessment_feedback(
        self,
        learner_id: str,
        evaluation_result: Dict[str, Any]
    ) -> List[FeedbackItem]:
        """
        生成评估反馈
        
        Args:
            learner_id: 学习者ID
            evaluation_result: 评价结果
        
        Returns:
            反馈项列表
        """
        feedback_items = []
        
        # 1. 整体评价反馈
        overall_feedback = self._generate_overall_feedback(evaluation_result)
        feedback_items.append(overall_feedback)
        
        # 2. 各维度反馈
        dimension_feedbacks = self._generate_dimension_feedbacks(evaluation_result)
        feedback_items.extend(dimension_feedbacks)
        
        # 3. 改进建议
        improvement_feedback = self._generate_improvement_feedback(evaluation_result)
        if improvement_feedback:
            feedback_items.append(improvement_feedback)
        
        # 4. 鼓励语
        encouragement = self._generate_encouragement(evaluation_result)
        feedback_items.append(encouragement)
        
        return feedback_items
    
    def _generate_overall_feedback(
        self, 
        evaluation_result: Dict[str, Any]
    ) -> FeedbackItem:
        """生成整体反馈"""
        overall_score = evaluation_result.get("overall_score", 0)
        level = evaluation_result.get("level", "beginner")
        
        level_desc = self.templates.LEVEL_FEEDBACK.get(level, "")
        
        content = f"""
你的综合得分为{overall_score:.1f}分。

{level_desc}
"""
        
        return FeedbackItem(
            id=str(uuid.uuid4()),
            type="overall",
            priority=FeedbackPriority.LOW,
            title="综合评价",
            content=content.strip(),
            suggestions=["查看各维度详细分析", "制定针对性学习计划"]
        )
    
    def _generate_dimension_feedbacks(
        self, 
        evaluation_result: Dict[str, Any]
    ) -> List[FeedbackItem]:
        """生成各维度反馈"""
        items = []
        dimension_scores = evaluation_result.get("dimension_scores", {})
        
        for dim_key, dim_data in dimension_scores.items():
            score = dim_data.get("score", 0)
            
            # 确定评价类别
            if score >= 80:
                category = "excellent"
                priority = FeedbackPriority.LOW
            elif score >= 60:
                category = "good"
                priority = FeedbackPriority.LOW
            elif score >= 40:
                category = "developing"
                priority = FeedbackPriority.MEDIUM
            else:
                category = "needs_improvement"
                priority = FeedbackPriority.HIGH
            
            # 获取反馈模板
            dim_templates = self.templates.DIMENSION_FEEDBACK.get(dim_key, {})
            templates = dim_templates.get(category, ["继续努力！"])
            content = random.choice(templates)
            
            # 获取建议
            suggestions_data = self.suggestions.SUGGESTIONS.get(dim_key, {})
            if category == "needs_improvement":
                suggestions = suggestions_data.get("improvement", [])
            elif category == "excellent":
                suggestions = suggestions_data.get("advanced", [])
            else:
                suggestions = suggestions_data.get("general", [])
            
            # 获取资源推荐
            resources = [
                r["name"] for r in self.suggestions.RESOURCES.get(dim_key, [])
            ]
            
            item = FeedbackItem(
                id=str(uuid.uuid4()),
                type="dimension",
                priority=priority,
                title=f"{self._translate_dimension_name(dim_key)} - {score:.1f}分",
                content=content,
                suggestions=suggestions[:3],
                resources=resources[:2]
            )
            items.append(item)
        
        return items
    
    def _generate_improvement_feedback(
        self, 
        evaluation_result: Dict[str, Any]
    ) -> Optional[FeedbackItem]:
        """生成改进建议反馈"""
        details = evaluation_result.get("details", {})
        weaknesses = details.get("weaknesses", [])
        
        if not weaknesses:
            return None
        
        content = f"""
基于评估结果，建议重点关注以下方面：

{', '.join(weaknesses)}

我们为你准备了针对性的改进建议。
"""
        
        # 收集所有改进建议
        all_suggestions = []
        for weakness in weaknesses[:2]:  # 只取前两个弱项
            dim_key = self._reverse_translate_dimension(weakness)
            suggestions_data = self.suggestions.SUGGESTIONS.get(dim_key, {})
            all_suggestions.extend(suggestions_data.get("improvement", []))
        
        return FeedbackItem(
            id=str(uuid.uuid4()),
            type="improvement",
            priority=FeedbackPriority.HIGH,
            title="改进建议",
            content=content.strip(),
            suggestions=list(set(all_suggestions))[:5]  # 去重后取前5条
        )
    
    def _generate_encouragement(
        self, 
        evaluation_result: Dict[str, Any]
    ) -> FeedbackItem:
        """生成鼓励语"""
        overall_score = evaluation_result.get("overall_score", 0)
        
        if overall_score >= 80:
            encouragement = "太棒了！你的数学能力非常出色，继续保持！"
        elif overall_score >= 60:
            encouragement = "你的进步很明显，相信通过努力会取得更大突破！"
        else:
            encouragement = random.choice(self.templates.ENCOURAGEMENT_TEMPLATES)
        
        return FeedbackItem(
            id=str(uuid.uuid4()),
            type="encouragement",
            priority=FeedbackPriority.LOW,
            title="加油！",
            content=encouragement,
            suggestions=[]
        )
    
    def generate_real_time_feedback(
        self,
        learner_id: str,
        interaction_data: Dict[str, Any]
    ) -> Optional[FeedbackItem]:
        """
        生成实时反馈
        
        Args:
            learner_id: 学习者ID
            interaction_data: 交互数据
        
        Returns:
            反馈项（如需要）
        """
        # 检测是否需要反馈
        feedback_rules = [
            {
                "condition": lambda d: d.get("consecutive_errors", 0) >= 3,
                "title": "遇到困难了？",
                "content": "连续答错了几道题，建议先休息一下或者回顾一下相关知识点。",
                "priority": FeedbackPriority.HIGH,
                "suggestions": ["查看相关概念讲解", "做一些基础练习", "寻求帮助"]
            },
            {
                "condition": lambda d: d.get("time_spent", 0) > 600,  # 10分钟
                "title": "用时较长",
                "content": "这道题你已经思考很久了，如果需要可以查看提示。",
                "priority": FeedbackPriority.MEDIUM,
                "suggestions": ["查看提示", "跳过此题，稍后再做", "寻求帮助"]
            },
            {
                "condition": lambda d: d.get("consecutive_correct", 0) >= 5,
                "title": "表现很棒！",
                "content": "你已经连续答对多道题了，状态很好！",
                "priority": FeedbackPriority.LOW,
                "suggestions": ["继续保持", "挑战更高难度"]
            }
        ]
        
        for rule in feedback_rules:
            if rule["condition"](interaction_data):
                return FeedbackItem(
                    id=str(uuid.uuid4()),
                    type="real_time",
                    priority=rule["priority"],
                    title=rule["title"],
                    content=rule["content"],
                    suggestions=rule["suggestions"]
                )
        
        return None
    
    def generate_process_feedback(
        self,
        learner_id: str,
        process_result: Dict[str, Any]
    ) -> List[FeedbackItem]:
        """生成过程性反馈"""
        items = []
        
        # 检查参与度
        participation = process_result.get("participation", 0)
        if participation < 60:
            items.append(FeedbackItem(
                id=str(uuid.uuid4()),
                type="process",
                priority=FeedbackPriority.HIGH,
                title="学习参与度提醒",
                content="你的学习参与度有待提高，建议制定规律的学习计划。",
                suggestions=[
                    "设定固定的学习时间",
                    "使用番茄工作法提高专注度",
                    "记录学习日志"
                ]
            ))
        
        # 检查主动性
        initiative = process_result.get("initiative", 0)
        if initiative < 50:
            items.append(FeedbackItem(
                id=str(uuid.uuid4()),
                type="process",
                priority=FeedbackPriority.MEDIUM,
                title="学习主动性建议",
                content="提高学习主动性可以帮助你更好地掌握知识。",
                suggestions=[
                    "提前预习新内容",
                    "主动提出问题",
                    "定期做学习反思"
                ]
            ))
        
        return items
    
    def generate_improvement_plan(
        self,
        learner_id: str,
        weak_areas: List[str],
        current_level: str
    ) -> ImprovementPlan:
        """生成改进计划"""
        actions = []
        
        for area in weak_areas[:3]:  # 最多3个改进目标
            dim_key = self._reverse_translate_dimension(area)
            suggestions = self.suggestions.SUGGESTIONS.get(dim_key, {}).get("improvement", [])
            
            actions.append({
                "area": area,
                "actions": suggestions[:3],
                "duration": "2周",
                "checkpoints": ["第1周自测", "第2周评估"]
            })
        
        timeline = "4周" if len(weak_areas) <= 2 else "6周"
        
        expected_outcomes = [
            f"{area}能力提升10-15分" for area in weak_areas[:2]
        ]
        expected_outcomes.append("整体学习效果明显改善")
        
        return ImprovementPlan(
            learner_id=learner_id,
            target_areas=weak_areas[:3],
            actions=actions,
            timeline=timeline,
            expected_outcomes=expected_outcomes
        )
    
    def _translate_dimension_name(self, key: str) -> str:
        """翻译维度名称"""
        translations = {
            "knowledge_mastery": "知识掌握度",
            "skill_proficiency": "技能熟练度",
            "problem_solving": "问题解决能力",
            "creative_thinking": "创新思维能力"
        }
        return translations.get(key, key)
    
    def _reverse_translate_dimension(self, name: str) -> str:
        """反向翻译维度名称"""
        reverse = {
            "知识掌握度": "knowledge_mastery",
            "技能熟练度": "skill_proficiency",
            "问题解决能力": "problem_solving",
            "创新思维能力": "creative_thinking"
        }
        return reverse.get(name, name)


# =============================================================================
# 主反馈系统类
# =============================================================================

class FeedbackSystem:
    """反馈系统主类"""
    
    def __init__(self):
        self.generator = FeedbackGenerator()
        self.error_engine = ErrorAnalysisEngine()
    
    def process_evaluation_result(
        self,
        learner_id: str,
        evaluation_result: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        处理评估结果，生成完整反馈
        
        Args:
            learner_id: 学习者ID
            evaluation_result: 评估结果
        
        Returns:
            反馈包
        """
        # 生成反馈项
        feedback_items = self.generator.generate_assessment_feedback(
            learner_id, evaluation_result
        )
        
        # 生成改进计划
        details = evaluation_result.get("details", {})
        weaknesses = details.get("weaknesses", [])
        level = evaluation_result.get("level", "beginner")
        
        improvement_plan = None
        if weaknesses:
            improvement_plan = self.generator.generate_improvement_plan(
                learner_id, weaknesses, level
            )
        
        return {
            "learner_id": learner_id,
            "feedback_items": [item.to_dict() for item in feedback_items],
            "improvement_plan": improvement_plan.to_dict() if improvement_plan else None,
            "summary": self._generate_summary(feedback_items),
            "generated_at": datetime.now().isoformat()
        }
    
    def process_error(
        self,
        learner_id: str,
        question_id: str,
        user_answer: Any,
        correct_answer: Any,
        concept_id: str,
        error_history: List[Dict] = None
    ) -> Dict[str, Any]:
        """
        处理答题错误
        
        Args:
            learner_id: 学习者ID
            question_id: 题目ID
            user_answer: 用户答案
            correct_answer: 正确答案
            concept_id: 概念ID
            error_history: 错误历史
        
        Returns:
            错误分析和反馈
        """
        # 分析错误
        analysis = self.error_engine.analyze_error(
            question_id, user_answer, correct_answer, concept_id, error_history
        )
        
        # 生成反馈
        feedback = self.error_engine.generate_error_feedback(analysis)
        
        return {
            "error_analysis": analysis.to_dict(),
            "feedback": feedback.to_dict(),
            "timestamp": datetime.now().isoformat()
        }
    
    def get_real_time_feedback(
        self,
        learner_id: str,
        interaction_data: Dict[str, Any]
    ) -> Optional[Dict[str, Any]]:
        """获取实时反馈"""
        feedback = self.generator.generate_real_time_feedback(learner_id, interaction_data)
        if feedback:
            return feedback.to_dict()
        return None
    
    def _generate_summary(self, feedback_items: List[FeedbackItem]) -> str:
        """生成反馈摘要"""
        high_priority = sum(1 for item in feedback_items if item.priority == FeedbackPriority.HIGH)
        medium_priority = sum(1 for item in feedback_items if item.priority == FeedbackPriority.MEDIUM)
        
        return f"共生成{len(feedback_items)}条反馈，其中高优先级{high_priority}条，中优先级{medium_priority}条。"
