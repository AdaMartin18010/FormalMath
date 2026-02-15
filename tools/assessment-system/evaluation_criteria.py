# -*- coding: utf-8 -*-
"""
evaluation_criteria.py - FormalMath 评估系统评价指标定义

本模块定义评估系统中使用的所有评价指标和维度，包括：
- 五维数学能力指标（MAA标准对齐）
- 过程性评价指标
- 增值评价指标
- 表现性评价指标
- 发散思维评价指标
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from enum import Enum, auto
from datetime import datetime


class AssessmentType(Enum):
    """评估类型枚举"""
    FORMATIVE = auto()      # 形成性评价
    SUMMATIVE = auto()      # 总结性评价
    PROCESS = auto()        # 过程性评价
    VALUE_ADDED = auto()    # 增值评价
    PERFORMANCE = auto()    # 表现性评价
    DIVERGENT = auto()      # 发散思维评价


class EvaluationLevel(Enum):
    """评价等级枚举"""
    BEGINNER = 1            # 初级
    DEVELOPING = 2          # 发展中
    PROFICIENT = 3          # 熟练
    ADVANCED = 4            # 高级
    EXPERT = 5              # 专家


@dataclass
class DimensionWeight:
    """维度权重定义"""
    dimension: str
    weight: float
    sub_weights: Dict[str, float] = field(default_factory=dict)


# =============================================================================
# 五维数学能力指标（MAA标准对齐）
# =============================================================================

@dataclass
class ConceptualUnderstanding:
    """
    概念理解 (Conceptual Understanding)
    
    评估学习者对数学概念、原理、关系的理解程度
    """
    # 核心指标
    concept_mastery: float = 0.0           # 概念掌握度 (0-100)
    principle_comprehension: float = 0.0   # 原理理解度 (0-100)
    relationship_grasp: float = 0.0        # 关系把握度 (0-100)
    
    # 子指标
    definition_accuracy: float = 0.0       # 定义准确性
    theorem_understanding: float = 0.0     # 定理理解度
    proof_comprehension: float = 0.0       # 证明理解度
    interconnection_awareness: float = 0.0 # 概念间联系意识
    
    # 权重配置
    WEIGHTS = {
        'concept_mastery': 0.35,
        'principle_comprehension': 0.30,
        'relationship_grasp': 0.35
    }
    
    def calculate_score(self) -> float:
        """计算概念理解总分"""
        return (
            self.concept_mastery * self.WEIGHTS['concept_mastery'] +
            self.principle_comprehension * self.WEIGHTS['principle_comprehension'] +
            self.relationship_grasp * self.WEIGHTS['relationship_grasp']
        )


@dataclass
class ProceduralFluency:
    """
    程序流畅性 (Procedural Fluency)
    
    评估学习者执行数学程序的灵活、准确、高效程度
    """
    # 核心指标
    accuracy: float = 0.0                  # 准确性 (0-100)
    efficiency: float = 0.0                # 效率 (0-100)
    flexibility: float = 0.0               # 灵活性 (0-100)
    
    # 子指标
    calculation_speed: float = 0.0         # 计算速度
    error_rate: float = 0.0                # 错误率 (越低越好)
    procedure_selection: float = 0.0       # 程序选择能力
    algorithm_mastery: float = 0.0         # 算法掌握度
    
    # 权重配置
    WEIGHTS = {
        'accuracy': 0.40,
        'efficiency': 0.30,
        'flexibility': 0.30
    }
    
    def calculate_score(self) -> float:
        """计算程序流畅性总分"""
        return (
            self.accuracy * self.WEIGHTS['accuracy'] +
            self.efficiency * self.WEIGHTS['efficiency'] +
            self.flexibility * self.WEIGHTS['flexibility']
        )


@dataclass
class StrategicCompetence:
    """
    策略能力 (Strategic Competence)
    
    评估学习者制定和运用数学策略解决问题的能力
    """
    # 核心指标
    problem_analysis: float = 0.0          # 问题分析能力 (0-100)
    strategy_formulation: float = 0.0      # 策略制定能力 (0-100)
    strategy_execution: float = 0.0        # 策略执行能力 (0-100)
    
    # 子指标
    decomposition_skill: float = 0.0       # 问题分解技能
    pattern_recognition: float = 0.0       # 模式识别能力
    heuristic_application: float = 0.0     # 启发式方法应用
    metacognitive_strategy: float = 0.0    # 元认知策略使用
    
    # 权重配置
    WEIGHTS = {
        'problem_analysis': 0.30,
        'strategy_formulation': 0.40,
        'strategy_execution': 0.30
    }
    
    def calculate_score(self) -> float:
        """计算策略能力总分"""
        return (
            self.problem_analysis * self.WEIGHTS['problem_analysis'] +
            self.strategy_formulation * self.WEIGHTS['strategy_formulation'] +
            self.strategy_execution * self.WEIGHTS['strategy_execution']
        )


@dataclass
class AdaptiveReasoning:
    """
    适应性推理 (Adaptive Reasoning)
    
    评估学习者进行逻辑思考、解释、论证的能力
    """
    # 核心指标
    logical_thinking: float = 0.0          # 逻辑思维能力 (0-100)
    justification_ability: float = 0.0     # 论证能力 (0-100)
    explanation_clarity: float = 0.0       # 解释清晰度 (0-100)
    
    # 子指标
    deductive_reasoning: float = 0.0       # 演绎推理
    inductive_reasoning: float = 0.0       # 归纳推理
    analogical_reasoning: float = 0.0      # 类比推理
    proof_construction: float = 0.0        # 证明构建能力
    
    # 权重配置
    WEIGHTS = {
        'logical_thinking': 0.35,
        'justification_ability': 0.35,
        'explanation_clarity': 0.30
    }
    
    def calculate_score(self) -> float:
        """计算适应性推理总分"""
        return (
            self.logical_thinking * self.WEIGHTS['logical_thinking'] +
            self.justification_ability * self.WEIGHTS['justification_ability'] +
            self.explanation_clarity * self.WEIGHTS['explanation_clarity']
        )


@dataclass
class ProductiveDisposition:
    """
    数学产出 (Productive Disposition)
    
    评估学习者将数学视为有意义、有价值、可掌握的学科的态度
    """
    # 核心指标
    confidence: float = 0.0                # 数学自信心 (0-100)
    persistence: float = 0.0               # 坚持性 (0-100)
    appreciation: float = 0.0              # 数学欣赏度 (0-100)
    
    # 子指标
    growth_mindset: float = 0.0            # 成长型思维
    challenge_seeking: float = 0.0         # 寻求挑战
    self_efficacy: float = 0.0             # 自我效能感
    intrinsic_motivation: float = 0.0      # 内在动机
    
    # 权重配置
    WEIGHTS = {
        'confidence': 0.35,
        'persistence': 0.35,
        'appreciation': 0.30
    }
    
    def calculate_score(self) -> float:
        """计算数学产出总分"""
        return (
            self.confidence * self.WEIGHTS['confidence'] +
            self.persistence * self.WEIGHTS['persistence'] +
            self.appreciation * self.WEIGHTS['appreciation']
        )


# =============================================================================
# 过程性评价指标
# =============================================================================

@dataclass
class LearningParticipation:
    """学习参与度指标"""
    study_time_score: float = 0.0          # 学习时间得分
    study_frequency_score: float = 0.0     # 学习频率得分
    content_depth_score: float = 0.0       # 内容深度得分
    content_breadth_score: float = 0.0     # 内容广度得分
    
    WEIGHTS = {
        'study_time_score': 0.30,
        'study_frequency_score': 0.30,
        'content_depth_score': 0.20,
        'content_breadth_score': 0.20
    }
    
    def calculate_score(self) -> float:
        return (
            self.study_time_score * self.WEIGHTS['study_time_score'] +
            self.study_frequency_score * self.WEIGHTS['study_frequency_score'] +
            self.content_depth_score * self.WEIGHTS['content_depth_score'] +
            self.content_breadth_score * self.WEIGHTS['content_breadth_score']
        )


@dataclass
class LearningInitiative:
    """学习主动性指标"""
    active_learning_score: float = 0.0     # 主动学习得分
    active_questioning_score: float = 0.0  # 主动提问得分
    active_exploration_score: float = 0.0  # 主动探索得分
    active_reflection_score: float = 0.0   # 主动反思得分
    
    WEIGHTS = {
        'active_learning_score': 0.30,
        'active_questioning_score': 0.30,
        'active_exploration_score': 0.20,
        'active_reflection_score': 0.20
    }
    
    def calculate_score(self) -> float:
        return (
            self.active_learning_score * self.WEIGHTS['active_learning_score'] +
            self.active_questioning_score * self.WEIGHTS['active_questioning_score'] +
            self.active_exploration_score * self.WEIGHTS['active_exploration_score'] +
            self.active_reflection_score * self.WEIGHTS['active_reflection_score']
        )


@dataclass
class LearningProgress:
    """学习进度指标"""
    content_completion: float = 0.0        # 内容完成度
    knowledge_mastery: float = 0.0         # 知识掌握度
    ability_improvement: float = 0.0       # 能力提升度
    goal_achievement: float = 0.0          # 目标达成度
    
    WEIGHTS = {
        'content_completion': 0.25,
        'knowledge_mastery': 0.30,
        'ability_improvement': 0.25,
        'goal_achievement': 0.20
    }
    
    def calculate_score(self) -> float:
        return (
            self.content_completion * self.WEIGHTS['content_completion'] +
            self.knowledge_mastery * self.WEIGHTS['knowledge_mastery'] +
            self.ability_improvement * self.WEIGHTS['ability_improvement'] +
            self.goal_achievement * self.WEIGHTS['goal_achievement']
        )


# =============================================================================
# 增值评价指标
# =============================================================================

@dataclass
class ValueAddedMetrics:
    """增值评价指标"""
    ability_value_added: Dict[str, float] = field(default_factory=dict)   # 能力增值
    knowledge_value_added: Dict[str, float] = field(default_factory=dict) # 知识增值
    skill_value_added: Dict[str, float] = field(default_factory=dict)     # 技能增值
    
    new_concepts_count: int = 0              # 新掌握概念数量
    mastery_improvement: float = 0.0         # 掌握度提升
    connection_improvement: float = 0.0      # 知识关联度提升
    
    def calculate_overall_value_added(self) -> float:
        """计算总体增值"""
        ability_avg = sum(self.ability_value_added.values()) / len(self.ability_value_added) if self.ability_value_added else 0
        knowledge_avg = sum(self.knowledge_value_added.values()) / len(self.knowledge_value_added) if self.knowledge_value_added else 0
        skill_avg = sum(self.skill_value_added.values()) / len(self.skill_value_added) if self.skill_value_added else 0
        
        return (ability_avg * 0.4 + knowledge_avg * 0.35 + skill_avg * 0.25)


# =============================================================================
# 表现性评价指标
# =============================================================================

@dataclass
class OperationalAbility:
    """操作能力指标"""
    problem_analysis: float = 0.0          # 问题分析能力
    method_selection: float = 0.0          # 方法选择能力
    execution: float = 0.0                 # 执行操作能力
    verification: float = 0.0              # 结果验证能力
    
    WEIGHTS = {
        'problem_analysis': 0.25,
        'method_selection': 0.25,
        'execution': 0.30,
        'verification': 0.20
    }
    
    def calculate_score(self) -> float:
        return (
            self.problem_analysis * self.WEIGHTS['problem_analysis'] +
            self.method_selection * self.WEIGHTS['method_selection'] +
            self.execution * self.WEIGHTS['execution'] +
            self.verification * self.WEIGHTS['verification']
        )


@dataclass
class CreativeProduct:
    """创造产品指标"""
    innovation: float = 0.0                # 创新性
    practicality: float = 0.0              # 实用性
    technical_quality: float = 0.0         # 技术性
    completeness: float = 0.0              # 完整性
    
    WEIGHTS = {
        'innovation': 0.30,
        'practicality': 0.25,
        'technical_quality': 0.25,
        'completeness': 0.20
    }
    
    def calculate_score(self) -> float:
        return (
            self.innovation * self.WEIGHTS['innovation'] +
            self.practicality * self.WEIGHTS['practicality'] +
            self.technical_quality * self.WEIGHTS['technical_quality'] +
            self.completeness * self.WEIGHTS['completeness']
        )


# =============================================================================
# 发散思维评价指标
# =============================================================================

@dataclass
class CreativityMetrics:
    """创造性指标"""
    fluency: float = 0.0                   # 流畅性（想法数量）
    flexibility: float = 0.0               # 灵活性（想法类型多样性）
    originality: float = 0.0               # 独创性（想法独特性）
    elaboration: float = 0.0               # 精细性（想法详细程度）
    
    WEIGHTS = {
        'fluency': 0.25,
        'flexibility': 0.25,
        'originality': 0.30,
        'elaboration': 0.20
    }
    
    def calculate_creativity_score(self) -> float:
        """计算创造性总分"""
        return (
            self.fluency * self.WEIGHTS['fluency'] +
            self.flexibility * self.WEIGHTS['flexibility'] +
            self.originality * self.WEIGHTS['originality'] +
            self.elaboration * self.WEIGHTS['elaboration']
        )


# =============================================================================
# 综合评价指标容器
# =============================================================================

@dataclass
class MathematicalAbilityProfile:
    """
    数学能力档案
    
    整合五维数学能力指标的完整档案
    """
    conceptual_understanding: ConceptualUnderstanding = field(default_factory=ConceptualUnderstanding)
    procedural_fluency: ProceduralFluency = field(default_factory=ProceduralFluency)
    strategic_competence: StrategicCompetence = field(default_factory=StrategicCompetence)
    adaptive_reasoning: AdaptiveReasoning = field(default_factory=AdaptiveReasoning)
    productive_disposition: ProductiveDisposition = field(default_factory=ProductiveDisposition)
    
    # 五维权重（MAA标准建议权重）
    DIMENSION_WEIGHTS = {
        'conceptual_understanding': 0.20,
        'procedural_fluency': 0.20,
        'strategic_competence': 0.25,
        'adaptive_reasoning': 0.25,
        'productive_disposition': 0.10
    }
    
    def calculate_overall_score(self) -> float:
        """计算综合数学能力得分"""
        scores = {
            'conceptual_understanding': self.conceptual_understanding.calculate_score(),
            'procedural_fluency': self.procedural_fluency.calculate_score(),
            'strategic_competence': self.strategic_competence.calculate_score(),
            'adaptive_reasoning': self.adaptive_reasoning.calculate_score(),
            'productive_disposition': self.productive_disposition.calculate_score()
        }
        
        overall = sum(scores[dim] * weight for dim, weight in self.DIMENSION_WEIGHTS.items())
        return overall
    
    def get_dimension_scores(self) -> Dict[str, float]:
        """获取各维度得分"""
        return {
            '概念理解': self.conceptual_understanding.calculate_score(),
            '程序流畅性': self.procedural_fluency.calculate_score(),
            '策略能力': self.strategic_competence.calculate_score(),
            '适应性推理': self.adaptive_reasoning.calculate_score(),
            '数学产出': self.productive_disposition.calculate_score()
        }
    
    def identify_strengths(self, threshold: float = 70.0) -> List[str]:
        """识别强项维度"""
        scores = self.get_dimension_scores()
        return [dim for dim, score in scores.items() if score >= threshold]
    
    def identify_weaknesses(self, threshold: float = 50.0) -> List[str]:
        """识别待改进维度"""
        scores = self.get_dimension_scores()
        return [dim for dim, score in scores.items() if score < threshold]


@dataclass
class EvaluationCriteria:
    """
    评价标准定义
    
    定义各评价等级的分数阈值
    """
    # 等级阈值
    THRESHOLDS = {
        EvaluationLevel.BEGINNER: (0, 40),
        EvaluationLevel.DEVELOPING: (40, 60),
        EvaluationLevel.PROFICIENT: (60, 80),
        EvaluationLevel.ADVANCED: (80, 95),
        EvaluationLevel.EXPERT: (95, 100)
    }
    
    @classmethod
    def get_level(cls, score: float) -> EvaluationLevel:
        """根据分数获取等级"""
        for level, (low, high) in cls.THRESHOLDS.items():
            if low <= score < high or (high == 100 and score >= low):
                return level
        return EvaluationLevel.BEGINNER
    
    @classmethod
    def get_level_description(cls, level: EvaluationLevel) -> str:
        """获取等级描述"""
        descriptions = {
            EvaluationLevel.BEGINNER: "初级 - 正在建立基础概念和技能",
            EvaluationLevel.DEVELOPING: "发展中 - 正在发展理解和应用能力",
            EvaluationLevel.PROFICIENT: "熟练 - 能够独立应用知识和技能",
            EvaluationLevel.ADVANCED: "高级 - 能够灵活应用和迁移知识",
            EvaluationLevel.EXPERT: "专家 - 能够创造新知和指导他人"
        }
        return descriptions.get(level, "未知")


# =============================================================================
# 学习者档案
# =============================================================================

@dataclass
class LearnerProfile:
    """学习者档案"""
    learner_id: str
    name: str = ""
    created_at: datetime = field(default_factory=datetime.now)
    
    # 当前能力状态
    current_ability: MathematicalAbilityProfile = field(default_factory=MathematicalAbilityProfile)
    
    # 初始能力状态（用于增值评价）
    initial_ability: MathematicalAbilityProfile = field(default_factory=MathematicalAbilityProfile)
    
    # 学习历史
    learning_history: List[Dict[str, Any]] = field(default_factory=list)
    
    # 知识掌握状态
    knowledge_state: Dict[str, float] = field(default_factory=dict)
    
    def calculate_value_added(self) -> ValueAddedMetrics:
        """计算能力增值"""
        current_scores = self.current_ability.get_dimension_scores()
        initial_scores = self.initial_ability.get_dimension_scores()
        
        ability_added = {}
        for dim in current_scores:
            ability_added[dim] = current_scores[dim] - initial_scores.get(dim, 0)
        
        return ValueAddedMetrics(
            ability_value_added=ability_added,
            knowledge_value_added={},  # 由具体系统填充
            skill_value_added={}
        )


# 导出所有类
__all__ = [
    'AssessmentType',
    'EvaluationLevel',
    'DimensionWeight',
    'ConceptualUnderstanding',
    'ProceduralFluency',
    'StrategicCompetence',
    'AdaptiveReasoning',
    'ProductiveDisposition',
    'LearningParticipation',
    'LearningInitiative',
    'LearningProgress',
    'ValueAddedMetrics',
    'OperationalAbility',
    'CreativeProduct',
    'CreativityMetrics',
    'MathematicalAbilityProfile',
    'EvaluationCriteria',
    'LearnerProfile'
]
