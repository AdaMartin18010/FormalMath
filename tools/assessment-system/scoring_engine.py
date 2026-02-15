# -*- coding: utf-8 -*-
"""
scoring_engine.py - FormalMath 评估系统评分引擎

本模块实现各种评分算法和模型，包括：
- 基础评分算法
- 加权评分模型
- 增值评分模型
- 表现性评分模型
- 认知诊断评分
"""

import math
from typing import Dict, List, Optional, Any, Tuple, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict

from evaluation_criteria import (
    MathematicalAbilityProfile, LearnerProfile, ValueAddedMetrics,
    LearningParticipation, LearningInitiative, LearningProgress,
    OperationalAbility, CreativeProduct, CreativityMetrics,
    EvaluationCriteria, EvaluationLevel, AssessmentType
)


# =============================================================================
# 基础评分算法
# =============================================================================

class ScoringAlgorithm:
    """评分算法基类"""
    
    @staticmethod
    def normalize_score(score: float, min_val: float = 0, max_val: float = 100) -> float:
        """将分数归一化到 [0, 100] 范围"""
        if max_val == min_val:
            return 50.0
        normalized = (score - min_val) / (max_val - min_val) * 100
        return max(0, min(100, normalized))
    
    @staticmethod
    def calculate_weighted_average(scores: Dict[str, float], weights: Dict[str, float]) -> float:
        """计算加权平均分"""
        total_weight = sum(weights.values())
        if total_weight == 0:
            return 0.0
        
        weighted_sum = sum(scores.get(key, 0) * weights.get(key, 0) for key in set(scores) & set(weights))
        return weighted_sum / total_weight
    
    @staticmethod
    def apply_penalty(score: float, penalty_factor: float, severity: float = 1.0) -> float:
        """应用惩罚因子"""
        return max(0, score * (1 - penalty_factor * severity))
    
    @staticmethod
    def apply_bonus(score: float, bonus_factor: float, cap: float = 100.0) -> float:
        """应用奖励因子"""
        return min(cap, score * (1 + bonus_factor))


# =============================================================================
# 加权评分模型
# =============================================================================

@dataclass
class WeightedScoringModel:
    """
    加权评分模型
    
    支持多维度加权评分，可配置不同维度和指标的权重
    """
    name: str
    dimensions: Dict[str, Dict[str, float]] = field(default_factory=dict)
    
    def add_dimension(self, dimension_name: str, indicators: Dict[str, float]):
        """
        添加评分维度
        
        Args:
            dimension_name: 维度名称
            indicators: 指标及其权重 {指标名: 权重}
        """
        self.dimensions[dimension_name] = indicators
    
    def calculate_score(self, scores: Dict[str, Dict[str, float]]) -> Dict[str, float]:
        """
        计算加权评分
        
        Args:
            scores: 分数数据 {维度: {指标: 分数}}
        
        Returns:
            各维度得分和总分
        """
        dimension_scores = {}
        
        for dim_name, indicators in self.dimensions.items():
            dim_scores = scores.get(dim_name, {})
            if dim_scores and indicators:
                # 计算该维度的加权平均分
                total_weight = sum(indicators.values())
                if total_weight > 0:
                    weighted_sum = sum(
                        dim_scores.get(ind, 0) * weight 
                        for ind, weight in indicators.items()
                    )
                    dimension_scores[dim_name] = weighted_sum / total_weight
                else:
                    dimension_scores[dim_name] = 0.0
            else:
                dimension_scores[dim_name] = 0.0
        
        # 计算总分（各维度平均分）
        if dimension_scores:
            total_score = sum(dimension_scores.values()) / len(dimension_scores)
        else:
            total_score = 0.0
        
        dimension_scores['total'] = total_score
        return dimension_scores


# =============================================================================
# 增值评分模型
# =============================================================================

class ValueAddedScoringModel:
    """
    增值评分模型
    
    评估学习者在一定时期内的能力提升和价值增值
    """
    
    def __init__(self):
        self.scoring_algo = ScoringAlgorithm()
    
    def calculate_absolute_value_added(
        self, 
        initial_scores: Dict[str, float], 
        current_scores: Dict[str, float]
    ) -> Dict[str, float]:
        """
        计算绝对增值
        
        Args:
            initial_scores: 初始分数
            current_scores: 当前分数
        
        Returns:
            各维度增值
        """
        value_added = {}
        all_dims = set(initial_scores.keys()) | set(current_scores.keys())
        
        for dim in all_dims:
            initial = initial_scores.get(dim, 0)
            current = current_scores.get(dim, 0)
            value_added[dim] = current - initial
        
        return value_added
    
    def calculate_relative_value_added(
        self, 
        value_added: Dict[str, float], 
        initial_scores: Dict[str, float]
    ) -> Dict[str, float]:
        """
        计算相对增值（百分比）
        
        Args:
            value_added: 绝对增值
            initial_scores: 初始分数
        
        Returns:
            各维度相对增值百分比
        """
        relative_added = {}
        
        for dim, added in value_added.items():
            initial = initial_scores.get(dim, 0)
            if initial > 0:
                relative_added[dim] = (added / initial) * 100
            else:
                # 如果初始为0，使用绝对增值作为相对增值
                relative_added[dim] = added
        
        return relative_added
    
    def calculate_comprehensive_value_added(
        self, 
        learner_profile: LearnerProfile,
        period_days: int = 30
    ) -> ValueAddedMetrics:
        """
        计算综合增值指标
        
        Args:
            learner_profile: 学习者档案
            period_days: 评估周期（天）
        
        Returns:
            综合增值指标
        """
        # 获取能力增值
        current_scores = learner_profile.current_ability.get_dimension_scores()
        initial_scores = learner_profile.initial_ability.get_dimension_scores()
        
        ability_added = self.calculate_absolute_value_added(initial_scores, current_scores)
        
        # 计算知识增值
        knowledge_added = self._calculate_knowledge_value_added(learner_profile)
        
        # 计算技能增值
        skill_added = self._calculate_skill_value_added(learner_profile)
        
        # 计算新掌握概念数量
        new_concepts = self._count_new_concepts(learner_profile)
        
        # 计算掌握度提升
        mastery_improvement = sum(knowledge_added.values()) / len(knowledge_added) if knowledge_added else 0
        
        return ValueAddedMetrics(
            ability_value_added=ability_added,
            knowledge_value_added=knowledge_added,
            skill_value_added=skill_added,
            new_concepts_count=new_concepts,
            mastery_improvement=mastery_improvement
        )
    
    def _calculate_knowledge_value_added(self, learner_profile: LearnerProfile) -> Dict[str, float]:
        """计算知识增值"""
        # 基于知识状态的变化计算增值
        added = {}
        # 这里简化处理，实际应根据历史记录计算
        for concept, mastery in learner_profile.knowledge_state.items():
            # 假设初始掌握度为0或较低
            initial_mastery = 0  # 实际应从历史记录获取
            added[concept] = mastery - initial_mastery
        return added
    
    def _calculate_skill_value_added(self, learner_profile: LearnerProfile) -> Dict[str, float]:
        """计算技能增值"""
        # 基于技能表现的变化计算增值
        return {
            'problem_solving': 0.0,  # 实际应根据历史记录计算
            'reasoning': 0.0,
            'communication': 0.0
        }
    
    def _count_new_concepts(self, learner_profile: LearnerProfile) -> int:
        """统计新掌握的概念数量"""
        # 简化处理：统计掌握度超过阈值的单元
        threshold = 60.0
        return sum(1 for m in learner_profile.knowledge_state.values() if m >= threshold)


# =============================================================================
# 表现性评分模型
# =============================================================================

class PerformanceScoringModel:
    """
    表现性评分模型
    
    评估学习者在真实任务情境中的表现
    """
    
    def __init__(self):
        self.scoring_algo = ScoringAlgorithm()
    
    def assess_operational_ability(
        self,
        problem_analysis_data: Dict[str, Any],
        method_selection_data: Dict[str, Any],
        execution_data: Dict[str, Any],
        verification_data: Dict[str, Any]
    ) -> OperationalAbility:
        """
        评估操作能力
        
        Args:
            problem_analysis_data: 问题分析过程数据
            method_selection_data: 方法选择过程数据
            execution_data: 执行过程数据
            verification_data: 验证过程数据
        
        Returns:
            操作能力评估结果
        """
        # 评估问题分析能力
        analysis_score = self._assess_problem_analysis(problem_analysis_data)
        
        # 评估方法选择能力
        method_score = self._assess_method_selection(method_selection_data)
        
        # 评估执行能力
        execution_score = self._assess_execution(execution_data)
        
        # 评估验证能力
        verification_score = self._assess_verification(verification_data)
        
        return OperationalAbility(
            problem_analysis=analysis_score,
            method_selection=method_score,
            execution=execution_score,
            verification=verification_score
        )
    
    def _assess_problem_analysis(self, data: Dict[str, Any]) -> float:
        """评估问题分析能力"""
        # 评估因素：理解准确性、分解能力、关键信息识别
        accuracy = data.get('understanding_accuracy', 0)
        decomposition = data.get('decomposition_ability', 0)
        info_identification = data.get('info_identification', 0)
        
        return (accuracy * 0.4 + decomposition * 0.3 + info_identification * 0.3)
    
    def _assess_method_selection(self, data: Dict[str, Any]) -> float:
        """评估方法选择能力"""
        # 评估因素：适用性判断、选择合理性、方法组合
        applicability = data.get('applicability_judgment', 0)
        rationality = data.get('selection_rationality', 0)
        combination = data.get('method_combination', 0)
        
        return (applicability * 0.4 + rationality * 0.4 + combination * 0.2)
    
    def _assess_execution(self, data: Dict[str, Any]) -> float:
        """评估执行能力"""
        # 评估因素：准确性、效率、规范性
        accuracy = data.get('accuracy', 0)
        efficiency = data.get('efficiency', 0)
        standardization = data.get('standardization', 0)
        
        return (accuracy * 0.5 + efficiency * 0.3 + standardization * 0.2)
    
    def _assess_verification(self, data: Dict[str, Any]) -> float:
        """评估验证能力"""
        # 评估因素：正确性检查、合理性验证、优化能力
        correctness_check = data.get('correctness_check', 0)
        rationality_check = data.get('rationality_check', 0)
        optimization = data.get('optimization_ability', 0)
        
        return (correctness_check * 0.4 + rationality_check * 0.4 + optimization * 0.2)
    
    def assess_creative_product(
        self,
        product_data: Dict[str, Any],
        requirements: Dict[str, Any]
    ) -> CreativeProduct:
        """
        评估创造产品
        
        Args:
            product_data: 产品数据
            requirements: 需求规格
        
        Returns:
            产品评估结果
        """
        # 评估创新性
        innovation = self._assess_innovation(product_data)
        
        # 评估实用性
        practicality = self._assess_practicality(product_data, requirements)
        
        # 评估技术性
        technical = self._assess_technical_quality(product_data)
        
        # 评估完整性
        completeness = self._assess_completeness(product_data, requirements)
        
        return CreativeProduct(
            innovation=innovation,
            practicality=practicality,
            technical_quality=technical,
            completeness=completeness
        )
    
    def _assess_innovation(self, product_data: Dict[str, Any]) -> float:
        """评估创新性"""
        novelty = product_data.get('novelty', 0)
        method_innovation = product_data.get('method_innovation', 0)
        application_innovation = product_data.get('application_innovation', 0)
        
        return (novelty * 0.4 + method_innovation * 0.3 + application_innovation * 0.3)
    
    def _assess_practicality(self, product_data: Dict[str, Any], requirements: Dict[str, Any]) -> float:
        """评估实用性"""
        usability = product_data.get('usability', 0)
        value = product_data.get('application_value', 0)
        requirement_meeting = product_data.get('requirement_meeting', 0)
        
        return (usability * 0.3 + value * 0.4 + requirement_meeting * 0.3)
    
    def _assess_technical_quality(self, product_data: Dict[str, Any]) -> float:
        """评估技术性"""
        implementation_quality = product_data.get('implementation_quality', 0)
        technical_difficulty = product_data.get('technical_difficulty', 0)
        standard_compliance = product_data.get('standard_compliance', 0)
        
        return (implementation_quality * 0.5 + technical_difficulty * 0.2 + standard_compliance * 0.3)
    
    def _assess_completeness(self, product_data: Dict[str, Any], requirements: Dict[str, Any]) -> float:
        """评估完整性"""
        product_completion = product_data.get('product_completion', 0)
        function_completeness = product_data.get('function_completeness', 0)
        documentation_completeness = product_data.get('documentation_completeness', 0)
        
        return (product_completion * 0.4 + function_completeness * 0.4 + documentation_completeness * 0.2)


# =============================================================================
# 发散思维评分模型
# =============================================================================

class DivergentThinkingScoringModel:
    """
    发散思维评分模型
    
    评估学习者的创造性思维能力
    """
    
    def assess_creativity(
        self,
        creative_output: Dict[str, Any],
        reference_data: Optional[Dict[str, Any]] = None
    ) -> CreativityMetrics:
        """
        评估创造性
        
        Args:
            creative_output: 创造性产出数据
            reference_data: 参考数据（用于比较独特性）
        
        Returns:
            创造性评估指标
        """
        # 评估流畅性
        fluency = self._assess_fluency(creative_output)
        
        # 评估灵活性
        flexibility = self._assess_flexibility(creative_output)
        
        # 评估独创性
        originality = self._assess_originality(creative_output, reference_data)
        
        # 评估精细性
        elaboration = self._assess_elaboration(creative_output)
        
        return CreativityMetrics(
            fluency=fluency,
            flexibility=flexibility,
            originality=originality,
            elaboration=elaboration
        )
    
    def _assess_fluency(self, creative_output: Dict[str, Any]) -> float:
        """评估流畅性（想法数量）"""
        idea_count = creative_output.get('idea_count', 0)
        generation_speed = creative_output.get('generation_speed', 0)  # 想法/分钟
        diversity = creative_output.get('idea_diversity', 0)
        
        # 标准化：假设最多20个想法，速度5个/分钟为满分
        count_score = min(100, idea_count * 5)
        speed_score = min(100, generation_speed * 20)
        
        return (count_score * 0.5 + speed_score * 0.3 + diversity * 0.2)
    
    def _assess_flexibility(self, creative_output: Dict[str, Any]) -> float:
        """评估灵活性（想法类型多样性）"""
        category_count = creative_output.get('category_count', 0)
        perspective_diversity = creative_output.get('perspective_diversity', 0)
        thinking_shifts = creative_output.get('thinking_shifts', 0)
        
        # 标准化：假设最多10个类别
        category_score = min(100, category_count * 10)
        shift_score = min(100, thinking_shifts * 20)
        
        return (category_score * 0.5 + perspective_diversity * 0.3 + shift_score * 0.2)
    
    def _assess_originality(
        self, 
        creative_output: Dict[str, Any], 
        reference_data: Optional[Dict[str, Any]]
    ) -> float:
        """评估独创性（想法独特性）"""
        uniqueness = creative_output.get('uniqueness_score', 0)
        novelty = creative_output.get('novelty_score', 0)
        rarity = creative_output.get('rarity_score', 0)
        
        # 如果有参考数据，计算客观独特性
        if reference_data:
            objective_uniqueness = self._calculate_objective_uniqueness(
                creative_output, reference_data
            )
        else:
            objective_uniqueness = uniqueness
        
        return (objective_uniqueness * 0.4 + novelty * 0.4 + rarity * 0.2)
    
    def _assess_elaboration(self, creative_output: Dict[str, Any]) -> float:
        """评估精细性（想法详细程度）"""
        detail_level = creative_output.get('detail_level', 0)
        refinement_level = creative_output.get('refinement_level', 0)
        depth = creative_output.get('depth_score', 0)
        
        return (detail_level * 0.4 + refinement_level * 0.3 + depth * 0.3)
    
    def _calculate_objective_uniqueness(
        self, 
        creative_output: Dict[str, Any], 
        reference_data: Dict[str, Any]
    ) -> float:
        """计算客观独特性（基于与参考数据的比较）"""
        ideas = set(creative_output.get('ideas', []))
        reference_ideas = set(reference_data.get('common_ideas', []))
        
        if not ideas:
            return 0.0
        
        # 计算不常见想法的比例
        unique_ideas = ideas - reference_ideas
        uniqueness_ratio = len(unique_ideas) / len(ideas) if ideas else 0
        
        return uniqueness_ratio * 100


# =============================================================================
# 过程性评分模型
# =============================================================================

class ProcessScoringModel:
    """
    过程性评分模型
    
    评估学习过程中的参与度和行为
    """
    
    def __init__(self):
        self.scoring_algo = ScoringAlgorithm()
    
    def assess_learning_participation(
        self, 
        learning_history: List[Dict[str, Any]],
        period_days: int = 7
    ) -> LearningParticipation:
        """
        评估学习参与度
        
        Args:
            learning_history: 学习历史记录
            period_days: 评估周期
        
        Returns:
            学习参与度指标
        """
        # 计算学习时间得分
        time_score = self._calculate_time_score(learning_history, period_days)
        
        # 计算学习频率得分
        frequency_score = self._calculate_frequency_score(learning_history, period_days)
        
        # 计算内容深度得分
        depth_score = self._calculate_depth_score(learning_history)
        
        # 计算内容广度得分
        breadth_score = self._calculate_breadth_score(learning_history)
        
        return LearningParticipation(
            study_time_score=time_score,
            study_frequency_score=frequency_score,
            content_depth_score=depth_score,
            content_breadth_score=breadth_score
        )
    
    def _calculate_time_score(self, history: List[Dict], period_days: int) -> float:
        """计算学习时间得分"""
        # 假设每周10小时为满分
        total_time = sum(record.get('duration', 0) for record in history)
        hours_per_week = (total_time / period_days) * 7 / 60  # 转换为小时/周
        return min(100, hours_per_week * 10)
    
    def _calculate_frequency_score(self, history: List[Dict], period_days: int) -> float:
        """计算学习频率得分"""
        # 假设每周5次为满分
        unique_days = len(set(record.get('date') for record in history))
        frequency_per_week = (unique_days / period_days) * 7
        return min(100, frequency_per_week * 20)
    
    def _calculate_depth_score(self, history: List[Dict]) -> float:
        """计算内容深度得分"""
        # 基于学习内容的深度评估
        depths = [record.get('content_depth', 0) for record in history]
        return sum(depths) / len(depths) if depths else 0
    
    def _calculate_breadth_score(self, history: List[Dict]) -> float:
        """计算内容广度得分"""
        # 基于学习内容的多样性评估
        topics = set()
        for record in history:
            topics.update(record.get('topics', []))
        # 假设10个不同主题为满分
        return min(100, len(topics) * 10)
    
    def assess_learning_initiative(self, learning_history: List[Dict[str, Any]]) -> LearningInitiative:
        """评估学习主动性"""
        # 主动学习
        active_learning = sum(1 for r in learning_history if r.get('is_active_learning', False))
        active_learning_score = min(100, active_learning * 10)
        
        # 主动提问
        questions_asked = sum(r.get('questions_asked', 0) for r in learning_history)
        questioning_score = min(100, questions_asked * 20)
        
        # 主动探索
        explorations = sum(1 for r in learning_history if r.get('is_exploration', False))
        exploration_score = min(100, explorations * 15)
        
        # 主动反思
        reflections = sum(1 for r in learning_history if r.get('is_reflection', False))
        reflection_score = min(100, reflections * 20)
        
        return LearningInitiative(
            active_learning_score=active_learning_score,
            active_questioning_score=questioning_score,
            active_exploration_score=exploration_score,
            active_reflection_score=reflection_score
        )
    
    def assess_learning_progress(
        self, 
        learner_profile: LearnerProfile,
        learning_path: Dict[str, Any]
    ) -> LearningProgress:
        """评估学习进度"""
        # 内容完成度
        completed = len([c for c in learner_profile.knowledge_state.values() if c > 0])
        total = len(learning_path.get('content_items', []))
        completion = (completed / total * 100) if total > 0 else 0
        
        # 知识掌握度
        mastery = sum(learner_profile.knowledge_state.values()) / len(learner_profile.knowledge_state) if learner_profile.knowledge_state else 0
        
        # 能力提升度（简化计算）
        current_score = learner_profile.current_ability.calculate_overall_score()
        initial_score = learner_profile.initial_ability.calculate_overall_score()
        improvement = current_score - initial_score
        
        # 目标达成度
        goals = learning_path.get('goals', [])
        achieved = sum(1 for g in goals if g.get('achieved', False))
        goal_achievement = (achieved / len(goals) * 100) if goals else 0
        
        return LearningProgress(
            content_completion=completion,
            knowledge_mastery=mastery,
            ability_improvement=improvement,
            goal_achievement=goal_achievement
        )


# =============================================================================
# 评分引擎主类
# =============================================================================

class ScoringEngine:
    """
    评分引擎主类
    
    整合所有评分模型，提供统一的评分接口
    """
    
    def __init__(self):
        self.weighted_model = WeightedScoringModel(name="default")
        self.value_added_model = ValueAddedScoringModel()
        self.performance_model = PerformanceScoringModel()
        self.divergent_model = DivergentThinkingScoringModel()
        self.process_model = ProcessScoringModel()
        self.scoring_algo = ScoringAlgorithm()
    
    def evaluate_mathematical_ability(
        self, 
        ability_profile: MathematicalAbilityProfile
    ) -> Dict[str, Any]:
        """
        评估数学能力
        
        Args:
            ability_profile: 数学能力档案
        
        Returns:
            评估结果
        """
        dimension_scores = ability_profile.get_dimension_scores()
        overall_score = ability_profile.calculate_overall_score()
        level = EvaluationCriteria.get_level(overall_score)
        
        return {
            'dimension_scores': dimension_scores,
            'overall_score': overall_score,
            'level': level,
            'level_description': EvaluationCriteria.get_level_description(level),
            'strengths': ability_profile.identify_strengths(),
            'weaknesses': ability_profile.identify_weaknesses()
        }
    
    def evaluate_process(
        self, 
        learner_profile: LearnerProfile,
        learning_history: List[Dict[str, Any]],
        learning_path: Dict[str, Any],
        period_days: int = 7
    ) -> Dict[str, Any]:
        """
        进行过程性评价
        
        Args:
            learner_profile: 学习者档案
            learning_history: 学习历史
            learning_path: 学习路径
            period_days: 评估周期
        
        Returns:
            过程性评价结果
        """
        participation = self.process_model.assess_learning_participation(
            learning_history, period_days
        )
        initiative = self.process_model.assess_learning_initiative(learning_history)
        progress = self.process_model.assess_learning_progress(learner_profile, learning_path)
        
        return {
            'participation': {
                'score': participation.calculate_score(),
                'details': {
                    'study_time': participation.study_time_score,
                    'study_frequency': participation.study_frequency_score,
                    'content_depth': participation.content_depth_score,
                    'content_breadth': participation.content_breadth_score
                }
            },
            'initiative': {
                'score': initiative.calculate_score(),
                'details': {
                    'active_learning': initiative.active_learning_score,
                    'active_questioning': initiative.active_questioning_score,
                    'active_exploration': initiative.active_exploration_score,
                    'active_reflection': initiative.active_reflection_score
                }
            },
            'progress': {
                'score': progress.calculate_score(),
                'details': {
                    'content_completion': progress.content_completion,
                    'knowledge_mastery': progress.knowledge_mastery,
                    'ability_improvement': progress.ability_improvement,
                    'goal_achievement': progress.goal_achievement
                }
            }
        }
    
    def evaluate_value_added(
        self, 
        learner_profile: LearnerProfile,
        period_days: int = 30
    ) -> Dict[str, Any]:
        """
        进行增值评价
        
        Args:
            learner_profile: 学习者档案
            period_days: 评估周期
        
        Returns:
            增值评价结果
        """
        value_added = self.value_added_model.calculate_comprehensive_value_added(
            learner_profile, period_days
        )
        
        return {
            'ability_value_added': value_added.ability_value_added,
            'knowledge_value_added': value_added.knowledge_value_added,
            'skill_value_added': value_added.skill_value_added,
            'overall_value_added': value_added.calculate_overall_value_added(),
            'new_concepts_count': value_added.new_concepts_count,
            'mastery_improvement': value_added.mastery_improvement
        }


# 导出所有类和函数
__all__ = [
    'ScoringAlgorithm',
    'WeightedScoringModel',
    'ValueAddedScoringModel',
    'PerformanceScoringModel',
    'DivergentThinkingScoringModel',
    'ProcessScoringModel',
    'ScoringEngine'
]
