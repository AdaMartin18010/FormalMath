"""
HCD（层级认知诊断）算法实现
基于层次约束感知的认知诊断框架
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

from app.models.knowledge_graph import KnowledgeGraph, KnowledgeLevel, ConstraintType
from app.models.question import Question
from app.models.diagnosis import DiagnosisResponse
from app.core.config import settings


class ConstraintViolationPolicy(str, Enum):
    """约束违反处理策略"""
    SOFT = "soft"      # 软约束：惩罚
    HARD = "hard"      # 硬约束：强制满足


@dataclass
class HCDResult:
    """HCD诊断结果"""
    knowledge_state: Dict[str, float]  # 知识点掌握概率
    ability_level: Dict[int, float]    # L0-L3各层次能力
    confidence: Dict[str, float]       # 置信度
    iterations: int                    # 迭代次数
    converged: bool                    # 是否收敛


class HCDEngine:
    """
    层级认知诊断引擎 (Hierarchical Cognitive Diagnosis)
    
    基于层次约束感知的认知诊断框架，考虑知识层次间的约束关系，
    利用层次约束提高诊断准确性。
    """
    
    def __init__(
        self,
        knowledge_graph: KnowledgeGraph,
        constraint_policy: ConstraintViolationPolicy = ConstraintViolationPolicy.SOFT
    ):
        self.knowledge_graph = knowledge_graph
        self.constraint_policy = constraint_policy
        self.max_iterations = settings.HCD_MAX_ITERATIONS
        self.convergence_threshold = settings.HCD_CONVERGENCE_THRESHOLD
        self.learning_rate = settings.HCD_LEARNING_RATE
        
        # 构建层次结构缓存
        self._build_level_cache()
    
    def _build_level_cache(self):
        """构建层次结构缓存"""
        self.level_nodes = {0: [], 1: [], 2: [], 3: []}
        for node_id, node in self.knowledge_graph.nodes.items():
            self.level_nodes[node.level].append(node_id)
        
        # 构建先修关系缓存
        self.prereq_map: Dict[str, List[str]] = {}
        for edge in self.knowledge_graph.edges.values():
            if edge.constraint_type == ConstraintType.PREREQUISITE:
                if edge.target_id not in self.prereq_map:
                    self.prereq_map[edge.target_id] = []
                self.prereq_map[edge.target_id].append(edge.source_id)
    
    def diagnose(
        self,
        responses: List[DiagnosisResponse],
        questions: Dict[str, Question],
        prior_knowledge: Optional[Dict[str, float]] = None
    ) -> HCDResult:
        """
        执行层级认知诊断
        
        Args:
            responses: 用户答题响应列表
            questions: 题目字典 (question_id -> Question)
            prior_knowledge: 先验知识状态
            
        Returns:
            HCDResult: 诊断结果
        """
        # 1. 初始化知识状态
        knowledge_state = self._initialize_knowledge_state(prior_knowledge)
        
        # 2. 构建答题矩阵
        response_matrix = self._build_response_matrix(responses, questions)
        
        # 3. 迭代优化
        prev_state = knowledge_state.copy()
        converged = False
        iteration = 0
        
        for iteration in range(self.max_iterations):
            # 3.1 基于IRT模型更新知识状态
            knowledge_state = self._update_knowledge_state_irt(
                knowledge_state, response_matrix, questions
            )
            
            # 3.2 基于DINA模型精细调整
            knowledge_state = self._refine_with_dina(
                knowledge_state, response_matrix, questions
            )
            
            # 3.3 应用层次约束
            knowledge_state = self._apply_hierarchy_constraints(knowledge_state)
            
            # 3.4 检查收敛
            if self._check_convergence(prev_state, knowledge_state):
                converged = True
                break
            
            prev_state = knowledge_state.copy()
        
        # 4. 评估能力水平
        ability_level = self._assess_ability_level(knowledge_state)
        
        # 5. 计算置信度
        confidence = self._calculate_confidence(knowledge_state, response_matrix, questions)
        
        return HCDResult(
            knowledge_state=knowledge_state,
            ability_level=ability_level,
            confidence=confidence,
            iterations=iteration + 1,
            converged=converged
        )
    
    def _initialize_knowledge_state(
        self,
        prior_knowledge: Optional[Dict[str, float]] = None
    ) -> Dict[str, float]:
        """初始化知识状态"""
        knowledge_state = {}
        
        for node_id in self.knowledge_graph.nodes:
            if prior_knowledge and node_id in prior_knowledge:
                knowledge_state[node_id] = np.clip(prior_knowledge[node_id], 0.0, 1.0)
            else:
                # 默认先验概率
                knowledge_state[node_id] = 0.5
        
        return knowledge_state
    
    def _build_response_matrix(
        self,
        responses: List[DiagnosisResponse],
        questions: Dict[str, Question]
    ) -> Dict[str, Tuple[Any, bool]]:
        """构建答题矩阵"""
        response_matrix = {}
        
        for resp in responses:
            if resp.question_id in questions:
                question = questions[resp.question_id]
                is_correct = self._check_answer(resp.answer, question.correct_answer)
                response_matrix[resp.question_id] = (resp.answer, is_correct)
        
        return response_matrix
    
    def _check_answer(self, user_answer: any, correct_answer: any) -> bool:
        """检查答案是否正确"""
        if isinstance(correct_answer, list):
            return user_answer in correct_answer if not isinstance(user_answer, list) else set(user_answer) == set(correct_answer)
        return str(user_answer).strip().lower() == str(correct_answer).strip().lower()
    
    def _update_knowledge_state_irt(
        self,
        knowledge_state: Dict[str, float],
        response_matrix: Dict[str, Tuple[Any, bool]],
        questions: Dict[str, Question]
    ) -> Dict[str, float]:
        """
        基于IRT模型更新知识状态
        
        使用2PL-IRT模型计算知识点掌握概率
        P(θ) = 1 / (1 + exp(-a(θ - b)))
        """
        new_state = knowledge_state.copy()
        
        # 计算每个知识点的更新
        for node_id in self.knowledge_graph.nodes:
            related_responses = []
            
            # 找到关联该知识点的所有题目
            for qid, (_, is_correct) in response_matrix.items():
                if qid in questions:
                    question = questions[qid]
                    if node_id in question.q_matrix:
                        weight = question.q_matrix[node_id]
                        related_responses.append((is_correct, question.difficulty, 
                                                  question.discrimination, weight))
            
            if not related_responses:
                continue
            
            # 计算梯度更新
            current_theta = knowledge_state[node_id]
            gradient = 0.0
            
            for is_correct, b, a, w in related_responses:
                # IRT概率
                prob = 1 / (1 + np.exp(-a * (current_theta - b)))
                
                # 梯度（对数似然）
                if is_correct:
                    gradient += a * (1 - prob) * w
                else:
                    gradient -= a * prob * w
            
            # 更新知识状态
            new_theta = current_theta + self.learning_rate * gradient / len(related_responses)
            new_state[node_id] = np.clip(new_theta, 0.0, 1.0)
        
        return new_state
    
    def _refine_with_dina(
        self,
        knowledge_state: Dict[str, float],
        response_matrix: Dict[str, Tuple[Any, bool]],
        questions: Dict[str, Question]
    ) -> Dict[str, float]:
        """
        基于DINA模型精细调整
        
        DINA模型考虑猜测和失误参数
        """
        new_state = knowledge_state.copy()
        
        # DINA参数
        guess_prob = 0.2  # 猜测概率
        slip_prob = 0.1   # 失误概率
        
        for node_id in self.knowledge_graph.nodes:
            # 找到关联该知识点的所有题目
            correct_count = 0
            total_weight = 0
            
            for qid, (_, is_correct) in response_matrix.items():
                if qid in questions:
                    question = questions[qid]
                    if node_id in question.q_matrix:
                        weight = question.q_matrix[node_id]
                        
                        # DINA调整
                        if is_correct:
                            # 答对可能来自掌握或猜测
                            correct_count += weight * (1 - guess_prob)
                        else:
                            # 答错可能来自未掌握或失误
                            correct_count += weight * slip_prob
                        
                        total_weight += weight
            
            if total_weight > 0:
                # 结合IRT结果和DINA调整
                dina_estimate = correct_count / total_weight
                # 加权平均
                new_state[node_id] = np.clip(
                    0.7 * knowledge_state[node_id] + 0.3 * dina_estimate,
                    0.0, 1.0
                )
        
        return new_state
    
    def _apply_hierarchy_constraints(
        self,
        knowledge_state: Dict[str, float]
    ) -> Dict[str, float]:
        """
        应用层次约束
        
        核心约束规则：
        1. 先修约束：L1需要先掌握L0，以此类推
        2. 能力约束：高级层次的能力评估需要考虑低层次的能力
        """
        new_state = knowledge_state.copy()
        
        # 1. 应用先修约束
        for node_id, prereq_ids in self.prereq_map.items():
            if prereq_ids and node_id in new_state:
                # 计算先修节点的平均掌握度
                prereq_mastery = [new_state.get(pid, 0.0) for pid in prereq_ids]
                avg_prereq_mastery = sum(prereq_mastery) / len(prereq_mastery)
                
                # 先修约束：后修节点的掌握度不应超过先修节点
                if self.constraint_policy == ConstraintViolationPolicy.HARD:
                    new_state[node_id] = min(new_state[node_id], avg_prereq_mastery)
                else:
                    # 软约束：惩罚违反
                    if new_state[node_id] > avg_prereq_mastery:
                        penalty = 0.1 * (new_state[node_id] - avg_prereq_mastery)
                        new_state[node_id] = max(0.0, new_state[node_id] - penalty)
        
        # 2. 应用层次能力约束
        for level in range(1, 4):  # L1, L2, L3
            lower_level = level - 1
            
            level_nodes = self.level_nodes[level]
            lower_level_nodes = self.level_nodes[lower_level]
            
            if not level_nodes or not lower_level_nodes:
                continue
            
            # 计算低层次的平均掌握度
            lower_mastery = [new_state.get(nid, 0.0) for nid in lower_level_nodes]
            avg_lower_mastery = sum(lower_mastery) / len(lower_mastery)
            
            # 高层次能力不应显著超过低层次
            for node_id in level_nodes:
                if node_id in new_state:
                    max_allowed = avg_lower_mastery + 0.2  # 允许小幅超出
                    if new_state[node_id] > max_allowed:
                        # 软惩罚
                        new_state[node_id] = 0.8 * new_state[node_id] + 0.2 * max_allowed
        
        return new_state
    
    def _check_convergence(
        self,
        prev_state: Dict[str, float],
        curr_state: Dict[str, float]
    ) -> bool:
        """检查是否收敛"""
        if not prev_state or not curr_state:
            return False
        
        total_diff = 0.0
        count = 0
        
        for node_id in prev_state:
            if node_id in curr_state:
                total_diff += abs(prev_state[node_id] - curr_state[node_id])
                count += 1
        
        if count == 0:
            return False
        
        avg_diff = total_diff / count
        return avg_diff < self.convergence_threshold
    
    def _assess_ability_level(self, knowledge_state: Dict[str, float]) -> Dict[int, float]:
        """
        评估各层次能力水平
        
        计算L0-L3各层次的平均掌握度
        """
        ability_level = {0: 0.0, 1: 0.0, 2: 0.0, 3: 0.0}
        
        for level in range(4):
            nodes = self.level_nodes[level]
            if not nodes:
                continue
            
            mastery_scores = [knowledge_state.get(nid, 0.0) for nid in nodes]
            ability_level[level] = sum(mastery_scores) / len(mastery_scores)
        
        return ability_level
    
    def _calculate_confidence(
        self,
        knowledge_state: Dict[str, float],
        response_matrix: Dict[str, Tuple[Any, bool]],
        questions: Dict[str, Question]
    ) -> Dict[str, float]:
        """计算诊断置信度"""
        confidence = {}
        
        for node_id in self.knowledge_graph.nodes:
            # 基于答题数量计算置信度
            related_count = 0
            
            for qid in response_matrix:
                if qid in questions:
                    question = questions[qid]
                    if node_id in question.q_matrix:
                        related_count += 1
            
            # 答题越多，置信度越高（饱和在0.9）
            base_confidence = min(0.9, related_count * 0.15)
            
            # 知识状态接近0.5时置信度较低（不确定性最大）
            state_uncertainty = 1.0 - 2.0 * abs(knowledge_state[node_id] - 0.5)
            
            confidence[node_id] = base_confidence * (1.0 - 0.3 * state_uncertainty)
        
        return confidence
    
    def get_weak_areas(
        self,
        result: HCDResult,
        threshold: float = 0.6
    ) -> List[Tuple[str, float]]:
        """
        识别薄弱环节
        
        Args:
            result: 诊断结果
            threshold: 掌握度阈值
            
        Returns:
            薄弱环节列表 (知识点ID, 掌握度)
        """
        weak_areas = []
        
        for node_id, mastery in result.knowledge_state.items():
            if mastery < threshold:
                weak_areas.append((node_id, mastery))
        
        # 按掌握度排序
        weak_areas.sort(key=lambda x: x[1])
        return weak_areas
