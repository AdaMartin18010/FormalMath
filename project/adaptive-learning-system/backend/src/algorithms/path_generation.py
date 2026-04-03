"""
学习路径生成算法
基于知识图谱的个性化路径规划算法
"""

import heapq
from typing import Dict, List, Optional, Set, Tuple, Any
from dataclasses import dataclass, field
import uuid
from datetime import datetime, timedelta

from models.knowledge_graph import KnowledgeGraph, ConceptNode, RelationEdge, RelationType, DifficultyLevel
from models.learner import LearnerProfile, LearningStyle, AbilityLevel
from models.learning_path import LearningPath, PathNode, NodeStatus, PathStatus


@dataclass
class PathConstraints:
    """路径约束条件"""
    max_total_time_hours: float = 100.0  # 最大总时长
    preferred_difficulty_range: Tuple[float, float] = (0.5, 1.5)  # 难度偏好范围
    learning_style_weight: float = 0.3  # 学习风格权重
    diversity_weight: float = 0.2  # 多样性权重
    min_mastery_threshold: float = 0.7  # 最小掌握阈值
    target_completion_date: Optional[datetime] = None  # 目标完成日期
    preferred_path_length: Optional[int] = None  # 偏好的路径长度


class PathScorer:
    """路径评分器"""
    
    def __init__(self, learner_profile: LearnerProfile, constraints: PathConstraints):
        self.learner = learner_profile
        self.constraints = constraints
    
    def calculate_node_score(self, concept: ConceptNode, position: int, total_nodes: int) -> float:
        """计算单个节点得分"""
        scores = []
        
        # 1. 学习风格匹配度
        style_match = self._calculate_style_match(concept)
        scores.append(style_match * self.constraints.learning_style_weight)
        
        # 2. 难度适宜度
        difficulty_fit = self._calculate_difficulty_fit(concept, position, total_nodes)
        scores.append(difficulty_fit * 0.3)
        
        # 3. 先验知识加分
        prior_bonus = self._calculate_prior_knowledge_bonus(concept)
        scores.append(prior_bonus * 0.2)
        
        # 4. 时间效率
        time_efficiency = self._calculate_time_efficiency(concept)
        scores.append(time_efficiency * 0.2)
        
        return sum(scores)
    
    def _calculate_style_match(self, concept: ConceptNode) -> float:
        """计算学习风格匹配度"""
        style = self.learner.learning_style.dominant_style
        resources = concept.get_resources_by_style(style.value)
        if not resources and concept.resources:
            return 0.5
        return 1.0 if resources else 0.3
    
    def _calculate_difficulty_fit(self, concept: ConceptNode, position: int, total_nodes: int) -> float:
        """计算难度适宜度"""
        # 根据学习者能力确定期望难度
        overall_ability = self.learner.calculate_overall_ability()
        
        # 渐进式难度曲线
        expected_progress = position / max(total_nodes, 1)
        expected_difficulty = overall_ability + expected_progress * 0.5
        
        # 计算实际难度与期望难度的匹配度
        concept_difficulty = concept.difficulty.value / 4.0  # 归一化到0-1
        diff = abs(concept_difficulty - expected_difficulty)
        return max(0, 1 - diff * 2)
    
    def _calculate_prior_knowledge_bonus(self, concept: ConceptNode) -> float:
        """计算先验知识加分"""
        mastery = self.learner.get_concept_mastery(concept.concept_id)
        if mastery >= self.constraints.min_mastery_threshold:
            return 0.2  # 已掌握概念有轻微加分（复习价值）
        elif mastery > 0:
            return 0.5  # 部分掌握概念有中等加分
        return 1.0  # 新概念有最高加分
    
    def _calculate_time_efficiency(self, concept: ConceptNode) -> float:
        """计算时间效率"""
        # 更短时间的概念得分更高
        max_time = 240  # 最大参考时间（分钟）
        return max(0, 1 - concept.estimated_time_minutes / max_time)
    
    def calculate_path_score(self, path: LearningPath) -> float:
        """计算整体路径得分"""
        scores = []
        
        # 1. 平滑度得分
        smoothness = self._calculate_smoothness(path)
        scores.append(smoothness * 0.25)
        
        # 2. 多样性得分
        diversity = self._calculate_diversity(path)
        scores.append(diversity * self.constraints.diversity_weight)
        
        # 3. 匹配度得分
        match_score = self._calculate_match_score(path)
        scores.append(match_score * 0.3)
        
        # 4. 可行性得分
        feasibility = self._calculate_feasibility(path)
        scores.append(feasibility * 0.25)
        
        return sum(scores)
    
    def _calculate_smoothness(self, path: LearningPath) -> float:
        """计算路径平滑度（难度连续性）"""
        if len(path.difficulty_curve) < 2:
            return 1.0
        
        # 计算难度跳跃
        jumps = [
            abs(path.difficulty_curve[i] - path.difficulty_curve[i-1])
            for i in range(1, len(path.difficulty_curve))
        ]
        avg_jump = sum(jumps) / len(jumps)
        return max(0, 1 - avg_jump * 2)
    
    def _calculate_diversity(self, path: LearningPath) -> float:
        """计算路径多样性"""
        # 基于MSC编码的多样性
        msc_codes = [path.nodes[nid].concept_id for nid in path.node_order]
        if len(msc_codes) <= 1:
            return 1.0
        
        # 计算不同MSC前缀的数量
        prefixes = set(code.split('.')[0] if '.' in code else code[:2] for code in msc_codes)
        return len(prefixes) / len(msc_codes)
    
    def _calculate_match_score(self, path: LearningPath) -> float:
        """计算路径与学习者的匹配度"""
        if not path.nodes:
            return 0.0
        
        total_score = 0.0
        for i, node_id in enumerate(path.node_order):
            node = path.nodes[node_id]
            concept = ConceptNode(concept_id=node.concept_id, difficulty=DifficultyLevel(int(node.difficulty)))
            node_score = self.calculate_node_score(concept, i, len(path.node_order))
            total_score += node_score
        
        return total_score / len(path.nodes)
    
    def _calculate_feasibility(self, path: LearningPath) -> float:
        """计算路径可行性"""
        # 检查总时间
        total_time = path.total_estimated_hours
        if total_time > self.constraints.max_total_time_hours:
            return 0.0
        
        time_score = 1 - (total_time / self.constraints.max_total_time_hours)
        
        # 检查目标日期
        if self.constraints.target_completion_date:
            est_completion = path.get_estimated_completion()
            if est_completion and est_completion > self.constraints.target_completion_date:
                return 0.0
        
        return time_score


class AStarPathPlanner:
    """A*路径规划器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph, learner_profile: LearnerProfile):
        self.graph = knowledge_graph
        self.learner = learner_profile
    
    def find_optimal_path(
        self,
        start_concepts: List[str],
        goal_concepts: List[str],
        constraints: PathConstraints
    ) -> Optional[LearningPath]:
        """使用A*算法寻找最优路径"""
        
        scorer = PathScorer(self.learner, constraints)
        
        # 获取所有需要学习的概念（包括先修）
        all_concepts = set()
        for goal in goal_concepts:
            prereqs = self.graph.get_prerequisite_graph(goal)
            all_concepts.update(prereqs)
        all_concepts.update(goal_concepts)
        
        # 过滤掉已掌握的概念
        concepts_to_learn = [
            c for c in all_concepts
            if not self.learner.is_concept_mastered(c, constraints.min_mastery_threshold)
        ]
        
        if not concepts_to_learn:
            return None
        
        # 拓扑排序确定学习顺序
        sorted_concepts = self.graph.topological_sort(concepts_to_learn)
        
        # 创建学习路径
        path = LearningPath(
            learner_id=self.learner.learner_id,
            name=f"个性化学习路径 - {datetime.now().strftime('%Y-%m-%d')}",
            description=f"基于A*算法生成的学习路径，目标概念: {', '.join(goal_concepts[:3])}...",
            goal=", ".join(goal_concepts),
            algorithm_used="A* with Topological Sort",
            constraints=constraints.__dict__
        )
        
        # 创建路径节点
        prev_node_id = None
        difficulty_curve = []
        total_time = 0
        
        for i, concept_id in enumerate(sorted_concepts):
            concept = self.graph.get_node(concept_id)
            if not concept:
                continue
            
            # 创建节点
            node = PathNode(
                concept_id=concept_id,
                sequence_number=i,
                status=NodeStatus.AVAILABLE if i == 0 else NodeStatus.LOCKED,
                estimated_duration=concept.estimated_time_minutes,
                mastery_threshold=constraints.min_mastery_threshold,
                difficulty=concept.difficulty.value,
                importance=self._calculate_importance(concept_id, goal_concepts)
            )
            
            # 设置先修关系
            if prev_node_id:
                node.prerequisites = [prev_node_id]
            
            # 获取推荐资源
            style = self.learner.learning_style.dominant_style
            node.recommended_resources = concept.get_resources_by_style(style.value)
            
            path.nodes[node.node_id] = node
            path.node_order.append(node.node_id)
            
            # 记录难度曲线
            difficulty_curve.append(concept.difficulty.value)
            total_time += concept.estimated_time_minutes / 60
            
            prev_node_id = node.node_id
        
        path.difficulty_curve = difficulty_curve
        path.total_estimated_hours = total_time
        path.diversity_score = scorer._calculate_diversity(path)
        
        # 解锁第一个节点
        if path.node_order:
            first_node = path.nodes[path.node_order[0]]
            first_node.status = NodeStatus.AVAILABLE
            first_node.planned_start = datetime.now()
            first_node.planned_end = datetime.now() + timedelta(minutes=first_node.estimated_duration)
        
        return path
    
    def _calculate_importance(self, concept_id: str, goal_concepts: List[str]) -> float:
        """计算概念对于目标的重要性"""
        if concept_id in goal_concepts:
            return 1.0
        
        # 检查是否是目标概念的先修
        for goal in goal_concepts:
            prereqs = self.graph.get_prerequisite_graph(goal)
            if concept_id in prereqs:
                return 0.8
        
        return 0.5
    
    def find_multiple_paths(
        self,
        start_concepts: List[str],
        goal_concepts: List[str],
        constraints: PathConstraints,
        num_paths: int = 3
    ) -> List[LearningPath]:
        """寻找多条备选路径"""
        paths = []
        
        # 主路径
        main_path = self.find_optimal_path(start_concepts, goal_concepts, constraints)
        if main_path:
            paths.append(main_path)
        
        # 通过调整约束生成备选路径
        for i in range(1, num_paths):
            # 创建略有不同的约束
            alt_constraints = PathConstraints(
                max_total_time_hours=constraints.max_total_time_hours * (0.8 + i * 0.2),
                learning_style_weight=constraints.learning_style_weight * (0.8 + i * 0.1),
                diversity_weight=constraints.diversity_weight * (0.8 + i * 0.1)
            )
            
            alt_path = self.find_optimal_path(start_concepts, goal_concepts, alt_constraints)
            if alt_path and alt_path.path_id != main_path.path_id if main_path else True:
                # 检查路径差异性
                if self._is_path_different(alt_path, paths):
                    paths.append(alt_path)
        
        return paths
    
    def _is_path_different(self, new_path: LearningPath, existing_paths: List[LearningPath], threshold: float = 0.6) -> bool:
        """检查新路径是否与现有路径足够不同"""
        if not existing_paths:
            return True
        
        new_concepts = set(new_path.nodes.keys())
        for existing in existing_paths:
            existing_concepts = set(existing.nodes.keys())
            overlap = len(new_concepts & existing_concepts)
            similarity = overlap / max(len(new_concepts), len(existing_concepts))
            if similarity > threshold:
                return False
        return True


class KnowledgeGapAnalyzer:
    """知识缺口分析器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph, learner_profile: LearnerProfile):
        self.graph = knowledge_graph
        self.learner = learner_profile
    
    def analyze_gaps(self, target_concepts: List[str]) -> Dict[str, Any]:
        """分析学习者为达到目标概念所需学习的知识缺口"""
        
        gaps = {
            "target_concepts": target_concepts,
            "prerequisites_needed": [],
            "knowledge_gaps": [],
            "estimated_study_time": 0,
            "prerequisite_tree": {}
        }
        
        for target in target_concepts:
            # 获取先修概念
            prereqs = self.graph.get_prerequisite_graph(target)
            
            # 检查每个先修概念的掌握情况
            for prereq in prereqs:
                mastery = self.learner.get_concept_mastery(prereq)
                if mastery < 0.7:  # 未充分掌握
                    gaps["knowledge_gaps"].append({
                        "concept_id": prereq,
                        "current_mastery": mastery,
                        "target_mastery": 0.7,
                        "gap": 0.7 - mastery,
                        "for_target": target
                    })
                    
                    concept = self.graph.get_node(prereq)
                    if concept:
                        gaps["estimated_study_time"] += concept.estimated_time_minutes
            
            gaps["prerequisites_needed"].extend(prereqs)
            gaps["prerequisite_tree"][target] = list(prereqs)
        
        # 去重
        gaps["prerequisites_needed"] = list(set(gaps["prerequisites_needed"]))
        gaps["estimated_study_time"] /= 60  # 转换为小时
        
        return gaps
    
    def prioritize_gaps(self, gaps: Dict[str, Any]) -> List[Dict[str, Any]]:
        """对知识缺口进行优先级排序"""
        
        gap_list = gaps.get("knowledge_gaps", [])
        
        # 根据多个因素计算优先级分数
        for gap in gap_list:
            concept_id = gap["concept_id"]
            concept = self.graph.get_node(concept_id)
            
            # 基础优先级 = 缺口大小
            base_priority = gap["gap"]
            
            # 影响范围（被多少目标概念依赖）
            impact_scope = sum(
                1 for target, prereqs in gaps["prerequisite_tree"].items()
                if concept_id in prereqs
            )
            
            # 难度权重（越基础的概念优先级越高）
            difficulty_weight = 1.0
            if concept:
                difficulty_weight = 1.0 / concept.difficulty.value
            
            gap["priority_score"] = base_priority * impact_scope * difficulty_weight
        
        # 按优先级排序
        gap_list.sort(key=lambda x: x.get("priority_score", 0), reverse=True)
        
        return gap_list


class MultiObjectiveOptimizer:
    """多目标优化器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph):
        self.graph = knowledge_graph
    
    def optimize(
        self,
        candidate_paths: List[LearningPath],
        objectives: Dict[str, float]
    ) -> List[Tuple[LearningPath, float]]:
        """
        多目标优化
        
        objectives: {
            "time": 权重,
            "depth": 权重,
            "breadth": 权重,
            "smoothness": 权重
        }
        """
        
        scored_paths = []
        
        for path in candidate_paths:
            score = 0.0
            
            # 时间目标（越短越好）
            if "time" in objectives:
                time_score = 1 / (1 + path.total_estimated_hours)
                score += time_score * objectives["time"]
            
            # 深度目标（覆盖高级概念）
            if "depth" in objectives:
                advanced_count = sum(
                    1 for node in path.nodes.values()
                    if node.difficulty >= 3
                )
                depth_score = advanced_count / max(len(path.nodes), 1)
                score += depth_score * objectives["depth"]
            
            # 广度目标（多样性）
            if "breadth" in objectives:
                score += path.diversity_score * objectives["breadth"]
            
            # 平滑度目标
            if "smoothness" in objectives:
                smoothness = self._calculate_path_smoothness(path)
                score += smoothness * objectives["smoothness"]
            
            scored_paths.append((path, score))
        
        # 按分数排序
        scored_paths.sort(key=lambda x: x[1], reverse=True)
        
        return scored_paths
    
    def _calculate_path_smoothness(self, path: LearningPath) -> float:
        """计算路径平滑度"""
        if len(path.difficulty_curve) < 2:
            return 1.0
        
        # 计算二阶导数（曲率变化）
        first_derivatives = [
            path.difficulty_curve[i] - path.difficulty_curve[i-1]
            for i in range(1, len(path.difficulty_curve))
        ]
        
        second_derivatives = [
            first_derivatives[i] - first_derivatives[i-1]
            for i in range(1, len(first_derivatives))
        ]
        
        # 曲率变化越小越平滑
        avg_change = sum(abs(d) for d in second_derivatives) / max(len(second_derivatives), 1)
        return max(0, 1 - avg_change)
