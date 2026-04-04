"""
个性化学习路径推荐系统 - 核心推荐算法
基于全局依赖图的个性化学习路径推荐引擎

本模块实现了多种推荐算法：
1. 最短学习路径算法 - 最小化总学习时间
2. 最牢固基础路径算法 - 优先打好基础
3. 快速预览路径算法 - 先整体预览再深入
4. 自适应混合推荐算法 - 综合多种策略
"""

import heapq
import networkx as nx
import numpy as np
from typing import Dict, List, Optional, Set, Tuple, Any, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import uuid
from collections import defaultdict
import json

from user_profile import (
    UserProfile, LearningGoal, ConceptMastery, LearningStyle,
    LearningPreference, TimePreference, LearningGoalPriority
)


class PathStrategy(Enum):
    """路径生成策略"""
    SHORTEST_TIME = "shortest_time"           # 最短时间
    SOLID_FOUNDATION = "solid_foundation"     # 牢固基础
    QUICK_OVERVIEW = "quick_overview"         # 快速预览
    ADAPTIVE = "adaptive"                     # 自适应混合
    CHALLENGE = "challenge"                   # 挑战导向
    BALANCED = "balanced"                     # 平衡模式


@dataclass
class PathNode:
    """路径节点"""
    concept_id: str
    sequence_number: int = 0
    name: str = ""
    estimated_duration: int = 60              # 预计学习时长（分钟）
    difficulty: int = 1                       # 难度等级 (1-5)
    importance: float = 1.0                   # 重要性分数 (0-1)
    prerequisites: List[str] = field(default_factory=list)
    parallelizable: bool = False              # 是否可并行学习
    
    # 推荐资源
    recommended_resources: List[Dict[str, Any]] = field(default_factory=list)
    
    # 学习建议
    study_tips: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "concept_id": self.concept_id,
            "sequence_number": self.sequence_number,
            "name": self.name,
            "estimated_duration": self.estimated_duration,
            "difficulty": self.difficulty,
            "importance": self.importance,
            "prerequisites": self.prerequisites,
            "parallelizable": self.parallelizable,
            "study_tips": self.study_tips
        }


@dataclass
class LearningPath:
    """学习路径"""
    path_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    description: str = ""
    strategy: PathStrategy = PathStrategy.ADAPTIVE
    
    # 路径节点
    nodes: List[PathNode] = field(default_factory=list)
    node_order: List[str] = field(default_factory=list)
    
    # 时间估算
    total_estimated_hours: float = 0.0
    estimated_completion_date: Optional[datetime] = None
    
    # 难度曲线
    difficulty_curve: List[int] = field(default_factory=list)
    
    # 路径评分
    overall_score: float = 0.0
    time_efficiency_score: float = 0.0
    difficulty_smoothness_score: float = 0.0
    learning_style_match_score: float = 0.0
    foundation_strength_score: float = 0.0
    
    # 元数据
    created_at: datetime = field(default_factory=datetime.now)
    target_concepts: List[str] = field(default_factory=list)
    user_id: str = ""
    
    def get_node_by_concept_id(self, concept_id: str) -> Optional[PathNode]:
        """根据概念ID获取节点"""
        for node in self.nodes:
            if node.concept_id == concept_id:
                return node
        return None
    
    def get_parallel_groups(self) -> List[List[PathNode]]:
        """获取可并行学习的节点组"""
        # 根据先修关系将节点分组
        groups = []
        current_group = []
        covered_concepts = set()
        
        for concept_id in self.node_order:
            node = self.get_node_by_concept_id(concept_id)
            if not node:
                continue
            
            # 检查是否所有先修都已覆盖
            if all(p in covered_concepts for p in node.prerequisites):
                current_group.append(node)
            else:
                if current_group:
                    groups.append(current_group)
                current_group = [node]
            
            covered_concepts.add(concept_id)
        
        if current_group:
            groups.append(current_group)
        
        return groups
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "path_id": self.path_id,
            "name": self.name,
            "description": self.description,
            "strategy": self.strategy.value,
            "total_estimated_hours": round(self.total_estimated_hours, 2),
            "estimated_completion_date": self.estimated_completion_date.isoformat() if self.estimated_completion_date else None,
            "difficulty_curve": self.difficulty_curve,
            "overall_score": round(self.overall_score, 2),
            "time_efficiency_score": round(self.time_efficiency_score, 2),
            "difficulty_smoothness_score": round(self.difficulty_smoothness_score, 2),
            "learning_style_match_score": round(self.learning_style_match_score, 2),
            "foundation_strength_score": round(self.foundation_strength_score, 2),
            "nodes": [node.to_dict() for node in self.nodes],
            "node_order": self.node_order,
            "target_concepts": self.target_concepts,
            "created_at": self.created_at.isoformat()
        }


@dataclass
class ConceptGraph:
    """概念依赖图 - 基于NetworkX的包装器"""
    graph: nx.DiGraph = field(default_factory=nx.DiGraph)
    
    def add_concept(self, concept_id: str, name: str = "", 
                    difficulty: int = 1, estimated_time: int = 60,
                    **attributes):
        """添加概念节点"""
        self.graph.add_node(
            concept_id,
            name=name or concept_id,
            difficulty=difficulty,
            estimated_time=estimated_time,
            **attributes
        )
    
    def add_dependency(self, from_concept: str, to_concept: str, 
                       weight: float = 1.0, **attributes):
        """添加依赖关系"""
        self.graph.add_edge(from_concept, to_concept, 
                           weight=weight, **attributes)
    
    def get_prerequisites(self, concept_id: str) -> Set[str]:
        """获取直接先修概念"""
        return set(self.graph.predecessors(concept_id))
    
    def get_all_prerequisites(self, concept_id: str) -> Set[str]:
        """获取所有先修概念（递归）"""
        try:
            return nx.ancestors(self.graph, concept_id)
        except nx.NetworkXError:
            return set()
    
    def get_dependents(self, concept_id: str) -> Set[str]:
        """获取依赖此概念的所有概念"""
        try:
            return nx.descendants(self.graph, concept_id)
        except nx.NetworkXError:
            return set()
    
    def topological_sort(self, concept_ids: Optional[List[str]] = None) -> List[str]:
        """拓扑排序"""
        if concept_ids is None:
            try:
                return list(nx.topological_sort(self.graph))
            except nx.NetworkXUnfeasible:
                # 图中有环，使用弱连通分量
                return list(self.graph.nodes())
        else:
            # 子图拓扑排序
            subgraph = self.graph.subgraph(concept_ids)
            try:
                return list(nx.topological_sort(subgraph))
            except nx.NetworkXUnfeasible:
                return list(concept_ids)
    
    def get_shortest_path(self, start: str, end: str) -> List[str]:
        """获取最短路径"""
        try:
            return nx.shortest_path(self.graph, start, end, weight='weight')
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            return []
    
    def get_difficulty(self, concept_id: str) -> int:
        """获取概念难度"""
        return self.graph.nodes[concept_id].get('difficulty', 1)
    
    def get_estimated_time(self, concept_id: str) -> int:
        """获取预计学习时间"""
        return self.graph.nodes[concept_id].get('estimated_time', 60)
    
    def get_concept_importance(self, concept_id: str, target_concepts: List[str]) -> float:
        """计算概念对于目标的重要性"""
        if concept_id in target_concepts:
            return 1.0
        
        importance = 0.0
        for target in target_concepts:
            if concept_id in self.get_all_prerequisites(target):
                # 计算先修深度
                try:
                    path_length = nx.shortest_path_length(self.graph, concept_id, target)
                    importance += 1.0 / (path_length + 1)
                except (nx.NetworkXNoPath, nx.NodeNotFound):
                    pass
        
        return min(1.0, importance)
    
    def get_parallelizable_concepts(self, learned_concepts: Set[str]) -> Set[str]:
        """获取可并行学习的概念"""
        parallelizable = set()
        
        for concept_id in self.graph.nodes():
            if concept_id in learned_concepts:
                continue
            
            prerequisites = self.get_prerequisites(concept_id)
            if prerequisites.issubset(learned_concepts):
                parallelizable.add(concept_id)
        
        return parallelizable
    
    def calculate_foundation_strength(self, concept_id: str, 
                                      mastered_concepts: Set[str]) -> float:
        """计算概念的基础强度（先修概念的掌握情况）"""
        prerequisites = self.get_all_prerequisites(concept_id)
        if not prerequisites:
            return 1.0
        
        mastered_prereqs = prerequisites.intersection(mastered_concepts)
        return len(mastered_prereqs) / len(prerequisites)


class PathScorer:
    """路径评分器"""
    
    def __init__(self, user_profile: UserProfile, concept_graph: ConceptGraph):
        self.user = user_profile
        self.graph = concept_graph
    
    def score_path(self, path: LearningPath) -> float:
        """综合评分路径"""
        scores = []
        weights = []
        
        # 时间效率 (权重: 0.25)
        time_score = self._score_time_efficiency(path)
        scores.append(time_score)
        weights.append(0.25)
        path.time_efficiency_score = time_score
        
        # 难度平滑度 (权重: 0.20)
        smoothness_score = self._score_difficulty_smoothness(path)
        scores.append(smoothness_score)
        weights.append(0.20)
        path.difficulty_smoothness_score = smoothness_score
        
        # 学习风格匹配 (权重: 0.20)
        style_score = self._score_learning_style_match(path)
        scores.append(style_score)
        weights.append(0.20)
        path.learning_style_match_score = style_score
        
        # 基础强度 (权重: 0.20)
        foundation_score = self._score_foundation_strength(path)
        scores.append(foundation_score)
        weights.append(0.20)
        path.foundation_strength_score = foundation_score
        
        # 目标覆盖 (权重: 0.15)
        coverage_score = self._score_target_coverage(path)
        scores.append(coverage_score)
        weights.append(0.15)
        
        # 加权总分
        overall = sum(s * w for s, w in zip(scores, weights))
        path.overall_score = overall
        
        return overall
    
    def _score_time_efficiency(self, path: LearningPath) -> float:
        """评分时间效率"""
        # 计算总时间
        total_time = sum(node.estimated_duration for node in path.nodes)
        
        # 考虑并行学习的可能性
        parallel_groups = path.get_parallel_groups()
        if parallel_groups:
            # 假设可并行学习的概念可以同时学习
            parallel_time = sum(
                max(node.estimated_duration for node in group)
                for group in parallel_groups
            )
            efficiency = parallel_time / total_time if total_time > 0 else 0
        else:
            efficiency = 0.5
        
        # 归一化到0-1
        return min(1.0, efficiency * 2)
    
    def _score_difficulty_smoothness(self, path: LearningPath) -> float:
        """评分难度平滑度"""
        if len(path.difficulty_curve) < 2:
            return 1.0
        
        # 计算难度跳跃
        jumps = [
            abs(path.difficulty_curve[i] - path.difficulty_curve[i-1])
            for i in range(1, len(path.difficulty_curve))
        ]
        
        # 平均跳跃越小越好
        avg_jump = sum(jumps) / len(jumps)
        return max(0, 1 - avg_jump / 3)
    
    def _score_learning_style_match(self, path: LearningPath) -> float:
        """评分学习风格匹配度"""
        dominant_style = self.user.learning_preference.get_dominant_style()
        
        # 这里简化处理，实际应根据概念资源类型匹配
        # 假设所有概念都提供多种资源
        style_weights = self.user.learning_preference.style_weights
        return style_weights.get(dominant_style, 0.25)
    
    def _score_foundation_strength(self, path: LearningPath) -> float:
        """评分基础强度"""
        mastered = self.user.get_mastered_concept_ids()
        
        total_strength = 0.0
        for node in path.nodes:
            strength = self.graph.calculate_foundation_strength(node.concept_id, mastered)
            total_strength += strength
        
        return total_strength / len(path.nodes) if path.nodes else 0
    
    def _score_target_coverage(self, path: LearningPath) -> float:
        """评分目标覆盖度"""
        if not path.target_concepts:
            return 0.0
        
        path_concepts = {node.concept_id for node in path.nodes}
        covered = set(path.target_concepts).intersection(path_concepts)
        
        return len(covered) / len(path.target_concepts)


class RecommendationEngine:
    """个性化学习路径推荐引擎"""
    
    def __init__(self, concept_graph: ConceptGraph):
        self.graph = concept_graph
        self.scorer: Optional[PathScorer] = None
    
    def recommend(self, user_profile: UserProfile, 
                  strategy: PathStrategy = PathStrategy.ADAPTIVE,
                  target_concepts: Optional[List[str]] = None,
                  num_alternatives: int = 3) -> List[LearningPath]:
        """
        生成个性化学习路径推荐
        
        Args:
            user_profile: 用户画像
            strategy: 推荐策略
            target_concepts: 目标概念（如未指定则使用用户目标）
            num_alternatives: 备选路径数量
        
        Returns:
            排序后的学习路径列表
        """
        # 确定目标概念
        targets = target_concepts or user_profile.get_target_concepts()
        if not targets:
            raise ValueError("No target concepts specified")
        
        # 初始化评分器
        self.scorer = PathScorer(user_profile, self.graph)
        
        # 生成路径
        paths = []
        
        if strategy == PathStrategy.SHORTEST_TIME:
            paths.append(self._shortest_learning_path(user_profile, targets))
        
        elif strategy == PathStrategy.SOLID_FOUNDATION:
            paths.append(self._solid_foundation_path(user_profile, targets))
        
        elif strategy == PathStrategy.QUICK_OVERVIEW:
            paths.append(self._quick_overview_path(user_profile, targets))
        
        elif strategy == PathStrategy.CHALLENGE:
            paths.append(self._challenge_path(user_profile, targets))
        
        elif strategy == PathStrategy.BALANCED:
            paths.append(self._balanced_path(user_profile, targets))
        
        else:  # ADAPTIVE - 生成多种策略并排序
            paths.append(self._shortest_learning_path(user_profile, targets))
            paths.append(self._solid_foundation_path(user_profile, targets))
            paths.append(self._quick_overview_path(user_profile, targets))
            paths.append(self._balanced_path(user_profile, targets))
        
        # 过滤掉无效路径
        paths = [p for p in paths if p and p.nodes]
        
        # 评分并排序
        for path in paths:
            path.target_concepts = targets
            path.user_id = user_profile.user_id
            self.scorer.score_path(path)
        
        paths.sort(key=lambda p: p.overall_score, reverse=True)
        
        # 生成备选路径（通过微调约束）
        alternatives = self._generate_alternatives(user_profile, targets, 
                                                   paths[0] if paths else None,
                                                   num_alternatives)
        
        all_paths = paths + alternatives
        all_paths.sort(key=lambda p: p.overall_score, reverse=True)
        
        return all_paths[:num_alternatives + 1]
    
    def _get_required_concepts(self, user_profile: UserProfile, 
                               target_concepts: List[str]) -> Set[str]:
        """获取达到目标所需的所有概念"""
        required = set()
        mastered = user_profile.get_mastered_concept_ids()
        
        for target in target_concepts:
            if target not in mastered:
                required.add(target)
                # 获取所有先修
                prereqs = self.graph.get_all_prerequisites(target)
                # 只添加未掌握的先修
                required.update(prereqs - mastered)
        
        return required
    
    def _shortest_learning_path(self, user_profile: UserProfile,
                                target_concepts: List[str]) -> LearningPath:
        """
        算法1：最短学习路径
        
        最小化总学习时间的路径，适合时间紧迫的学习者
        """
        path = LearningPath(
            name="最短时间路径",
            description="优化总学习时间，适合时间紧迫的学习者",
            strategy=PathStrategy.SHORTEST_TIME
        )
        
        # 获取所需概念
        required = self._get_required_concepts(user_profile, target_concepts)
        
        if not required:
            return path
        
        # 拓扑排序
        sorted_concepts = self.graph.topological_sort(list(required))
        
        # 创建节点
        for i, concept_id in enumerate(sorted_concepts):
            node = PathNode(
                concept_id=concept_id,
                sequence_number=i,
                name=self.graph.graph.nodes[concept_id].get('name', concept_id),
                estimated_duration=self.graph.get_estimated_time(concept_id),
                difficulty=self.graph.get_difficulty(concept_id),
                importance=self.graph.get_concept_importance(concept_id, target_concepts),
                prerequisites=list(self.graph.get_prerequisites(concept_id))
            )
            
            # 标记可并行学习的概念
            node.parallelizable = len(node.prerequisites) == 0 or i == 0
            
            path.nodes.append(node)
            path.node_order.append(concept_id)
            path.difficulty_curve.append(node.difficulty)
        
        # 计算总时间（考虑并行）
        parallel_groups = path.get_parallel_groups()
        path.total_estimated_hours = sum(
            max(node.estimated_duration for node in group) / 60
            for group in parallel_groups
        )
        
        # 估算完成日期
        days = user_profile.time_preference.estimate_completion_days(
            path.total_estimated_hours
        )
        path.estimated_completion_date = datetime.now() + timedelta(days=days)
        
        return path
    
    def _solid_foundation_path(self, user_profile: UserProfile,
                               target_concepts: List[str]) -> LearningPath:
        """
        算法2：最牢固基础路径
        
        优先打好基础，确保每个概念的依赖都充分掌握
        适合追求深度理解的学习者
        """
        path = LearningPath(
            name="牢固基础路径",
            description="深度优先，确保每个概念的前置都完全掌握",
            strategy=PathStrategy.SOLID_FOUNDATION
        )
        
        mastered = user_profile.get_mastered_concept_ids()
        visited = set(mastered)
        ordered_concepts = []
        
        def dfs(concept_id: str):
            """深度优先遍历"""
            if concept_id in visited:
                return
            
            # 递归处理所有先修
            for prereq in self.graph.get_prerequisites(concept_id):
                dfs(prereq)
            
            ordered_concepts.append(concept_id)
            visited.add(concept_id)
        
        # 对所有目标概念进行DFS
        for target in target_concepts:
            if target not in mastered:
                dfs(target)
        
        # 创建节点
        for i, concept_id in enumerate(ordered_concepts):
            node = PathNode(
                concept_id=concept_id,
                sequence_number=i,
                name=self.graph.graph.nodes[concept_id].get('name', concept_id),
                estimated_duration=self.graph.get_estimated_time(concept_id),
                difficulty=self.graph.get_difficulty(concept_id),
                importance=self.graph.get_concept_importance(concept_id, target_concepts),
                prerequisites=list(self.graph.get_prerequisites(concept_id))
            )
            
            # 为基础概念增加额外学习时间
            if self.graph.calculate_foundation_strength(concept_id, mastered) < 0.5:
                node.estimated_duration = int(node.estimated_duration * 1.3)
                node.study_tips.append("建议额外练习，巩固基础")
            
            path.nodes.append(node)
            path.node_order.append(concept_id)
            path.difficulty_curve.append(node.difficulty)
        
        # 计算总时间
        path.total_estimated_hours = sum(
            node.estimated_duration for node in path.nodes
        ) / 60
        
        days = user_profile.time_preference.estimate_completion_days(
            path.total_estimated_hours
        )
        path.estimated_completion_date = datetime.now() + timedelta(days=days)
        
        return path
    
    def _quick_overview_path(self, user_profile: UserProfile,
                             target_concepts: List[str]) -> LearningPath:
        """
        算法3：快速预览路径
        
        先整体预览，再深入学习
        广度优先，先建立整体框架
        适合快速入门和建立全局观
        """
        path = LearningPath(
            name="快速预览路径",
            description="广度优先，先建立整体框架，再深入细节",
            strategy=PathStrategy.QUICK_OVERVIEW
        )
        
        mastered = user_profile.get_mastered_concept_ids()
        required = self._get_required_concepts(user_profile, target_concepts)
        
        # BFS分层
        layers = []
        current_layer = set(mastered)
        remaining = required.copy()
        
        while remaining:
            next_layer = set()
            for concept_id in current_layer:
                # 获取依赖于当前层概念的所有概念
                for dependent in self.graph.get_dependents(concept_id):
                    if dependent in remaining:
                        # 检查所有先修是否都已覆盖
                        prereqs = self.graph.get_prerequisites(dependent)
                        if prereqs.issubset(set().union(*layers, mastered, current_layer)):
                            next_layer.add(dependent)
            
            if not next_layer:
                break
            
            layers.append(list(next_layer))
            remaining -= next_layer
            current_layer = next_layer
        
        # 每层内部按难度排序
        for layer in layers:
            layer.sort(key=lambda x: self.graph.get_difficulty(x))
        
        # 扁平化
        ordered_concepts = [c for layer in layers for c in layer]
        
        # 创建节点
        for i, concept_id in enumerate(ordered_concepts):
            node = PathNode(
                concept_id=concept_id,
                sequence_number=i,
                name=self.graph.graph.nodes[concept_id].get('name', concept_id),
                estimated_duration=int(self.graph.get_estimated_time(concept_id) * 0.7),  # 快速预览减少时间
                difficulty=self.graph.get_difficulty(concept_id),
                importance=self.graph.get_concept_importance(concept_id, target_concepts),
                prerequisites=list(self.graph.get_prerequisites(concept_id))
            )
            
            # 第一层概念标记为预览
            if concept_id in layers[0] if layers else False:
                node.study_tips.append("先快速预览，建立整体框架")
            
            path.nodes.append(node)
            path.node_order.append(concept_id)
            path.difficulty_curve.append(node.difficulty)
        
        # 计算总时间
        path.total_estimated_hours = sum(
            node.estimated_duration for node in path.nodes
        ) / 60
        
        days = user_profile.time_preference.estimate_completion_days(
            path.total_estimated_hours
        )
        path.estimated_completion_date = datetime.now() + timedelta(days=days)
        
        return path
    
    def _challenge_path(self, user_profile: UserProfile,
                        target_concepts: List[str]) -> LearningPath:
        """
        算法4：挑战导向路径
        
        以挑战性目标为导向，穿插基础概念学习
        适合有明确目标且学习能力强的学习者
        """
        path = LearningPath(
            name="挑战导向路径",
            description="以目标为导向，在实践中学习所需概念",
            strategy=PathStrategy.CHALLENGE
        )
        
        # 先添加目标概念作为"挑战"
        for target in target_concepts:
            node = PathNode(
                concept_id=target,
                sequence_number=0,
                name=self.graph.graph.nodes[target].get('name', target),
                estimated_duration=self.graph.get_estimated_time(target),
                difficulty=self.graph.get_difficulty(target),
                importance=1.0,
                prerequisites=list(self.graph.get_prerequisites(target)),
                study_tips=["这是一个挑战目标，先了解需要哪些前置知识"]
            )
            path.nodes.append(node)
        
        # 然后按照solid_foundation方式补充先修
        foundation_path = self._solid_foundation_path(user_profile, target_concepts)
        
        # 合并两个路径：挑战在前，基础在后
        existing_concepts = {node.concept_id for node in path.nodes}
        i = len(path.nodes)
        for node in foundation_path.nodes:
            if node.concept_id not in existing_concepts:
                node.sequence_number = i
                node.study_tips.append("学习后回顾挑战目标")
                path.nodes.append(node)
                path.node_order.append(node.concept_id)
                path.difficulty_curve.append(node.difficulty)
                i += 1
        
        # 重新排序：先基础后挑战
        path.nodes.sort(key=lambda n: n.difficulty)
        path.node_order = [n.concept_id for n in path.nodes]
        path.difficulty_curve = [n.difficulty for n in path.nodes]
        
        path.total_estimated_hours = foundation_path.total_estimated_hours * 1.2
        
        days = user_profile.time_preference.estimate_completion_days(
            path.total_estimated_hours
        )
        path.estimated_completion_date = datetime.now() + timedelta(days=days)
        
        return path
    
    def _balanced_path(self, user_profile: UserProfile,
                       target_concepts: List[str]) -> LearningPath:
        """
        算法5：平衡路径
        
        综合时间效率、基础强度和学习风格的平衡方案
        """
        path = LearningPath(
            name="平衡学习路径",
            description="综合优化时间、基础和风格匹配的推荐路径",
            strategy=PathStrategy.BALANCED
        )
        
        # 获取所需概念
        required = self._get_required_concepts(user_profile, target_concepts)
        
        if not required:
            return path
        
        # 使用拓扑排序作为基础
        sorted_concepts = self.graph.topological_sort(list(required))
        
        # 根据用户特征调整顺序
        mastered = user_profile.get_mastered_concept_ids()
        
        # 计算每个概念的优先级分数
        concept_scores = {}
        for concept_id in sorted_concepts:
            score = 0.0
            
            # 重要性权重
            importance = self.graph.get_concept_importance(concept_id, target_concepts)
            score += importance * 0.4
            
            # 基础强度权重（先修掌握情况）
            foundation = self.graph.calculate_foundation_strength(concept_id, mastered)
            score += foundation * 0.3
            
            # 难度适中权重
            difficulty = self.graph.get_difficulty(concept_id)
            user_level = user_profile.calculate_overall_ability() if hasattr(user_profile, 'calculate_overall_ability') else 2
            difficulty_fit = 1 - abs(difficulty - user_level) / 5
            score += difficulty_fit * 0.3
            
            concept_scores[concept_id] = score
        
        # 按分数重新排序（保持拓扑约束）
        ordered_concepts = []
        remaining = set(sorted_concepts)
        
        while remaining:
            # 找出当前可学习的概念（所有先修已在ordered_concepts中）
            available = [
                c for c in remaining
                if self.graph.get_prerequisites(c).issubset(set(ordered_concepts).union(mastered))
            ]
            
            if not available:
                break
            
            # 选择分数最高的
            available.sort(key=lambda c: concept_scores.get(c, 0), reverse=True)
            selected = available[0]
            
            ordered_concepts.append(selected)
            remaining.remove(selected)
        
        # 创建节点
        for i, concept_id in enumerate(ordered_concepts):
            node = PathNode(
                concept_id=concept_id,
                sequence_number=i,
                name=self.graph.graph.nodes[concept_id].get('name', concept_id),
                estimated_duration=self.graph.get_estimated_time(concept_id),
                difficulty=self.graph.get_difficulty(concept_id),
                importance=self.graph.get_concept_importance(concept_id, target_concepts),
                prerequisites=list(self.graph.get_prerequisites(concept_id))
            )
            
            # 根据用户学习风格添加提示
            dominant_style = user_profile.learning_preference.get_dominant_style()
            if dominant_style == LearningStyle.VISUAL:
                node.study_tips.append("寻找相关图表和可视化资源")
            elif dominant_style == LearningStyle.TEXTUAL:
                node.study_tips.append("阅读教材中的详细定义和定理")
            elif dominant_style == LearningStyle.INTERACTIVE:
                node.study_tips.append("完成相关练习题巩固理解")
            
            path.nodes.append(node)
            path.node_order.append(concept_id)
            path.difficulty_curve.append(node.difficulty)
        
        # 计算总时间
        path.total_estimated_hours = sum(
            node.estimated_duration for node in path.nodes
        ) / 60
        
        days = user_profile.time_preference.estimate_completion_days(
            path.total_estimated_hours
        )
        path.estimated_completion_date = datetime.now() + timedelta(days=days)
        
        return path
    
    def _generate_alternatives(self, user_profile: UserProfile,
                               target_concepts: List[str],
                               base_path: Optional[LearningPath],
                               num_alternatives: int) -> List[LearningPath]:
        """生成备选路径"""
        if not base_path or not base_path.nodes:
            return []
        
        alternatives = []
        
        # 策略1: 调整学习顺序（对于独立性高的概念）
        if len(base_path.nodes) > 3:
            alt_path = LearningPath(
                name="替代路径 - 顺序优化",
                description="调整了部分概念的学习顺序",
                strategy=base_path.strategy
            )
            
            # 打乱独立概念的顺序
            nodes_with_prereqs = [(n, set(n.prerequisites)) for n in base_path.nodes]
            shuffled = []
            covered = user_profile.get_mastered_concept_ids().copy()
            
            remaining = nodes_with_prereqs.copy()
            while remaining:
                # 找出当前可学习的
                available = [(n, p) for n, p in remaining if p.issubset(covered)]
                if not available:
                    break
                
                # 随机选择一个
                import random
                selected, prereqs = random.choice(available)
                shuffled.append(selected)
                covered.add(selected.concept_id)
                remaining.remove((selected, prereqs))
            
            alt_path.nodes = shuffled
            alt_path.node_order = [n.concept_id for n in shuffled]
            alt_path.difficulty_curve = [n.difficulty for n in shuffled]
            alt_path.total_estimated_hours = base_path.total_estimated_hours
            alt_path.target_concepts = target_concepts
            alt_path.user_id = user_profile.user_id
            
            alternatives.append(alt_path)
        
        # 策略2: 增加/减少时间投入
        for i in range(min(num_alternatives - 1, 2)):
            factor = 0.8 if i == 0 else 1.2  # 80%或120%时间
            
            alt_path = LearningPath(
                name=f"替代路径 - {'紧凑' if factor < 1 else '深度'}版",
                description=f"{'压缩学习时间，适合快速完成' if factor < 1 else '增加学习时间，追求深度理解'}",
                strategy=base_path.strategy
            )
            
            for node in base_path.nodes:
                new_node = PathNode(
                    concept_id=node.concept_id,
                    sequence_number=node.sequence_number,
                    name=node.name,
                    estimated_duration=int(node.estimated_duration * factor),
                    difficulty=node.difficulty,
                    importance=node.importance,
                    prerequisites=node.prerequisites.copy(),
                    study_tips=node.study_tips.copy()
                )
                alt_path.nodes.append(new_node)
            
            alt_path.node_order = base_path.node_order.copy()
            alt_path.difficulty_curve = base_path.difficulty_curve.copy()
            alt_path.total_estimated_hours = base_path.total_estimated_hours * factor
            alt_path.target_concepts = target_concepts
            alt_path.user_id = user_profile.user_id
            
            alternatives.append(alt_path)
        
        return alternatives


def create_sample_graph() -> ConceptGraph:
    """创建示例概念图"""
    graph = ConceptGraph()
    
    # 基础概念
    concepts = [
        ("set_theory", "集合论", 1, 45),
        ("functions", "函数", 1, 60),
        ("relations", "关系", 1, 50),
        ("logic", "数理逻辑", 2, 90),
        ("group_theory", "群论", 2, 120),
        ("ring_theory", "环论", 2, 120),
        ("field_theory", "域论", 3, 100),
        ("vector_spaces", "向量空间", 2, 120),
        ("linear_algebra", "线性代数", 3, 150),
        ("topology", "拓扑学", 3, 180),
        ("metric_spaces", "度量空间", 2, 100),
        ("analysis", "数学分析", 3, 200),
        ("calculus", "微积分", 2, 180),
        ("algebraic_topology", "代数拓扑", 4, 250),
    ]
    
    for cid, name, difficulty, time in concepts:
        graph.add_concept(cid, name, difficulty, time)
    
    # 依赖关系
    dependencies = [
        ("set_theory", "functions"),
        ("set_theory", "relations"),
        ("functions", "group_theory"),
        ("relations", "group_theory"),
        ("logic", "group_theory"),
        ("group_theory", "ring_theory"),
        ("ring_theory", "field_theory"),
        ("field_theory", "vector_spaces"),
        ("vector_spaces", "linear_algebra"),
        ("set_theory", "topology"),
        ("topology", "metric_spaces"),
        ("metric_spaces", "analysis"),
        ("analysis", "calculus"),
        ("group_theory", "algebraic_topology"),
        ("topology", "algebraic_topology"),
    ]
    
    for prereq, concept in dependencies:
        graph.add_dependency(prereq, concept)
    
    return graph


if __name__ == "__main__":
    # 测试代码
    print("=== 推荐引擎测试 ===\n")
    
    # 创建概念图
    graph = create_sample_graph()
    print(f"创建概念图: {len(graph.graph.nodes)} 个概念, {len(graph.graph.edges)} 条依赖")
    
    # 创建用户画像
    user = UserProfile(name="测试用户", email="test@example.com")
    user.learning_preference.style_weights = {
        LearningStyle.VISUAL: 0.4,
        LearningStyle.TEXTUAL: 0.3,
        LearningStyle.INTERACTIVE: 0.2,
        LearningStyle.MULTIMODAL: 0.1
    }
    user.time_preference.daily_hours = 2.5
    user.time_preference.weekly_days = 5
    
    # 设置已掌握的概念
    user.update_mastery("set_theory", 0.85)
    user.update_mastery("functions", 0.75)
    user.update_mastery("relations", 0.70)
    
    print(f"\n用户画像:")
    print(f"  - 已掌握: {list(user.get_mastered_concept_ids())}")
    print(f"  - 学习风格: {user.learning_preference.get_dominant_style().value}")
    print(f"  - 每日学习: {user.time_preference.daily_hours}小时")
    
    # 创建推荐引擎
    engine = RecommendationEngine(graph)
    
    # 测试不同策略
    target_concepts = ["algebraic_topology", "linear_algebra"]
    print(f"\n目标概念: {target_concepts}")
    
    strategies = [
        PathStrategy.SHORTEST_TIME,
        PathStrategy.SOLID_FOUNDATION,
        PathStrategy.QUICK_OVERVIEW,
        PathStrategy.BALANCED,
        PathStrategy.ADAPTIVE
    ]
    
    for strategy in strategies:
        print(f"\n{'='*50}")
        print(f"策略: {strategy.value}")
        print('='*50)
        
        paths = engine.recommend(user, strategy=strategy, 
                                 target_concepts=target_concepts,
                                 num_alternatives=1)
        
        for i, path in enumerate(paths[:2]):  # 只显示前2条
            print(f"\n路径 {i+1}: {path.name}")
            print(f"  描述: {path.description}")
            print(f"  总时间: {path.total_estimated_hours:.1f}小时")
            print(f"  概念数: {len(path.nodes)}")
            print(f"  综合评分: {path.overall_score:.2f}")
            print(f"  学习顺序: {' -> '.join(path.node_order[:5])}{'...' if len(path.node_order) > 5 else ''}")
    
    print("\n\n=== 测试完成 ===")
