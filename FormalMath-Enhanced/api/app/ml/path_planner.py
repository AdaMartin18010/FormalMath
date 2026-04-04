"""
学习路径规划器
实现A*算法和强化学习优化的路径规划
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import heapq
from collections import defaultdict


class PathOptimizationGoal(Enum):
    """路径优化目标"""
    MIN_TIME = "min_time"           # 最短时间
    MAX_MASTERY = "max_mastery"     # 最大掌握度
    BALANCED = "balanced"           # 平衡
    MIN_DIFFICULTY = "min_difficulty"  # 最低难度


@dataclass
class PathNode:
    """路径节点"""
    concept_id: str
    estimated_time: int = 30  # 分钟
    difficulty: float = 0.5
    importance: float = 0.5
    prerequisites: Set[str] = field(default_factory=set)
    
    # 动态属性
    mastery_level: float = 0.0
    retention_rate: float = 1.0
    
    def to_dict(self) -> Dict:
        return {
            'concept_id': self.concept_id,
            'estimated_time': self.estimated_time,
            'difficulty': self.difficulty,
            'importance': self.importance,
            'prerequisites': list(self.prerequisites),
            'mastery_level': self.mastery_level,
            'retention_rate': self.retention_rate
        }


@dataclass
class LearningPath:
    """学习路径"""
    path_id: str
    user_id: str
    nodes: List[PathNode]
    target_concepts: List[str]
    
    # 路径属性
    total_time: int = 0  # 分钟
    total_difficulty: float = 0.0
    expected_mastery: float = 0.0
    
    # 元数据
    created_at: datetime = field(default_factory=datetime.utcnow)
    optimization_goal: PathOptimizationGoal = PathOptimizationGoal.BALANCED
    
    def to_dict(self) -> Dict:
        return {
            'path_id': self.path_id,
            'user_id': self.user_id,
            'nodes': [node.to_dict() for node in self.nodes],
            'target_concepts': self.target_concepts,
            'total_time': self.total_time,
            'total_difficulty': self.total_difficulty,
            'expected_mastery': self.expected_mastery,
            'created_at': self.created_at.isoformat(),
            'optimization_goal': self.optimization_goal.value,
            'node_count': len(self.nodes)
        }


class AStarPathPlanner:
    """
    A*路径规划器
    用于生成最优学习序列
    """
    
    def __init__(
        self,
        knowledge_graph: Any,  # KnowledgeGraphEmbedder
        alpha: float = 1.0,     # 时间权重
        beta: float = 1.0,      # 难度权重
        gamma: float = 1.0      # 掌握度权重
    ):
        self.knowledge_graph = knowledge_graph
        self.alpha = alpha
        self.beta = beta
        self.gamma = gamma
        
        # 启发式函数权重
        self.heuristic_weight = 1.2
        
    def plan_path(
        self,
        user_id: str,
        start_concepts: Set[str],
        target_concepts: Set[str],
        goal: PathOptimizationGoal = PathOptimizationGoal.BALANCED,
        constraints: Optional[Dict] = None
    ) -> Optional[LearningPath]:
        """
        规划学习路径
        
        Args:
            user_id: 用户ID
            start_concepts: 已掌握概念
            target_concepts: 目标概念
            goal: 优化目标
            constraints: 约束条件 (max_time, min_mastery等)
        
        Returns:
            学习路径
        """
        constraints = constraints or {}
        
        # 获取所有需要学习的概念
        all_required = set()
        for target in target_concepts:
            prereqs = self.knowledge_graph.graph.get_all_prerequisites(target)
            all_required.update(prereqs)
        
        # 排除已掌握的概念
        to_learn = all_required - start_concepts
        
        if not to_learn:
            return LearningPath(
                path_id=f"path_{user_id}_{datetime.utcnow().timestamp()}",
                user_id=user_id,
                nodes=[],
                target_concepts=list(target_concepts),
                optimization_goal=goal
            )
        
        # 根据优化目标调整权重
        self._adjust_weights_for_goal(goal)
        
        # A*搜索
        path_nodes = self._astar_search(
            start_concepts, target_concepts, to_learn, constraints
        )
        
        if not path_nodes:
            return None
        
        # 构建路径对象
        total_time = sum(node.estimated_time for node in path_nodes)
        avg_difficulty = np.mean([node.difficulty for node in path_nodes]) if path_nodes else 0
        
        return LearningPath(
            path_id=f"path_{user_id}_{int(datetime.utcnow().timestamp())}",
            user_id=user_id,
            nodes=path_nodes,
            target_concepts=list(target_concepts),
            total_time=total_time,
            total_difficulty=avg_difficulty,
            expected_mastery=self._estimate_final_mastery(path_nodes),
            optimization_goal=goal
        )
    
    def _adjust_weights_for_goal(self, goal: PathOptimizationGoal):
        """根据优化目标调整权重"""
        if goal == PathOptimizationGoal.MIN_TIME:
            self.alpha, self.beta, self.gamma = 2.0, 0.5, 0.5
        elif goal == PathOptimizationGoal.MAX_MASTERY:
            self.alpha, self.beta, self.gamma = 0.5, 0.5, 2.0
        elif goal == PathOptimizationGoal.MIN_DIFFICULTY:
            self.alpha, self.beta, self.gamma = 0.5, 2.0, 0.5
        else:  # BALANCED
            self.alpha, self.beta, self.gamma = 1.0, 1.0, 1.0
    
    def _astar_search(
        self,
        start_concepts: Set[str],
        target_concepts: Set[str],
        to_learn: Set[str],
        constraints: Dict
    ) -> List[PathNode]:
        """A*搜索算法"""
        # 初始化
        open_set = []
        closed_set = set()
        
        # 节点信息: (g_score, parent, concept_id)
        node_info = {
            concept: {'g': float('inf'), 'parent': None}
            for concept in to_learn
        }
        
        # 找到起始点（没有前置或前置已掌握的概念）
        starters = self._find_starting_concepts(to_learn, start_concepts)
        
        for starter in starters:
            node_info[starter]['g'] = 0
            h = self._heuristic(starter, target_concepts, to_learn)
            heapq.heappush(open_set, (h, starter))
        
        path_found = []
        learned = set()
        
        while open_set and len(learned) < len(to_learn):
            _, current = heapq.heappop(open_set)
            
            if current in learned:
                continue
            
            learned.add(current)
            path_found.append(self._create_path_node(current))
            
            # 检查是否所有目标已可达
            if self._all_targets_reachable(target_concepts, start_concepts | learned):
                break
            
            # 扩展邻居（依赖当前概念的概念）
            neighbors = self._get_available_concepts(to_learn - learned, learned | start_concepts)
            
            for neighbor in neighbors:
                if neighbor in learned:
                    continue
                
                # 计算g值
                edge_cost = self._compute_edge_cost(current, neighbor)
                tentative_g = node_info[current]['g'] + edge_cost
                
                if tentative_g < node_info[neighbor]['g']:
                    node_info[neighbor]['g'] = tentative_g
                    node_info[neighbor]['parent'] = current
                    
                    h = self._heuristic(neighbor, target_concepts, to_learn - learned)
                    f = tentative_g + self.heuristic_weight * h
                    
                    heapq.heappush(open_set, (f, neighbor))
        
        return path_found
    
    def _find_starting_concepts(self, to_learn: Set[str], known: Set[str]) -> List[str]:
        """找到可以开始学习的概念（没有未掌握的前置）"""
        starters = []
        for concept in to_learn:
            prereqs = set(self.knowledge_graph.graph.get_prerequisites(concept))
            if not prereqs or prereqs.issubset(known):
                starters.append(concept)
        return starters
    
    def _get_available_concepts(self, remaining: Set[str], learned: Set[str]) -> List[str]:
        """获取当前可以学习的概念"""
        available = []
        for concept in remaining:
            prereqs = set(self.knowledge_graph.graph.get_prerequisites(concept))
            if prereqs.issubset(learned):
                available.append(concept)
        return available
    
    def _all_targets_reachable(self, targets: Set[str], known: Set[str]) -> bool:
        """检查所有目标是否都可达"""
        for target in targets:
            prereqs = self.knowledge_graph.graph.get_all_prerequisites(target)
            if not prereqs.issubset(known):
                return False
        return True
    
    def _create_path_node(self, concept_id: str) -> PathNode:
        """创建路径节点"""
        node = self.knowledge_graph.graph.nodes.get(concept_id)
        
        if node:
            return PathNode(
                concept_id=concept_id,
                estimated_time=self._estimate_learning_time(concept_id),
                difficulty=node.difficulty,
                importance=node.importance,
                prerequisites=set(self.knowledge_graph.graph.get_prerequisites(concept_id))
            )
        else:
            return PathNode(
                concept_id=concept_id,
                estimated_time=30,
                difficulty=0.5,
                importance=0.5
            )
    
    def _estimate_learning_time(self, concept_id: str) -> int:
        """估计学习时间"""
        node = self.knowledge_graph.graph.nodes.get(concept_id)
        if node:
            # 基础时间根据难度
            base_time = 20 + node.difficulty * 40  # 20-60分钟
            return int(base_time)
        return 30
    
    def _compute_edge_cost(self, from_concept: str, to_concept: str) -> float:
        """计算边成本"""
        node = self.knowledge_graph.graph.nodes.get(to_concept)
        if not node:
            return 1.0
        
        # 综合成本
        time_cost = self._estimate_learning_time(to_concept) / 60.0  # 转换为小时
        difficulty_cost = node.difficulty
        
        # 概念间相似度（相似度高则学习成本低）
        if self.knowledge_graph.is_fitted:
            similarity = self.knowledge_graph.embedding_model.compute_similarity(
                from_concept, to_concept
            )
            similarity_bonus = max(0, similarity * 0.3)  # 相似度降低成本
        else:
            similarity_bonus = 0
        
        return (
            self.alpha * time_cost +
            self.beta * difficulty_cost -
            self.gamma * similarity_bonus
        )
    
    def _heuristic(
        self,
        concept: str,
        targets: Set[str],
        remaining: Set[str]
    ) -> float:
        """启发式函数（到目标的估计成本）"""
        # 计算到最近目标的距离
        min_distance = float('inf')
        
        for target in targets:
            if target in remaining:
                # 估计距离
                distance = self._estimate_distance(concept, target)
                min_distance = min(min_distance, distance)
        
        return min_distance if min_distance != float('inf') else 0
    
    def _estimate_distance(self, from_concept: str, to_concept: str) -> float:
        """估计两个概念间的距离"""
        # 使用嵌入向量计算语义距离
        if self.knowledge_graph.is_fitted:
            sim = self.knowledge_graph.embedding_model.compute_similarity(
                from_concept, to_concept
            )
            return 1 - sim
        
        # 回退：拓扑距离
        return 1.0
    
    def _estimate_final_mastery(self, path_nodes: List[PathNode]) -> float:
        """估计最终掌握度"""
        if not path_nodes:
            return 0.0
        
        # 假设学习后掌握度与难度相关
        expected_mastery = []
        for node in path_nodes:
            # 难度越低，掌握度越高
            mastery = max(0.6, 1 - node.difficulty * 0.3)
            expected_mastery.append(mastery)
        
        return np.mean(expected_mastery)


class AdaptivePathPlanner:
    """
    自适应路径规划器
    根据学习进度动态调整路径
    """
    
    def __init__(self, base_planner: AStarPathPlanner):
        self.base_planner = base_planner
        self.path_history: Dict[str, List[Dict]] = {}
        self.adaptation_rules = self._initialize_rules()
    
    def _initialize_rules(self) -> Dict[str, Any]:
        """初始化自适应规则"""
        return {
            'fast_mastery_threshold': 0.8,      # 快速掌握阈值
            'slow_mastery_threshold': 0.4,      # 慢速掌握阈值
            'struggle_threshold': 0.3,           # 困难阈值
            'excellence_threshold': 0.9,         # 优秀阈值
            'time_variance_factor': 0.2          # 时间调整因子
        }
    
    def adapt_path(
        self,
        current_path: LearningPath,
        progress_data: Dict[str, Any]
    ) -> LearningPath:
        """
        根据学习进度调整路径
        
        Args:
            current_path: 当前路径
            progress_data: 进度数据
                {
                    'completed_concepts': [concept_ids],
                    'mastery_levels': {concept_id: level},
                    'time_spent': {concept_id: minutes},
                    'performance_scores': {concept_id: score}
                }
        
        Returns:
            调整后的路径
        """
        user_id = current_path.user_id
        
        # 记录历史
        if user_id not in self.path_history:
            self.path_history[user_id] = []
        
        self.path_history[user_id].append({
            'timestamp': datetime.utcnow().isoformat(),
            'path': current_path.to_dict(),
            'progress': progress_data
        })
        
        # 分析学习模式
        learning_pattern = self._analyze_learning_pattern(user_id, progress_data)
        
        # 调整剩余路径
        remaining_nodes = self._adjust_remaining_nodes(
            current_path.nodes,
            progress_data,
            learning_pattern
        )
        
        # 添加补充节点（如果需要）
        if learning_pattern['struggling_concepts']:
            remedial_nodes = self._create_remedial_nodes(
                learning_pattern['struggling_concepts']
            )
            remaining_nodes = remedial_nodes + remaining_nodes
        
        # 创建新路径
        adapted_path = LearningPath(
            path_id=f"{current_path.path_id}_adapted",
            user_id=user_id,
            nodes=remaining_nodes,
            target_concepts=current_path.target_concepts,
            total_time=sum(node.estimated_time for node in remaining_nodes),
            total_difficulty=np.mean([node.difficulty for node in remaining_nodes]) if remaining_nodes else 0,
            expected_mastery=self._estimate_adapted_mastery(remaining_nodes, learning_pattern),
            optimization_goal=current_path.optimization_goal
        )
        
        return adapted_path
    
    def _analyze_learning_pattern(
        self,
        user_id: str,
        progress_data: Dict
    ) -> Dict[str, Any]:
        """分析学习模式"""
        completed = progress_data.get('completed_concepts', [])
        mastery = progress_data.get('mastery_levels', {})
        performance = progress_data.get('performance_scores', {})
        
        fast_concepts = []
        slow_concepts = []
        struggling_concepts = []
        
        for concept in completed:
            m = mastery.get(concept, 0)
            p = performance.get(concept, 0)
            
            if m >= self.adaptation_rules['fast_mastery_threshold'] and p >= self.adaptation_rules['excellence_threshold']:
                fast_concepts.append(concept)
            elif m < self.adaptation_rules['slow_mastery_threshold'] or p < self.adaptation_rules['struggle_threshold']:
                struggling_concepts.append(concept)
            else:
                slow_concepts.append(concept)
        
        # 计算平均掌握速度
        if completed:
            avg_mastery = np.mean([mastery.get(c, 0) for c in completed])
            avg_performance = np.mean([performance.get(c, 0) for c in completed])
        else:
            avg_mastery = 0
            avg_performance = 0
        
        return {
            'fast_concepts': fast_concepts,
            'slow_concepts': slow_concepts,
            'struggling_concepts': struggling_concepts,
            'avg_mastery_speed': avg_mastery,
            'avg_performance': avg_performance,
            'is_fast_learner': len(fast_concepts) > len(slow_concepts) + len(struggling_concepts)
        }
    
    def _adjust_remaining_nodes(
        self,
        nodes: List[PathNode],
        progress_data: Dict,
        learning_pattern: Dict
    ) -> List[PathNode]:
        """调整剩余节点"""
        completed = set(progress_data.get('completed_concepts', []))
        remaining = [n for n in nodes if n.concept_id not in completed]
        
        for node in remaining:
            # 根据学习速度调整时间估计
            if learning_pattern['is_fast_learner']:
                # 快速学习者减少时间
                node.estimated_time = int(node.estimated_time * 0.8)
                # 可以提高难度
                if learning_pattern['avg_performance'] > 0.85:
                    node.difficulty = min(1.0, node.difficulty * 1.1)
            else:
                # 慢速学习者增加时间
                node.estimated_time = int(node.estimated_time * 1.2)
                # 提供更多支持
                node.difficulty = max(0.1, node.difficulty * 0.9)
        
        return remaining
    
    def _create_remedial_nodes(self, struggling_concepts: List[str]) -> List[PathNode]:
        """创建补救学习节点"""
        remedial = []
        
        for concept in struggling_concepts:
            # 查找前置概念
            prereqs = self.base_planner.knowledge_graph.graph.get_prerequisites(concept)
            
            for prereq in prereqs:
                node = self.base_planner._create_path_node(prereq)
                node.estimated_time = int(node.estimated_time * 0.7)  # 复习时间较短
                node.importance = 1.0  # 高重要性
                remedial.append(node)
        
        return remedial
    
    def _estimate_adapted_mastery(
        self,
        nodes: List[PathNode],
        learning_pattern: Dict
    ) -> float:
        """估计调整后掌握度"""
        base_mastery = self.base_planner._estimate_final_mastery(nodes)
        
        # 根据学习模式调整
        if learning_pattern['is_fast_learner']:
            return min(1.0, base_mastery * 1.1)
        elif learning_pattern['struggling_concepts']:
            # 补救学习提高掌握度
            return min(1.0, base_mastery * 1.05)
        
        return base_mastery


class MultiObjectivePathOptimizer:
    """
    多目标路径优化器
    平衡时间、难度、掌握度多个目标
    """
    
    def __init__(self, knowledge_graph: Any):
        self.knowledge_graph = knowledge_graph
        
    def optimize(
        self,
        user_id: str,
        target_concepts: List[str],
        user_profile: Dict[str, Any],
        weights: Optional[Dict[str, float]] = None
    ) -> List[LearningPath]:
        """
        生成多目标优化的路径选项
        
        Returns:
            多个优化路径选项（Pareto前沿）
        """
        weights = weights or {'time': 0.33, 'difficulty': 0.33, 'mastery': 0.34}
        
        base_planner = AStarPathPlanner(self.knowledge_graph)
        
        # 生成不同优化目标的路径
        paths = []
        
        for goal in PathOptimizationGoal:
            path = base_planner.plan_path(
                user_id=user_id,
                start_concepts=set(user_profile.get('known_concepts', [])),
                target_concepts=set(target_concepts),
                goal=goal
            )
            
            if path:
                paths.append(path)
        
        # 评分并排序
        scored_paths = []
        for path in paths:
            score = self._compute_multi_objective_score(path, weights)
            scored_paths.append((score, path))
        
        scored_paths.sort(key=lambda x: x[0], reverse=True)
        
        return [p for _, p in scored_paths[:3]]  # 返回前3个
    
    def _compute_multi_objective_score(
        self,
        path: LearningPath,
        weights: Dict[str, float]
    ) -> float:
        """计算多目标分数"""
        # 归一化各目标（越小越好）
        time_score = 1 / (1 + path.total_time / 60)  # 转换为小时
        difficulty_score = 1 - path.total_difficulty
        mastery_score = path.expected_mastery
        
        # 加权
        return (
            weights.get('time', 0.33) * time_score +
            weights.get('difficulty', 0.33) * difficulty_score +
            weights.get('mastery', 0.34) * mastery_score
        )
