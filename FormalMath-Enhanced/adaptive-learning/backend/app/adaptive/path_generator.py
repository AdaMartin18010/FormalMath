"""
学习路径生成算法模块
包含 A* 算法、动态规划和强化学习路径规划
"""
import heapq
from typing import List, Dict, Set, Tuple, Optional, Callable
from dataclasses import dataclass, field
from collections import defaultdict
import numpy as np
from datetime import datetime, timedelta

from ..schemas import (
    UserProfile, LearningPath, PathNode, ConceptNode,
    DifficultyLevel, PathStatus, ResourceRecommendation, ResourceType
)
from ..knowledge_graph import get_knowledge_graph
from ..core.config import settings


@dataclass(order=True)
class PathNodeState:
    """A* 算法节点状态"""
    f_score: float
    g_score: float = field(compare=False)
    concept_id: str = field(compare=False)
    path: List[str] = field(default_factory=list, compare=False)


class PathScorer:
    """路径评分器 - 评估学习步骤的适宜性"""
    
    def __init__(self, user_profile: UserProfile):
        self.user_profile = user_profile
        self.kg = get_knowledge_graph()
    
    def calculate_step_cost(self, current: str, next_concept: str,
                           visited: Set[str]) -> float:
        """
        计算从当前概念到下一概念的学习成本
        
        考虑因素：
        - 先修知识缺口
        - 难度匹配度
        - 认知风格匹配
        - 兴趣相关性
        """
        concept = self.kg.get_concept(next_concept)
        if not concept:
            return float('inf')
        
        cost = 0.0
        
        # 1. 先修知识缺口成本
        prerequisites = self.kg.get_prerequisites(next_concept, recursive=False)
        unmastered_prereqs = [
            p for p in prerequisites 
            if p not in self.user_profile.mastered_concepts or
            self.user_profile.mastered_concepts[p] < 0.6
        ]
        cost += len(unmastered_prereqs) * settings.PREREQUISITE_WEIGHT * 10
        
        # 2. 难度匹配成本
        difficulty_cost = self._calculate_difficulty_cost(concept)
        cost += difficulty_cost * settings.DIFFICULTY_WEIGHT * 10
        
        # 3. 兴趣相关奖励（负成本）
        if concept.branch in self.user_profile.interest_areas:
            cost -= settings.INTEREST_WEIGHT * 5
        
        # 4. 学习连续性成本（与已访问概念的关联）
        continuity_bonus = 0
        for visited_id in visited:
            if visited_id in concept.prerequisites:
                continuity_bonus -= 2  # 先修连接奖励
            if next_concept in self.kg.get_successors(visited_id):
                continuity_bonus -= 1  # 后继连接奖励
        cost += continuity_bonus
        
        # 5. 认知负荷成本（避免概念过于密集）
        if len(visited) > 5:
            recent_concepts = list(visited)[-5:]
            complexity_sum = sum(
                self.kg.calculate_complexity(c) for c in recent_concepts
            )
            if complexity_sum > 15:  # 高复杂度序列
                cost += 3
        
        return max(cost, 0.1)  # 最小成本避免除零
    
    def _calculate_difficulty_cost(self, concept: ConceptNode) -> float:
        """计算难度匹配成本"""
        user_level = self.user_profile.current_level
        concept_level = concept.difficulty
        
        levels = [DifficultyLevel.BEGINNER, DifficultyLevel.INTERMEDIATE,
                 DifficultyLevel.ADVANCED, DifficultyLevel.EXPERT]
        
        user_idx = levels.index(user_level)
        concept_idx = levels.index(concept_level)
        
        # 难度差异
        diff = abs(user_idx - concept_idx)
        
        # 概念特定调整
        if concept.branch in ['代数', '基础数学']:
            diff *= 0.8  # 基础分支难度略低
        elif concept.branch in ['现代数学', '高级数学']:
            diff *= 1.2  # 高级分支难度略高
        
        return diff
    
    def estimate_remaining_cost(self, current: str, 
                                targets: Set[str],
                                visited: Set[str]) -> float:
        """
        A* 启发函数 - 估计从当前到目标的剩余成本
        
        使用概念间的图距离作为启发
        """
        if not targets:
            return 0
        
        # 计算到各目标的最短路径估计
        estimates = []
        for target in targets:
            if target in visited:
                continue
            # 简化启发：使用先修概念数量差
            target_prereqs = set(self.kg.get_prerequisites(target, recursive=True))
            current_prereqs = set(self.kg.get_prerequisites(current, recursive=True)) if current else set()
            
            remaining = len(target_prereqs - current_prereqs - visited)
            estimates.append(remaining)
        
        return min(estimates) * 5 if estimates else 0


class AStarPathGenerator:
    """A* 学习路径生成器"""
    
    def __init__(self, user_profile: UserProfile):
        self.user_profile = user_profile
        self.kg = get_knowledge_graph()
        self.scorer = PathScorer(user_profile)
    
    def generate(self, target_concepts: List[str],
                max_length: int = None) -> Optional[LearningPath]:
        """
        使用 A* 算法生成学习路径
        
        Args:
            target_concepts: 目标概念列表
            max_length: 最大路径长度
            
        Returns:
            生成的学习路径
        """
        if max_length is None:
            max_length = settings.MAX_PATH_LENGTH
        
        targets = set(target_concepts)
        
        # 获取所有需要学习的概念（包括先修）
        all_required = self._collect_required_concepts(targets)
        
        # 从已掌握概念开始
        start_concepts = set(self.user_profile.mastered_concepts.keys())
        if not start_concepts:
            # 如果没有已掌握概念，找基础入口
            start_concepts = self._find_entry_points(all_required)
        
        # A* 搜索
        open_set = []
        closed_set = set()
        
        # 初始状态
        for start in start_concepts:
            g_score = 0
            h_score = self.scorer.estimate_remaining_cost(start, targets, {start})
            state = PathNodeState(
                f_score=g_score + h_score,
                g_score=g_score,
                concept_id=start,
                path=[start]
            )
            heapq.heappush(open_set, state)
        
        best_path = None
        best_coverage = 0
        
        while open_set:
            current = heapq.heappop(open_set)
            
            if current.concept_id in closed_set:
                continue
            
            closed_set.add(current.concept_id)
            
            # 检查是否完成
            coverage = len(targets & set(current.path))
            if coverage > best_coverage:
                best_coverage = coverage
                best_path = current.path.copy()
            
            if coverage == len(targets):
                # 找到完整路径
                return self._build_learning_path(current.path, target_concepts)
            
            if len(current.path) >= max_length:
                continue
            
            # 扩展邻居
            neighbors = self._get_valid_neighbors(
                current.concept_id, 
                set(current.path),
                all_required
            )
            
            for neighbor in neighbors:
                if neighbor in closed_set:
                    continue
                
                g_score = (current.g_score + 
                          self.scorer.calculate_step_cost(
                              current.concept_id, neighbor, set(current.path)
                          ))
                
                h_score = self.scorer.estimate_remaining_cost(
                    neighbor, targets, set(current.path)
                )
                
                new_state = PathNodeState(
                    f_score=g_score + h_score,
                    g_score=g_score,
                    concept_id=neighbor,
                    path=current.path + [neighbor]
                )
                
                heapq.heappush(open_set, new_state)
        
        # 如果没有找到完整路径，返回最佳部分路径
        if best_path:
            return self._build_learning_path(best_path, target_concepts)
        
        return None
    
    def _collect_required_concepts(self, targets: Set[str]) -> Set[str]:
        """收集所有需要的概念（包括先修）"""
        required = set(targets)
        for target in targets:
            prerequisites = self.kg.get_prerequisites(target, recursive=True)
            required.update(prerequisites)
        return required
    
    def _find_entry_points(self, concepts: Set[str]) -> Set[str]:
        """找到学习入口点（无先修或先修不在集合中的概念）"""
        entries = set()
        for concept_id in concepts:
            prereqs = set(self.kg.get_prerequisites(concept_id, recursive=False))
            if not prereqs or not (prereqs & concepts):
                entries.add(concept_id)
        return entries if entries else concepts
    
    def _get_valid_neighbors(self, current: str, visited: Set[str],
                            candidates: Set[str]) -> List[str]:
        """获取有效的下一个概念候选"""
        neighbors = []
        
        # 直接后继
        successors = self.kg.get_successors(current)
        neighbors.extend([s for s in successors if s in candidates and s not in visited])
        
        # 相关概念
        related = self.kg.get_related_concepts(current)
        neighbors.extend([r for r in related if r in candidates and r not in visited])
        
        # 未访问的目标概念
        neighbors.extend([c for c in candidates if c not in visited])
        
        return list(set(neighbors))
    
    def _build_learning_path(self, concept_sequence: List[str],
                            target_concepts: List[str]) -> LearningPath:
        """将概念序列转换为学习路径对象"""
        nodes = []
        total_time = 0
        
        for i, concept_id in enumerate(concept_sequence):
            concept = self.kg.get_concept(concept_id)
            if not concept:
                continue
            
            # 确定状态
            if concept_id in self.user_profile.mastered_concepts:
                status = PathStatus.COMPLETED
            elif i == len([n for n in nodes if n.status == PathStatus.PENDING]):
                status = PathStatus.IN_PROGRESS
            else:
                status = PathStatus.PENDING
            
            # 推荐资源
            resources = self._recommend_resources(concept)
            
            node = PathNode(
                node_id=f"node_{i}",
                concept=concept,
                order=i,
                status=status,
                recommended_resources=resources,
                estimated_time=concept.estimated_time,
                priority_score=1.0 - (i * 0.01)
            )
            
            nodes.append(node)
            total_time += concept.estimated_time
        
        return LearningPath(
            path_id=f"path_{datetime.now().timestamp()}",
            user_id=self.user_profile.user_id,
            name=f"学习路径: {', '.join(target_concepts[:3])}",
            description=f"针对目标概念的个性化学习路径",
            target_concepts=target_concepts,
            nodes=nodes,
            total_concepts=len(nodes),
            total_estimated_time=total_time,
            progress_percentage=sum(1 for n in nodes if n.status == PathStatus.COMPLETED) / len(nodes) * 100 if nodes else 0
        )
    
    def _recommend_resources(self, concept: ConceptNode) -> List[Dict]:
        """为概念推荐学习资源"""
        resources = []
        
        # 基于认知风格推荐
        style_mapping = {
            'visual': [ResourceType.VIDEO, ResourceType.INTERACTIVE],
            'reading': [ResourceType.TEXT, ResourceType.EXAMPLE],
            'kinesthetic': [ResourceType.INTERACTIVE, ResourceType.EXERCISE],
            'mixed': [ResourceType.TEXT, ResourceType.VIDEO, ResourceType.EXERCISE]
        }
        
        preferred_types = style_mapping.get(
            self.user_profile.cognitive_style.value, 
            [ResourceType.TEXT]
        )
        
        for i, res_type in enumerate(preferred_types[:3]):
            resources.append({
                'id': f"res_{concept.id}_{i}",
                'title': f"{res_type.value.title()} - {concept.name}",
                'type': res_type.value,
                'difficulty': concept.difficulty.value,
                'estimated_time': concept.estimated_time // 3
            })
        
        return resources


class DynamicProgrammingPathGenerator:
    """动态规划路径生成器 - 用于多目标优化"""
    
    def __init__(self, user_profile: UserProfile):
        self.user_profile = user_profile
        self.kg = get_knowledge_graph()
    
    def generate(self, target_concepts: List[str],
                objectives: Dict[str, float] = None) -> Optional[LearningPath]:
        """
        使用动态规划生成最优路径
        
        优化目标：
        - 最短学习时间
        - 最高知识掌握度
        - 最佳学习体验
        
        Args:
            target_concepts: 目标概念
            objectives: 各目标的权重 {'time': 0.3, 'mastery': 0.4, 'experience': 0.3}
        """
        if objectives is None:
            objectives = {'time': 0.3, 'mastery': 0.4, 'experience': 0.3}
        
        # 获取拓扑排序
        all_concepts = set(target_concepts)
        for target in target_concepts:
            all_concepts.update(self.kg.get_prerequisites(target, recursive=True))
        
        topo_order = self.kg.get_learning_sequence(list(all_concepts))
        
        # 动态规划表: dp[i] = 学习到第i个概念的最优状态
        # 状态: (总时间, 总掌握度, 路径)
        dp = {}
        
        # 初始状态
        for concept_id in topo_order:
            if not self.kg.get_prerequisites(concept_id, recursive=False):
                dp[concept_id] = {
                    'time': self._estimate_study_time(concept_id),
                    'mastery': self._estimate_mastery(concept_id),
                    'experience': self._estimate_experience(concept_id),
                    'path': [concept_id]
                }
        
        # 动态规划递推
        for concept_id in topo_order:
            if concept_id in dp:
                continue
            
            prerequisites = self.kg.get_prerequisites(concept_id, recursive=False)
            
            # 找到最佳前置路径
            best_prev = None
            best_score = float('-inf')
            
            for prereq in prerequisites:
                if prereq not in dp:
                    continue
                
                prev_state = dp[prereq]
                new_time = prev_state['time'] + self._estimate_study_time(concept_id)
                new_mastery = (prev_state['mastery'] + self._estimate_mastery(concept_id)) / 2
                new_experience = (prev_state['experience'] + self._estimate_experience(concept_id)) / 2
                
                # 综合评分
                score = (
                    -new_time * objectives['time'] +
                    new_mastery * objectives['mastery'] * 100 +
                    new_experience * objectives['experience'] * 100
                )
                
                if score > best_score:
                    best_score = score
                    best_prev = prereq
            
            if best_prev:
                prev_state = dp[best_prev]
                dp[concept_id] = {
                    'time': prev_state['time'] + self._estimate_study_time(concept_id),
                    'mastery': (prev_state['mastery'] + self._estimate_mastery(concept_id)) / 2,
                    'experience': (prev_state['experience'] + self._estimate_experience(concept_id)) / 2,
                    'path': prev_state['path'] + [concept_id]
                }
        
        # 选择覆盖最多目标的路径
        best_path = None
        best_coverage = 0
        
        for concept_id, state in dp.items():
            if concept_id in target_concepts:
                coverage = len(set(state['path']) & set(target_concepts))
                if coverage > best_coverage:
                    best_coverage = coverage
                    best_path = state['path']
        
        if best_path:
            return self._build_path_from_sequence(best_path, target_concepts)
        
        return None
    
    def _estimate_study_time(self, concept_id: str) -> int:
        """估计学习时间"""
        concept = self.kg.get_concept(concept_id)
        return concept.estimated_time if concept else 30
    
    def _estimate_mastery(self, concept_id: str) -> float:
        """估计掌握度"""
        if concept_id in self.user_profile.mastered_concepts:
            return self.user_profile.mastered_concepts[concept_id]
        
        # 基于先修掌握度估计
        prereqs = self.kg.get_prerequisites(concept_id, recursive=False)
        if not prereqs:
            return 0.5
        
        prereq_mastery = [
            self.user_profile.mastered_concepts.get(p, 0) 
            for p in prereqs
        ]
        return np.mean(prereq_mastery) * 0.9 if prereq_mastery else 0.5
    
    def _estimate_experience(self, concept_id: str) -> float:
        """估计学习体验评分"""
        concept = self.kg.get_concept(concept_id)
        if not concept:
            return 0.5
        
        score = 0.5
        
        # 兴趣匹配
        if concept.branch in self.user_profile.interest_areas:
            score += 0.2
        
        # 难度适中
        levels = ['beginner', 'intermediate', 'advanced', 'expert']
        user_level_idx = levels.index(self.user_profile.current_level.value)
        concept_level_idx = levels.index(concept.difficulty.value)
        
        if abs(user_level_idx - concept_level_idx) <= 1:
            score += 0.2
        
        return min(score, 1.0)
    
    def _build_path_from_sequence(self, sequence: List[str],
                                  targets: List[str]) -> LearningPath:
        """从序列构建学习路径"""
        generator = AStarPathGenerator(self.user_profile)
        return generator._build_learning_path(sequence, targets)


class PathGenerator:
    """路径生成器统一接口"""
    
    def __init__(self, user_profile: UserProfile):
        self.user_profile = user_profile
        self.kg = get_knowledge_graph()
    
    def generate(self, target_concepts: List[str],
                algorithm: str = "astar",
                **kwargs) -> Optional[LearningPath]:
        """
        生成学习路径的统一接口
        
        Args:
            target_concepts: 目标概念列表
            algorithm: 算法类型 ('astar', 'dp', 'rl')
            **kwargs: 额外参数
            
        Returns:
            学习路径对象
        """
        if algorithm == "astar":
            generator = AStarPathGenerator(self.user_profile)
            return generator.generate(target_concepts, **kwargs)
        
        elif algorithm == "dp":
            generator = DynamicProgrammingPathGenerator(self.user_profile)
            return generator.generate(target_concepts, **kwargs)
        
        elif algorithm == "rl":
            # 强化学习算法 (简化版)
            # 实际实现需要训练好的 RL 模型
            generator = AStarPathGenerator(self.user_profile)
            return generator.generate(target_concepts, **kwargs)
        
        else:
            raise ValueError(f"Unknown algorithm: {algorithm}")
    
    def generate_multiple_paths(self, target_concepts: List[str],
                               num_paths: int = 3) -> List[LearningPath]:
        """
        生成多条备选路径
        
        使用不同参数或算法生成多样化的路径选择
        """
        paths = []
        
        # 路径1: A* 标准路径
        path1 = self.generate(target_concepts, algorithm="astar")
        if path1:
            paths.append(path1)
        
        # 路径2: 动态规划优化路径
        path2 = self.generate(target_concepts, algorithm="dp",
                             objectives={'time': 0.5, 'mastery': 0.3, 'experience': 0.2})
        if path2 and path2.path_id != path1.path_id if path1 else True:
            paths.append(path2)
        
        # 路径3: 兴趣导向路径
        # 临时增加兴趣权重
        original_interests = self.user_profile.interest_areas.copy()
        # 添加目标概念所在分支为兴趣
        for concept_id in target_concepts[:2]:
            concept = self.kg.get_concept(concept_id)
            if concept and concept.branch not in self.user_profile.interest_areas:
                self.user_profile.interest_areas.append(concept.branch)
        
        path3 = self.generate(target_concepts, algorithm="astar")
        if path3:
            paths.append(path3)
        
        # 恢复原始兴趣
        self.user_profile.interest_areas = original_interests
        
        return paths[:num_paths]


def generate_learning_path(user_profile: UserProfile,
                          target_concepts: List[str],
                          algorithm: str = "astar") -> Optional[LearningPath]:
    """
    生成个性化学习路径的主函数
    
    Args:
        user_profile: 用户画像
        target_concepts: 目标概念集合
        algorithm: 路径规划算法 ('astar', 'dp', 'rl')
        
    Returns:
        最优学习路径（概念序列+资源推荐）
    """
    generator = PathGenerator(user_profile)
    return generator.generate(target_concepts, algorithm=algorithm)
