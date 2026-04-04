"""
多目标优化系统
时间效率vs掌握深度、广度vs深度、兴趣vs基础
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import random


class ObjectiveType(str, Enum):
    """目标类型"""
    TIME_EFFICIENCY = "time_efficiency"
    MASTERY_DEPTH = "mastery_depth"
    BREADTH = "breadth"
    INTEREST = "interest"
    FOUNDATION = "foundation"


@dataclass
class ObjectiveBalance:
    """目标平衡配置"""
    time_vs_depth: float = 0.5  # 0=时间优先, 1=深度优先
    breadth_vs_depth: float = 0.5  # 0=广度优先, 1=深度优先
    interest_vs_foundation: float = 0.5  # 0=兴趣优先, 1=基础优先
    
    def to_vector(self) -> np.ndarray:
        return np.array([
            self.time_vs_depth,
            self.breadth_vs_depth,
            self.interest_vs_foundation
        ])


@dataclass
class LearningObjective:
    """学习目标"""
    name: str
    objective_type: ObjectiveType
    weight: float
    target_value: float
    current_value: float = 0.0
    
    def calculate_fitness(self) -> float:
        """计算适应度"""
        if self.target_value == 0:
            return 1.0 if self.current_value == 0 else 0.0
        
        ratio = self.current_value / self.target_value
        # 使用sigmoid平滑
        return 1 / (1 + np.exp(-5 * (ratio - 1)))


@dataclass
class LearningPath:
    """学习路径（用于优化）"""
    nodes: List[Dict]
    objectives: Dict[str, float] = field(default_factory=dict)
    fitness: float = 0.0
    
    def clone(self) -> 'LearningPath':
        return LearningPath(
            nodes=self.nodes.copy(),
            objectives=self.objectives.copy(),
            fitness=self.fitness
        )


class MultiObjectiveOptimizer:
    """
    多目标优化器
    
    使用NSGA-II风格的多目标遗传算法
    """
    
    def __init__(
        self,
        population_size: int = 50,
        generations: int = 100,
        crossover_rate: float = 0.8,
        mutation_rate: float = 0.2,
        elitism_ratio: float = 0.1
    ):
        self.population_size = population_size
        self.generations = generations
        self.crossover_rate = crossover_rate
        self.mutation_rate = mutation_rate
        self.elitism_ratio = elitism_ratio
        
        # 目标函数
        self.objective_functions: Dict[str, Callable] = {}
        
        # 约束函数
        self.constraints: List[Callable] = []
    
    def add_objective(self, name: str, func: Callable):
        """添加目标函数"""
        self.objective_functions[name] = func
    
    def add_constraint(self, func: Callable):
        """添加约束"""
        self.constraints.append(func)
    
    def optimize(
        self,
        available_nodes: List[Dict],
        user_balance: ObjectiveBalance,
        fixed_start: Optional[Dict] = None,
        fixed_end: Optional[Dict] = None
    ) -> List[LearningPath]:
        """
        执行多目标优化
        
        Args:
            available_nodes: 可用节点
            user_balance: 用户目标偏好
            fixed_start: 固定起始节点
            fixed_end: 固定结束节点
        
        Returns:
            Pareto前沿解集
        """
        # 初始化种群
        population = self._initialize_population(
            available_nodes, fixed_start, fixed_end
        )
        
        # 进化
        for generation in range(self.generations):
            # 评估
            self._evaluate_population(population, user_balance)
            
            # 非支配排序
            fronts = self._non_dominated_sort(population)
            
            # 选择
            selected = self._tournament_selection(population, fronts)
            
            # 交叉和变异
            offspring = self._crossover_and_mutate(
                selected, available_nodes
            )
            
            # 精英保留
            elite_count = int(self.elitism_ratio * self.population_size)
            if fronts and len(fronts[0]) > 0:
                elites = [population[i] for i in fronts[0][:elite_count]]
            else:
                elites = []
            
            # 新种群
            population = elites + offspring[:self.population_size - len(elites)]
        
        # 最终评估
        self._evaluate_population(population, user_balance)
        fronts = self._non_dominated_sort(population)
        
        # 返回Pareto前沿
        if fronts:
            return [population[i] for i in fronts[0]]
        return population[:5]
    
    def _initialize_population(
        self,
        available_nodes: List[Dict],
        fixed_start: Optional[Dict],
        fixed_end: Optional[Dict]
    ) -> List[LearningPath]:
        """初始化种群"""
        population = []
        
        for _ in range(self.population_size):
            # 随机生成路径
            path_length = random.randint(5, min(20, len(available_nodes)))
            
            nodes = random.sample(available_nodes, path_length)
            
            # 添加固定节点
            if fixed_start:
                nodes.insert(0, fixed_start)
            if fixed_end:
                nodes.append(fixed_end)
            
            population.append(LearningPath(nodes=nodes))
        
        return population
    
    def _evaluate_population(
        self,
        population: List[LearningPath],
        user_balance: ObjectiveBalance
    ):
        """评估种群"""
        for individual in population:
            # 检查约束
            valid = all(constraint(individual) for constraint in self.constraints)
            
            if not valid:
                individual.fitness = 0
                individual.objectives = {name: 0 for name in self.objective_functions.keys()}
                continue
            
            # 计算各目标
            objectives = {}
            for name, func in self.objective_functions.items():
                objectives[name] = func(individual)
            
            individual.objectives = objectives
            
            # 综合适应度（加权）
            individual.fitness = self._calculate_weighted_fitness(
                objectives, user_balance
            )
    
    def _calculate_weighted_fitness(
        self,
        objectives: Dict[str, float],
        balance: ObjectiveBalance
    ) -> float:
        """计算加权适应度"""
        # 根据用户偏好调整权重
        time_weight = 1 - balance.time_vs_depth
        depth_weight = balance.time_vs_depth
        breadth_weight = 1 - balance.breadth_vs_depth
        depth2_weight = balance.breadth_vs_depth
        interest_weight = 1 - balance.interest_vs_foundation
        foundation_weight = balance.interest_vs_foundation
        
        weights = {
            'time_efficiency': time_weight * 0.5,
            'mastery_depth': depth_weight * 0.5,
            'breadth': breadth_weight * 0.3,
            'knowledge_depth': depth2_weight * 0.3,
            'interest_alignment': interest_weight * 0.2,
            'foundation_strength': foundation_weight * 0.2
        }
        
        total_fitness = 0
        total_weight = 0
        
        for obj_name, obj_value in objectives.items():
            weight = weights.get(obj_name, 0.1)
            total_fitness += weight * obj_value
            total_weight += weight
        
        return total_fitness / total_weight if total_weight > 0 else 0
    
    def _non_dominated_sort(self, population: List[LearningPath]) -> List[List[int]]:
        """非支配排序"""
        n = len(population)
        domination_count = [0] * n
        dominated_solutions = [[] for _ in range(n)]
        fronts = [[]]
        
        for i in range(n):
            for j in range(i + 1, n):
                if self._dominates(population[i], population[j]):
                    dominated_solutions[i].append(j)
                    domination_count[j] += 1
                elif self._dominates(population[j], population[i]):
                    dominated_solutions[j].append(i)
                    domination_count[i] += 1
            
            if domination_count[i] == 0:
                fronts[0].append(i)
        
        i = 0
        while len(fronts[i]) > 0:
            next_front = []
            for p in fronts[i]:
                for q in dominated_solutions[p]:
                    domination_count[q] -= 1
                    if domination_count[q] == 0:
                        next_front.append(q)
            i += 1
            fronts.append(next_front)
        
        return fronts[:-1]  # 去掉空的最后一层
    
    def _dominates(self, a: LearningPath, b: LearningPath) -> bool:
        """判断a是否支配b"""
        better_in_one = False
        
        for obj_name in self.objective_functions.keys():
            val_a = a.objectives.get(obj_name, 0)
            val_b = b.objectives.get(obj_name, 0)
            
            if val_a < val_b:
                return False
            elif val_a > val_b:
                better_in_one = True
        
        return better_in_one
    
    def _tournament_selection(
        self,
        population: List[LearningPath],
        fronts: List[List[int]],
        tournament_size: int = 3
    ) -> List[LearningPath]:
        """锦标赛选择"""
        selected = []
        
        while len(selected) < self.population_size:
            # 随机选择tournament_size个个体
            candidates = random.sample(range(len(population)), 
                                     min(tournament_size, len(population)))
            
            # 选择最好的（层级越低越好，同层级适应度越高越好）
            best = candidates[0]
            best_rank = self._get_rank(best, fronts)
            
            for c in candidates[1:]:
                rank = self._get_rank(c, fronts)
                if rank < best_rank:
                    best = c
                    best_rank = rank
                elif rank == best_rank:
                    if population[c].fitness > population[best].fitness:
                        best = c
            
            selected.append(population[best])
        
        return selected
    
    def _get_rank(self, idx: int, fronts: List[List[int]]) -> int:
        """获取个体的Pareto层级"""
        for rank, front in enumerate(fronts):
            if idx in front:
                return rank
        return len(fronts)
    
    def _crossover_and_mutate(
        self,
        parents: List[LearningPath],
        available_nodes: List[Dict]
    ) -> List[LearningPath]:
        """交叉和变异"""
        offspring = []
        
        for i in range(0, len(parents) - 1, 2):
            parent1 = parents[i]
            parent2 = parents[i + 1]
            
            if random.random() < self.crossover_rate:
                child1, child2 = self._crossover(parent1, parent2)
            else:
                child1, child2 = parent1.clone(), parent2.clone()
            
            # 变异
            if random.random() < self.mutation_rate:
                child1 = self._mutate(child1, available_nodes)
            if random.random() < self.mutation_rate:
                child2 = self._mutate(child2, available_nodes)
            
            offspring.extend([child1, child2])
        
        return offspring
    
    def _crossover(
        self,
        parent1: LearningPath,
        parent2: LearningPath
    ) -> Tuple[LearningPath, LearningPath]:
        """交叉操作"""
        # 单点交叉
        min_len = min(len(parent1.nodes), len(parent2.nodes))
        if min_len < 2:
            return parent1.clone(), parent2.clone()
        
        point = random.randint(1, min_len - 1)
        
        child1_nodes = parent1.nodes[:point] + parent2.nodes[point:]
        child2_nodes = parent2.nodes[:point] + parent1.nodes[point:]
        
        # 去重
        seen = set()
        child1_nodes_unique = []
        for node in child1_nodes:
            node_id = node.get('id', str(node))
            if node_id not in seen:
                seen.add(node_id)
                child1_nodes_unique.append(node)
        
        seen = set()
        child2_nodes_unique = []
        for node in child2_nodes:
            node_id = node.get('id', str(node))
            if node_id not in seen:
                seen.add(node_id)
                child2_nodes_unique.append(node)
        
        return (
            LearningPath(nodes=child1_nodes_unique),
            LearningPath(nodes=child2_nodes_unique)
        )
    
    def _mutate(
        self,
        individual: LearningPath,
        available_nodes: List[Dict]
    ) -> LearningPath:
        """变异操作"""
        mutated = individual.clone()
        
        mutation_type = random.choice(['swap', 'insert', 'remove', 'replace'])
        
        if mutation_type == 'swap' and len(mutated.nodes) >= 2:
            # 交换两个节点
            i, j = random.sample(range(len(mutated.nodes)), 2)
            mutated.nodes[i], mutated.nodes[j] = mutated.nodes[j], mutated.nodes[i]
        
        elif mutation_type == 'insert':
            # 插入新节点
            new_node = random.choice(available_nodes)
            pos = random.randint(0, len(mutated.nodes))
            mutated.nodes.insert(pos, new_node)
        
        elif mutation_type == 'remove' and len(mutated.nodes) > 3:
            # 移除节点
            pos = random.randint(0, len(mutated.nodes) - 1)
            mutated.nodes.pop(pos)
        
        elif mutation_type == 'replace' and mutated.nodes:
            # 替换节点
            pos = random.randint(0, len(mutated.nodes) - 1)
            new_node = random.choice(available_nodes)
            mutated.nodes[pos] = new_node
        
        return mutated


class LearningPathOptimizer:
    """
    学习路径优化器（应用层）
    
    将多目标优化应用于学习路径规划
    """
    
    def __init__(self, knowledge_graph=None):
        self.knowledge_graph = knowledge_graph
        self.optimizer = MultiObjectiveOptimizer()
        self._setup_default_objectives()
    
    def _setup_default_objectives(self):
        """设置默认目标函数"""
        # 时间效率：路径长度越短越好
        self.optimizer.add_objective(
            'time_efficiency',
            lambda path: 1 / (1 + len(path.nodes) * 0.1)  # 节点数越少越好
        )
        
        # 掌握深度：覆盖的知识点深度
        self.optimizer.add_objective(
            'mastery_depth',
            lambda path: np.mean([
                node.get('depth', 0.5) for node in path.nodes
            ])
        )
        
        # 广度：覆盖的概念数量
        self.optimizer.add_objective(
            'breadth',
            lambda path: len(set(
                node.get('concept_id') for node in path.nodes
            )) / max(len(path.nodes), 1)
        )
        
        # 知识深度：平均难度
        self.optimizer.add_objective(
            'knowledge_depth',
            lambda path: np.mean([
                node.get('difficulty', 0.5) for node in path.nodes
            ])
        )
        
        # 兴趣匹配
        self.optimizer.add_objective(
            'interest_alignment',
            lambda path: np.mean([
                node.get('interest_score', 0.5) for node in path.nodes
            ])
        )
        
        # 基础强度：前置知识覆盖
        self.optimizer.add_objective(
            'foundation_strength',
            lambda path: np.mean([
                node.get('foundation_score', 0.5) for node in path.nodes
            ])
        )
        
        # 添加约束
        self.optimizer.add_constraint(
            lambda path: len(path.nodes) >= 3  # 最少3个节点
        )
        self.optimizer.add_constraint(
            lambda path: len(path.nodes) <= 30  # 最多30个节点
        )
    
    def optimize_path(
        self,
        user_id: str,
        target_concepts: List[str],
        user_preferences: ObjectiveBalance,
        time_budget: Optional[int] = None,
        current_knowledge: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        优化学习路径
        
        Args:
            user_id: 用户ID
            target_concepts: 目标概念
            user_preferences: 用户偏好
            time_budget: 时间预算（分钟）
            current_knowledge: 当前知识状态
        
        Returns:
            优化结果
        """
        # 获取可用节点
        available_nodes = self._get_available_nodes(
            target_concepts, current_knowledge
        )
        
        # 根据时间预算调整
        if time_budget:
            # 估计每个节点的时间，过滤
            available_nodes = [
                n for n in available_nodes
                if n.get('estimated_time', 30) <= time_budget / 3
            ]
        
        # 执行优化
        pareto_front = self.optimizer.optimize(
            available_nodes=available_nodes,
            user_balance=user_preferences
        )
        
        if not pareto_front:
            return {'error': 'No valid paths found'}
        
        # 选择最佳路径（基于用户偏好的加权）
        best_path = max(pareto_front, key=lambda p: p.fitness)
        
        # 生成不同侧重点的备选方案
        alternatives = self._generate_alternatives(pareto_front)
        
        return {
            'user_id': user_id,
            'optimal_path': {
                'nodes': best_path.nodes,
                'fitness': best_path.fitness,
                'objectives': best_path.objectives,
                'estimated_time': sum(
                    n.get('estimated_time', 30) for n in best_path.nodes
                )
            },
            'alternatives': alternatives,
            'trade_off_analysis': self._analyze_trade_offs(best_path.objectives),
            'pareto_front_size': len(pareto_front)
        }
    
    def _get_available_nodes(
        self,
        target_concepts: List[str],
        current_knowledge: Optional[Dict]
    ) -> List[Dict]:
        """获取可用学习节点"""
        nodes = []
        
        # 从知识图谱获取节点
        if self.knowledge_graph:
            # 这里应该查询知识图谱
            # 简化示例
            for concept_id in target_concepts:
                nodes.append({
                    'id': f'{concept_id}_basic',
                    'concept_id': concept_id,
                    'difficulty': 0.3,
                    'depth': 0.4,
                    'estimated_time': 20,
                    'type': 'basic'
                })
                nodes.append({
                    'id': f'{concept_id}_advanced',
                    'concept_id': concept_id,
                    'difficulty': 0.7,
                    'depth': 0.8,
                    'estimated_time': 40,
                    'type': 'advanced'
                })
        
        return nodes
    
    def _generate_alternatives(
        self,
        pareto_front: List[LearningPath]
    ) -> List[Dict]:
        """生成备选方案"""
        alternatives = []
        
        # 按不同目标排序
        for objective in ['time_efficiency', 'mastery_depth', 'breadth']:
            sorted_paths = sorted(
                pareto_front,
                key=lambda p: p.objectives.get(objective, 0),
                reverse=True
            )
            
            if sorted_paths:
                best = sorted_paths[0]
                alternatives.append({
                    'focus': objective,
                    'fitness': best.fitness,
                    'objectives': best.objectives,
                    'node_count': len(best.nodes),
                    'nodes': [
                        {'id': n.get('id'), 'concept_id': n.get('concept_id')}
                        for n in best.nodes[:5]  # 只显示前5个
                    ]
                })
        
        return alternatives
    
    def _analyze_trade_offs(self, objectives: Dict[str, float]) -> Dict[str, Any]:
        """分析权衡关系"""
        analysis = {
            'primary_strengths': [],
            'trade_offs': [],
            'suggestions': []
        }
        
        # 找出强项
        for obj, val in objectives.items():
            if val > 0.8:
                analysis['primary_strengths'].append(obj)
        
        # 分析权衡
        time_eff = objectives.get('time_efficiency', 0)
        depth = objectives.get('mastery_depth', 0)
        
        if time_eff > 0.7 and depth < 0.5:
            analysis['trade_offs'].append({
                'type': 'time_vs_depth',
                'description': '选择了时间效率，但可能牺牲了一些掌握深度',
                'suggestion': '如果时间允许，可以考虑增加复习环节'
            })
        elif depth > 0.7 and time_eff < 0.5:
            analysis['trade_offs'].append({
                'type': 'depth_vs_time',
                'description': '追求深度掌握，需要更多时间投入',
                'suggestion': '建议分阶段完成，避免疲劳'
            })
        
        return analysis
    
    def balance_objectives(
        self,
        current_objectives: Dict[str, float],
        target_improvement: str,
        max_degradation: float = 0.2
    ) -> Dict[str, Any]:
        """
        平衡多个目标
        
        Args:
            current_objectives: 当前目标值
            target_improvement: 希望改进的目标
            max_degradation: 其他目标最大可接受降低
        
        Returns:
            平衡建议
        """
        suggestions = {
            'current_state': current_objectives,
            'target': target_improvement,
            'recommended_adjustments': [],
            'expected_outcomes': {}
        }
        
        # 根据目标类型给出建议
        if target_improvement == 'time_efficiency':
            suggestions['recommended_adjustments'] = [
                '减少非核心内容的学习',
                '使用更简洁的学习材料',
                '跳过已掌握的前置知识'
            ]
            suggestions['expected_outcomes'] = {
                'time_efficiency': min(1.0, current_objectives.get('time_efficiency', 0) + 0.2),
                'mastery_depth': max(0, current_objectives.get('mastery_depth', 0) - 0.1),
                'note': '预计节省20-30%时间，深度可能略微下降'
            }
        
        elif target_improvement == 'mastery_depth':
            suggestions['recommended_adjustments'] = [
                '增加练习和巩固环节',
                '添加拓展阅读材料',
                '安排复习间隔'
            ]
            suggestions['expected_outcomes'] = {
                'mastery_depth': min(1.0, current_objectives.get('mastery_depth', 0) + 0.25),
                'time_efficiency': max(0, current_objectives.get('time_efficiency', 0) - 0.15),
                'note': '预计深度提升25%，时间增加15-20%'
            }
        
        return suggestions


def create_default_objective_balance(
    learning_goal: str = 'balanced'
) -> ObjectiveBalance:
    """
    创建默认目标平衡配置
    
    Args:
        learning_goal: 学习目标类型
            - 'quick': 快速掌握
            - 'thorough': 深入掌握
            - 'explore': 广泛探索
            - 'balanced': 平衡
    
    Returns:
        目标平衡配置
    """
    presets = {
        'quick': ObjectiveBalance(
            time_vs_depth=0.2,      # 时间优先
            breadth_vs_depth=0.3,   # 略广
            interest_vs_foundation=0.5
        ),
        'thorough': ObjectiveBalance(
            time_vs_depth=0.8,      # 深度优先
            breadth_vs_depth=0.8,   # 深度优先
            interest_vs_foundation=0.6  # 略偏基础
        ),
        'explore': ObjectiveBalance(
            time_vs_depth=0.5,
            breadth_vs_depth=0.2,   # 广度优先
            interest_vs_foundation=0.3  # 兴趣优先
        ),
        'balanced': ObjectiveBalance(
            time_vs_depth=0.5,
            breadth_vs_depth=0.5,
            interest_vs_foundation=0.5
        )
    }
    
    return presets.get(learning_goal, presets['balanced'])
