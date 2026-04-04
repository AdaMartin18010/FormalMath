"""
知识图谱嵌入模块
使用图神经网络实现知识概念的高效嵌入表示
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime
from collections import defaultdict
import heapq


@dataclass
class ConceptNode:
    """概念节点"""
    concept_id: str
    name: str
    description: str = ""
    difficulty: float = 0.5  # 0-1
    importance: float = 0.5  # 0-1
    category: str = ""
    embedding: Optional[np.ndarray] = None
    
    def to_dict(self) -> Dict:
        return {
            'concept_id': self.concept_id,
            'name': self.name,
            'description': self.description,
            'difficulty': self.difficulty,
            'importance': self.importance,
            'category': self.category,
            'has_embedding': self.embedding is not None
        }


@dataclass
class RelationEdge:
    """关系边"""
    source_id: str
    target_id: str
    relation_type: str  # 'prerequisite', 'related', 'extends', 'part_of'
    weight: float = 1.0
    confidence: float = 1.0
    
    def to_dict(self) -> Dict:
        return {
            'source_id': self.source_id,
            'target_id': self.target_id,
            'relation_type': self.relation_type,
            'weight': self.weight,
            'confidence': self.confidence
        }


class KnowledgeGraph:
    """知识图谱"""
    
    def __init__(self):
        self.nodes: Dict[str, ConceptNode] = {}
        self.edges: Dict[str, List[RelationEdge]] = defaultdict(list)
        self.reverse_edges: Dict[str, List[RelationEdge]] = defaultdict(list)
        
    def add_node(self, node: ConceptNode):
        """添加节点"""
        self.nodes[node.concept_id] = node
        
    def add_edge(self, edge: RelationEdge):
        """添加边"""
        self.edges[edge.source_id].append(edge)
        self.reverse_edges[edge.target_id].append(edge)
        
    def get_neighbors(self, concept_id: str, relation_type: Optional[str] = None) -> List[Tuple[str, float]]:
        """获取邻居节点"""
        if concept_id not in self.edges:
            return []
        
        neighbors = []
        for edge in self.edges[concept_id]:
            if relation_type is None or edge.relation_type == relation_type:
                neighbors.append((edge.target_id, edge.weight))
        return neighbors
    
    def get_prerequisites(self, concept_id: str) -> List[str]:
        """获取前置概念"""
        prereqs = []
        for edge in self.reverse_edges.get(concept_id, []):
            if edge.relation_type == 'prerequisite':
                prereqs.append(edge.source_id)
        return prereqs
    
    def get_all_prerequisites(self, concept_id: str, visited: Optional[Set[str]] = None) -> Set[str]:
        """获取所有前置概念（递归）"""
        if visited is None:
            visited = set()
        
        if concept_id in visited:
            return visited
        
        visited.add(concept_id)
        
        for prereq in self.get_prerequisites(concept_id):
            self.get_all_prerequisites(prereq, visited)
        
        return visited
    
    def topological_sort(self, target_concepts: List[str]) -> List[str]:
        """拓扑排序学习顺序"""
        # 获取所有相关概念（包括前置）
        all_concepts = set()
        for target in target_concepts:
            all_concepts.update(self.get_all_prerequisites(target))
        
        # 计算入度
        in_degree = {cid: 0 for cid in all_concepts}
        for cid in all_concepts:
            for prereq in self.get_prerequisites(cid):
                if prereq in all_concepts:
                    in_degree[cid] += 1
        
        # Kahn算法
        queue = [cid for cid, deg in in_degree.items() if deg == 0]
        result = []
        
        while queue:
            # 按重要性排序
            queue.sort(key=lambda x: self.nodes.get(x, ConceptNode(x, x)).importance, reverse=True)
            current = queue.pop(0)
            result.append(current)
            
            for neighbor, _ in self.get_neighbors(current, 'prerequisite'):
                if neighbor in all_concepts:
                    in_degree[neighbor] -= 1
                    if in_degree[neighbor] == 0:
                        queue.append(neighbor)
        
        return result


class GraphEmbeddingModel:
    """
    图嵌入模型
    使用改进的Node2Vec算法学习概念嵌入
    """
    
    def __init__(
        self,
        embedding_dim: int = 64,
        walk_length: int = 10,
        num_walks: int = 20,
        p: float = 1.0,  # 返回参数
        q: float = 1.0,  # 进出参数
        learning_rate: float = 0.025
    ):
        self.embedding_dim = embedding_dim
        self.walk_length = walk_length
        self.num_walks = num_walks
        self.p = p  # BFS倾向
        self.q = q  # DFS倾向
        self.learning_rate = learning_rate
        
        self.embeddings: Dict[str, np.ndarray] = {}
        self.context_embeddings: Dict[str, np.ndarray] = {}
        
    def fit(self, graph: KnowledgeGraph, epochs: int = 100):
        """训练嵌入"""
        # 初始化嵌入
        for concept_id in graph.nodes.keys():
            self.embeddings[concept_id] = np.random.randn(self.embedding_dim) * 0.01
            self.context_embeddings[concept_id] = np.random.randn(self.embedding_dim) * 0.01
        
        # 生成随机游走
        walks = self._generate_walks(graph)
        
        # 使用Skip-gram训练
        for epoch in range(epochs):
            np.random.shuffle(walks)
            for walk in walks:
                self._skip_gram_update(walk)
            
            # 学习率衰减
            self.learning_rate *= 0.995
    
    def _generate_walks(self, graph: KnowledgeGraph) -> List[List[str]]:
        """生成随机游走序列"""
        walks = []
        nodes = list(graph.nodes.keys())
        
        for _ in range(self.num_walks):
            np.random.shuffle(nodes)
            for node in nodes:
                walk = self._biased_random_walk(graph, node)
                walks.append(walk)
        
        return walks
    
    def _biased_random_walk(self, graph: KnowledgeGraph, start_node: str) -> List[str]:
        """有偏随机游走（Node2Vec）"""
        walk = [start_node]
        
        for _ in range(self.walk_length - 1):
            current = walk[-1]
            neighbors = graph.get_neighbors(current)
            
            if not neighbors:
                break
            
            # 计算转移概率
            if len(walk) == 1:
                # 第一步：均匀采样
                probs = [weight for _, weight in neighbors]
            else:
                # 基于p和q计算有偏概率
                prev = walk[-2]
                probs = []
                for neighbor, weight in neighbors:
                    if neighbor == prev:
                        # 返回前一个节点
                        prob = weight / self.p
                    elif neighbor in [n for n, _ in graph.get_neighbors(prev)]:
                        # 保持局部（BFS）
                        prob = weight
                    else:
                        # 探索新区域（DFS）
                        prob = weight / self.q
                    probs.append(prob)
            
            # 归一化
            total = sum(probs)
            if total > 0:
                probs = [p / total for p in probs]
            else:
                probs = [1.0 / len(neighbors)] * len(neighbors)
            
            # 采样
            next_node = np.random.choice([n for n, _ in neighbors], p=probs)
            walk.append(next_node)
        
        return walk
    
    def _skip_gram_update(self, walk: List[str], window_size: int = 5):
        """Skip-gram负采样更新"""
        for i, target in enumerate(walk):
            if target not in self.embeddings:
                continue
            
            # 上下文窗口
            start = max(0, i - window_size)
            end = min(len(walk), i + window_size + 1)
            
            for j in range(start, end):
                if i != j and walk[j] in self.embeddings:
                    context = walk[j]
                    self._update_pair(target, context, positive=True)
            
            # 负采样
            for _ in range(5):  # 5个负样本
                negative = np.random.choice(list(self.embeddings.keys()))
                if negative not in walk[start:end]:
                    self._update_pair(target, negative, positive=False)
    
    def _update_pair(self, target: str, context: str, positive: bool):
        """更新一对词的嵌入"""
        target_emb = self.embeddings[target]
        context_emb = self.context_embeddings[context]
        
        # 计算梯度
        dot = np.dot(target_emb, context_emb)
        sigmoid = 1 / (1 + np.exp(-dot))
        
        label = 1.0 if positive else 0.0
        grad = self.learning_rate * (label - sigmoid)
        
        # 更新
        self.embeddings[target] += grad * context_emb
        self.context_embeddings[context] += grad * target_emb
    
    def get_embedding(self, concept_id: str) -> Optional[np.ndarray]:
        """获取概念嵌入"""
        return self.embeddings.get(concept_id)
    
    def compute_similarity(self, concept_a: str, concept_b: str) -> float:
        """计算概念相似度"""
        emb_a = self.get_embedding(concept_a)
        emb_b = self.get_embedding(concept_b)
        
        if emb_a is None or emb_b is None:
            return 0.0
        
        # 余弦相似度
        dot = np.dot(emb_a, emb_b)
        norm_a = np.linalg.norm(emb_a)
        norm_b = np.linalg.norm(emb_b)
        
        if norm_a == 0 or norm_b == 0:
            return 0.0
        
        return dot / (norm_a * norm_b)
    
    def find_similar_concepts(
        self,
        concept_id: str,
        top_k: int = 5,
        relation_type: Optional[str] = None
    ) -> List[Tuple[str, float]]:
        """查找相似概念"""
        if concept_id not in self.embeddings:
            return []
        
        similarities = []
        for other_id, other_emb in self.embeddings.items():
            if other_id != concept_id:
                sim = self.compute_similarity(concept_id, other_id)
                similarities.append((other_id, sim))
        
        similarities.sort(key=lambda x: x[1], reverse=True)
        return similarities[:top_k]


class KnowledgeGraphEmbedder:
    """
    知识图谱嵌入器
    整合图结构和嵌入模型
    """
    
    def __init__(self, embedding_dim: int = 64):
        self.graph = KnowledgeGraph()
        self.embedding_model = GraphEmbeddingModel(embedding_dim=embedding_dim)
        self.embedding_dim = embedding_dim
        self.is_fitted = False
        
    def add_concept(self, concept_data: Dict[str, Any]):
        """添加概念"""
        node = ConceptNode(
            concept_id=concept_data['concept_id'],
            name=concept_data.get('name', ''),
            description=concept_data.get('description', ''),
            difficulty=concept_data.get('difficulty', 0.5),
            importance=concept_data.get('importance', 0.5),
            category=concept_data.get('category', '')
        )
        self.graph.add_node(node)
        
        if self.is_fitted:
            # 增量添加嵌入
            self.embedding_model.embeddings[concept_data['concept_id']] = (
                np.random.randn(self.embedding_dim) * 0.01
            )
    
    def add_relation(self, relation_data: Dict[str, Any]):
        """添加关系"""
        edge = RelationEdge(
            source_id=relation_data['source_id'],
            target_id=relation_data['target_id'],
            relation_type=relation_data['relation_type'],
            weight=relation_data.get('weight', 1.0),
            confidence=relation_data.get('confidence', 1.0)
        )
        self.graph.add_edge(edge)
    
    def fit_embeddings(self, epochs: int = 100):
        """训练嵌入"""
        if len(self.graph.nodes) < 2:
            return
        
        self.embedding_model.fit(self.graph, epochs=epochs)
        
        # 更新节点嵌入
        for concept_id, node in self.graph.nodes.items():
            node.embedding = self.embedding_model.get_embedding(concept_id)
        
        self.is_fitted = True
    
    def get_concept_embedding(self, concept_id: str) -> Optional[np.ndarray]:
        """获取概念嵌入"""
        return self.embedding_model.get_embedding(concept_id)
    
    def get_learning_path_prerequisites(self, target_concepts: List[str]) -> List[str]:
        """获取学习路径的前置概念序列"""
        return self.graph.topological_sort(target_concepts)
    
    def get_prerequisite_chain(
        self,
        target_concept: str,
        known_concepts: Set[str]
    ) -> List[str]:
        """获取从已知概念到目标概念的前置链"""
        # BFS查找最短路径
        if target_concept in known_concepts:
            return []
        
        # 构建图用于路径查找
        queue = [(target_concept, [target_concept])]
        visited = {target_concept}
        
        while queue:
            current, path = queue.pop(0)
            
            prereqs = self.graph.get_prerequisites(current)
            
            # 优先选择已知的前置概念
            for prereq in prereqs:
                if prereq in known_concepts:
                    return path[::-1]
            
            # 否则继续BFS
            for prereq in prereqs:
                if prereq not in visited:
                    visited.add(prereq)
                    queue.append((prereq, path + [prereq]))
        
        return []
    
    def compute_path_difficulty(
        self,
        path: List[str],
        user_abilities: Optional[Dict[str, float]] = None
    ) -> float:
        """计算路径难度"""
        if not path:
            return 0.0
        
        total_difficulty = 0.0
        
        for concept_id in path:
            if concept_id in self.graph.nodes:
                node = self.graph.nodes[concept_id]
                base_difficulty = node.difficulty
                
                # 如果有用户能力数据，调整难度
                if user_abilities and concept_id in user_abilities:
                    ability = user_abilities[concept_id]
                    adjusted_difficulty = base_difficulty * (1 - ability * 0.5)
                else:
                    adjusted_difficulty = base_difficulty
                
                total_difficulty += adjusted_difficulty
        
        return total_difficulty / len(path)
    
    def recommend_next_concepts(
        self,
        current_concepts: Set[str],
        target_concepts: Set[str],
        top_k: int = 5
    ) -> List[Dict]:
        """推荐下一步学习的概念"""
        recommendations = []
        
        for target in target_concepts:
            if target in current_concepts:
                continue
            
            # 获取前置链
            prereq_chain = self.get_prerequisite_chain(target, current_concepts)
            
            if prereq_chain:
                next_concept = prereq_chain[0]
                
                # 计算优先级分数
                importance = self.graph.nodes.get(target, ConceptNode(target, target)).importance
                chain_length = len(prereq_chain)
                
                # 越短的前置链优先级越高
                priority = importance / (chain_length + 1)
                
                recommendations.append({
                    'concept_id': next_concept,
                    'target_concept': target,
                    'prerequisite_chain': prereq_chain,
                    'chain_length': chain_length,
                    'priority_score': priority
                })
        
        # 按优先级排序
        recommendations.sort(key=lambda x: x['priority_score'], reverse=True)
        return recommendations[:top_k]
    
    def export_graph(self) -> Dict:
        """导出图谱"""
        return {
            'nodes': {cid: node.to_dict() for cid, node in self.graph.nodes.items()},
            'edges': [
                edge.to_dict() 
                for edges in self.graph.edges.values() 
                for edge in edges
            ],
            'is_fitted': self.is_fitted,
            'embedding_dim': self.embedding_dim
        }
