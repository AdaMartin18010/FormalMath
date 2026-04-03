"""
知识图谱模型
定义概念节点、关系边、知识图谱结构
"""

from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, field
from enum import Enum
import uuid


class RelationType(Enum):
    """关系类型"""
    PREREQUISITE = "prerequisite"  # 先修关系
    RELATED = "related"            # 相关关系
    LEADS_TO = "leads_to"          # 导向关系
    PART_OF = "part_of"            # 组成部分
    EXTENDS = "extends"            # 扩展关系
    APPLICATION = "application"    # 应用关系


class DifficultyLevel(Enum):
    """难度级别"""
    BEGINNER = 1      # 初级
    INTERMEDIATE = 2  # 中级
    ADVANCED = 3      # 高级
    RESEARCH = 4      # 研究级


@dataclass
class ConceptNode:
    """概念节点"""
    concept_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""  # 概念名称
    msc_code: str = ""  # MSC分类编码
    description: str = ""  # 概念描述
    difficulty: DifficultyLevel = DifficultyLevel.BEGINNER  # 难度级别
    estimated_time_minutes: int = 60  # 预计学习时间（分钟）
    
    # 内容资源
    resources: Dict[str, List[str]] = field(default_factory=dict)  # 资源列表
    # 格式: {"text": [...], "video": [...], "interactive": [...], "exercise": [...]}
    
    # 元数据
    tags: List[str] = field(default_factory=list)
    keywords: List[str] = field(default_factory=list)
    
    def get_resources_by_style(self, style: str) -> List[str]:
        """根据学习风格获取推荐资源"""
        style_mapping = {
            "visual": ["video", "interactive", "diagram"],
            "auditory": ["audio", "video"],
            "kinesthetic": ["interactive", "exercise", "project"],
            "reading": ["text", "paper"]
        }
        resource_types = style_mapping.get(style, ["text"])
        resources = []
        for rt in resource_types:
            resources.extend(self.resources.get(rt, []))
        return resources


@dataclass
class RelationEdge:
    """关系边"""
    edge_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    source_id: str = ""  # 源概念ID
    target_id: str = ""  # 目标概念ID
    relation_type: RelationType = RelationType.RELATED
    weight: float = 1.0  # 关系权重 (0-1)
    strength: float = 1.0  # 关系强度 (0-1)
    description: str = ""  # 关系描述
    
    def is_prerequisite(self) -> bool:
        """判断是否为先修关系"""
        return self.relation_type == RelationType.PREREQUISITE
    
    def is_strong_relation(self, threshold: float = 0.7) -> bool:
        """判断是否为强关系"""
        return self.strength >= threshold


@dataclass
class KnowledgeGraph:
    """知识图谱"""
    graph_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = "FormalMath Knowledge Graph"
    version: str = "1.0"
    
    nodes: Dict[str, ConceptNode] = field(default_factory=dict)  # 概念节点字典
    edges: Dict[str, RelationEdge] = field(default_factory=dict)  # 关系边字典
    
    # 邻接表表示
    adjacency_list: Dict[str, List[str]] = field(default_factory=dict)  # 出边
    reverse_adjacency: Dict[str, List[str]] = field(default_factory=dict)  # 入边
    
    def add_node(self, node: ConceptNode) -> str:
        """添加概念节点"""
        self.nodes[node.concept_id] = node
        if node.concept_id not in self.adjacency_list:
            self.adjacency_list[node.concept_id] = []
        if node.concept_id not in self.reverse_adjacency:
            self.reverse_adjacency[node.concept_id] = []
        return node.concept_id
    
    def add_edge(self, edge: RelationEdge) -> str:
        """添加关系边"""
        self.edges[edge.edge_id] = edge
        
        # 更新邻接表
        if edge.source_id not in self.adjacency_list:
            self.adjacency_list[edge.source_id] = []
        if edge.target_id not in self.adjacency_list[edge.source_id]:
            self.adjacency_list[edge.source_id].append(edge.target_id)
        
        # 更新反向邻接表
        if edge.target_id not in self.reverse_adjacency:
            self.reverse_adjacency[edge.target_id] = []
        if edge.source_id not in self.reverse_adjacency[edge.target_id]:
            self.reverse_adjacency[edge.target_id].append(edge.source_id)
        
        return edge.edge_id
    
    def get_node(self, concept_id: str) -> Optional[ConceptNode]:
        """获取概念节点"""
        return self.nodes.get(concept_id)
    
    def get_neighbors(self, concept_id: str) -> List[str]:
        """获取邻接概念"""
        return self.adjacency_list.get(concept_id, [])
    
    def get_prerequisites(self, concept_id: str) -> List[str]:
        """获取先修概念"""
        prereqs = []
        for source_id in self.reverse_adjacency.get(concept_id, []):
            for edge in self.edges.values():
                if edge.source_id == source_id and edge.target_id == concept_id:
                    if edge.is_prerequisite():
                        prereqs.append(source_id)
                        break
        return prereqs
    
    def get_prerequisite_graph(self, concept_id: str) -> Set[str]:
        """获取概念的所有先修概念（递归）"""
        visited = set()
        stack = [concept_id]
        
        while stack:
            current = stack.pop()
            if current not in visited:
                visited.add(current)
                prereqs = self.get_prerequisites(current)
                stack.extend(prereqs)
        
        visited.remove(concept_id)
        return visited
    
    def topological_sort(self, concept_ids: List[str]) -> List[str]:
        """拓扑排序概念列表"""
        # 构建子图的入度
        in_degree = {cid: 0 for cid in concept_ids}
        sub_adj = {cid: [] for cid in concept_ids}
        
        for cid in concept_ids:
            for neighbor in self.adjacency_list.get(cid, []):
                if neighbor in concept_ids:
                    sub_adj[cid].append(neighbor)
                    in_degree[neighbor] += 1
        
        # Kahn算法
        queue = [cid for cid, degree in in_degree.items() if degree == 0]
        result = []
        
        while queue:
            # 按难度排序，确保先学简单的
            queue.sort(key=lambda x: self.nodes[x].difficulty.value)
            current = queue.pop(0)
            result.append(current)
            
            for neighbor in sub_adj[current]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)
        
        return result if len(result) == len(concept_ids) else concept_ids
    
    def get_path_weight(self, path: List[str]) -> float:
        """计算路径权重"""
        weight = 0.0
        for i in range(len(path) - 1):
            for edge in self.edges.values():
                if edge.source_id == path[i] and edge.target_id == path[i + 1]:
                    weight += edge.weight
                    break
        return weight
    
    def get_concepts_by_difficulty(self, difficulty: DifficultyLevel) -> List[str]:
        """获取特定难度的所有概念"""
        return [
            cid for cid, node in self.nodes.items()
            if node.difficulty == difficulty
        ]
    
    def get_concepts_by_msc(self, msc_prefix: str) -> List[str]:
        """根据MSC编码前缀获取概念"""
        return [
            cid for cid, node in self.nodes.items()
            if node.msc_code.startswith(msc_prefix)
        ]
    
    def calculate_complexity(self, concept_id: str) -> float:
        """计算概念复杂度（基于先修关系数量）"""
        prereqs = self.get_prerequisite_graph(concept_id)
        return len(prereqs) / max(len(self.nodes), 1)
    
    def export_to_networkx(self):
        """导出为NetworkX图"""
        try:
            import networkx as nx
            
            G = nx.DiGraph()
            
            # 添加节点
            for cid, node in self.nodes.items():
                G.add_node(cid, 
                          name=node.name,
                          difficulty=node.difficulty.value,
                          msc_code=node.msc_code)
            
            # 添加边
            for edge in self.edges.values():
                G.add_edge(edge.source_id, edge.target_id,
                          weight=edge.weight,
                          relation_type=edge.relation_type.value,
                          strength=edge.strength)
            
            return G
        except ImportError:
            raise ImportError("NetworkX is required for graph export")


# 预定义的FormalMath知识概念（示例）
FORMALMATH_CONCEPTS = [
    {
        "name": "集合",
        "msc_code": "03E99",
        "difficulty": DifficultyLevel.BEGINNER,
        "estimated_time_minutes": 45,
        "description": "数学对象的集合，是数学的基础概念"
    },
    {
        "name": "函数",
        "msc_code": "03E20",
        "difficulty": DifficultyLevel.BEGINNER,
        "estimated_time_minutes": 60,
        "description": "映射关系，将一个集合的元素映射到另一个集合"
    },
    {
        "name": "关系",
        "msc_code": "03E20",
        "difficulty": DifficultyLevel.BEGINNER,
        "estimated_time_minutes": 50,
        "description": "集合元素之间的关系"
    },
    {
        "name": "群",
        "msc_code": "20A05",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 120,
        "description": "具有运算的代数结构"
    },
    {
        "name": "环",
        "msc_code": "13A99",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 120,
        "description": "具有两种运算的代数结构"
    },
    {
        "name": "域",
        "msc_code": "12E99",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 100,
        "description": "可逆的交换环"
    },
    {
        "name": "向量空间",
        "msc_code": "15A03",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 120,
        "description": "域上的向量集合"
    },
    {
        "name": "拓扑空间",
        "msc_code": "54A99",
        "difficulty": DifficultyLevel.ADVANCED,
        "estimated_time_minutes": 150,
        "description": "具有拓扑结构的集合"
    },
    {
        "name": "度量空间",
        "msc_code": "54E35",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 100,
        "description": "具有度量函数的集合"
    },
    {
        "name": "范畴",
        "msc_code": "18A05",
        "difficulty": DifficultyLevel.ADVANCED,
        "estimated_time_minutes": 180,
        "description": "对象和态射的数学结构"
    },
    {
        "name": "极限",
        "msc_code": "26A03",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 120,
        "description": "序列或函数的极限行为"
    },
    {
        "name": "连续性",
        "msc_code": "26A15",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 100,
        "description": "函数的连续性"
    },
    {
        "name": "可微性",
        "msc_code": "26A24",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 120,
        "description": "函数的可微性"
    },
    {
        "name": "积分",
        "msc_code": "26A42",
        "difficulty": DifficultyLevel.INTERMEDIATE,
        "estimated_time_minutes": 150,
        "description": "函数的积分"
    },
    {
        "name": "同调代数",
        "msc_code": "18Gxx",
        "difficulty": DifficultyLevel.RESEARCH,
        "estimated_time_minutes": 300,
        "description": "使用同调方法研究代数结构"
    }
]


# 预定义的关系边（示例）
FORMALMATH_RELATIONS = [
    {"source": "集合", "target": "函数", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "集合", "target": "关系", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "函数", "target": "群", "type": RelationType.PREREQUISITE, "weight": 0.7, "strength": 0.9},
    {"source": "关系", "target": "群", "type": RelationType.PREREQUISITE, "weight": 0.5, "strength": 0.7},
    {"source": "群", "target": "环", "type": RelationType.PREREQUISITE, "weight": 0.8, "strength": 0.9},
    {"source": "环", "target": "域", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "域", "target": "向量空间", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "集合", "target": "拓扑空间", "type": RelationType.PREREQUISITE, "weight": 0.8, "strength": 0.9},
    {"source": "拓扑空间", "target": "度量空间", "type": RelationType.LEADS_TO, "weight": 0.6, "strength": 0.7},
    {"source": "集合", "target": "范畴", "type": RelationType.PREREQUISITE, "weight": 0.7, "strength": 0.8},
    {"source": "函数", "target": "范畴", "type": RelationType.PREREQUISITE, "weight": 0.8, "strength": 0.9},
    {"source": "极限", "target": "连续性", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "连续性", "target": "可微性", "type": RelationType.PREREQUISITE, "weight": 0.9, "strength": 1.0},
    {"source": "可微性", "target": "积分", "type": RelationType.RELATED, "weight": 0.8, "strength": 0.9},
    {"source": "群", "target": "同调代数", "type": RelationType.PREREQUISITE, "weight": 0.7, "strength": 0.8},
    {"source": "范畴", "target": "同调代数", "type": RelationType.PREREQUISITE, "weight": 0.8, "strength": 0.9},
    {"source": "集合", "target": "度量空间", "type": RelationType.PREREQUISITE, "weight": 0.6, "strength": 0.7},
    {"source": "度量空间", "target": "极限", "type": RelationType.PREREQUISITE, "weight": 0.7, "strength": 0.8},
]
