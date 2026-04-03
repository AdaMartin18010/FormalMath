"""
知识图谱模型
"""

from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Any
from pydantic import BaseModel, Field


class KnowledgeLevel(int, Enum):
    """知识层次 L0-L3"""
    L0 = 0  # 基础层：直观理解、基本定义
    L1 = 1  # 中级层：严格定义、基本定理
    L2 = 2  # 高级层：深入定理、应用
    L3 = 3  # 研究层：开放问题、研究方向


class ConstraintType(str, Enum):
    """约束类型"""
    PREREQUISITE = "prerequisite"  # 先修约束
    ABILITY = "ability"            # 能力约束
    LEARNING = "learning"          # 学习约束


class KnowledgeNode(BaseModel):
    """知识图谱节点"""
    id: str = Field(..., description="节点ID")
    name: str = Field(..., description="知识点名称")
    level: KnowledgeLevel = Field(..., description="知识层次 L0-L3")
    description: Optional[str] = None
    
    # 内容规模（与L0-L3层次对应）
    content_length: Optional[int] = Field(None, description="内容长度(字)")
    
    # CPFS结构分类
    cpfs_type: Optional[str] = Field(None, description="CPFS类型: CF/CS/PF/PS")
    
    # 元数据
    category: Optional[str] = None  # 所属类别
    tags: List[str] = Field(default_factory=list)
    importance: float = Field(1.0, ge=0.0, le=1.0, description="重要程度")
    
    created_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "set_theory_basic",
                "name": "集合的基本概念",
                "level": 0,
                "description": "集合的直观理解、基本例子",
                "content_length": 1500,
                "cpfs_type": "CF",
                "category": "集合论",
                "tags": ["基础", "直观"],
                "importance": 0.9
            }
        }


class KnowledgeEdge(BaseModel):
    """知识图谱边（关系）"""
    id: str = Field(..., description="边ID")
    source_id: str = Field(..., description="源节点ID")
    target_id: str = Field(..., description="目标节点ID")
    
    constraint_type: ConstraintType = Field(..., description="约束类型")
    strength: float = Field(1.0, ge=0.0, le=1.0, description="约束强度")
    
    description: Optional[str] = None
    created_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "edge_001",
                "source_id": "set_theory_basic",
                "target_id": "set_operations",
                "constraint_type": "prerequisite",
                "strength": 0.9,
                "description": "学习集合运算需要先掌握集合基本概念"
            }
        }


class KnowledgeGraph(BaseModel):
    """知识图谱"""
    id: str = Field(..., description="图谱ID")
    name: str = Field(..., description="图谱名称")
    description: Optional[str] = None
    
    # 节点和边
    nodes: Dict[str, KnowledgeNode] = Field(default_factory=dict)
    edges: Dict[str, KnowledgeEdge] = Field(default_factory=dict)
    
    # 层次结构
    level_structure: Dict[int, List[str]] = Field(
        default_factory=dict,
        description="各层次节点ID列表"
    )
    
    # 邻接表（方便遍历）
    adjacency_list: Dict[str, List[str]] = Field(
        default_factory=dict,
        description="节点邻接表"
    )
    
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)
    
    def get_nodes_by_level(self, level: int) -> List[KnowledgeNode]:
        """获取指定层次的所有节点"""
        node_ids = self.level_structure.get(level, [])
        return [self.nodes[nid] for nid in node_ids if nid in self.nodes]
    
    def get_prerequisites(self, node_id: str) -> List[KnowledgeNode]:
        """获取指定节点的所有先修节点"""
        prereq_ids = [
            edge.source_id 
            for edge in self.edges.values()
            if edge.target_id == node_id and edge.constraint_type == ConstraintType.PREREQUISITE
        ]
        return [self.nodes[nid] for nid in prereq_ids if nid in self.nodes]
    
    def get_successors(self, node_id: str) -> List[KnowledgeNode]:
        """获取指定节点的后继节点"""
        successor_ids = [
            edge.target_id
            for edge in self.edges.values()
            if edge.source_id == node_id
        ]
        return [self.nodes[nid] for nid in successor_ids if nid in self.nodes]
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "math_foundation",
                "name": "数学基础概念图谱",
                "description": "涵盖数学基础概念的层次结构",
                "nodes": {},
                "edges": {},
                "level_structure": {0: [], 1: [], 2: [], 3: []}
            }
        }
