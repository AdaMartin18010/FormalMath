"""
知识图谱API - 支持分页和缓存
"""
from fastapi import APIRouter, Depends, HTTPException, Query, Request
from sqlalchemy.orm import Session
from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
from enum import Enum

from ..core.database import get_db
from ..core.config import settings
from ..cache.redis_cache import cache, cached
from ..services.pagination import PaginatedResponse, paginate_query

router = APIRouter()


class ConceptDifficulty(str, Enum):
    """概念难度"""
    BASIC = "basic"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"
    RESEARCH = "research"


class ConceptResponse(BaseModel):
    """概念响应模型"""
    id: str
    name: str
    branch: str
    difficulty: ConceptDifficulty
    description: Optional[str] = None
    prerequisites: List[str] = []


class ConceptListResponse(PaginatedResponse):
    """概念列表响应"""
    items: List[ConceptResponse]


class GraphStats(BaseModel):
    """图谱统计"""
    total_nodes: int
    total_edges: int
    branches: Dict[str, int]
    difficulty_distribution: Dict[str, int]


# ============ API端点 ============

@router.get("", response_model=ConceptListResponse)
async def list_concepts(
    request: Request,
    branch: Optional[str] = Query(None, description="学科分支过滤"),
    difficulty: Optional[ConceptDifficulty] = Query(None, description="难度过滤"),
    search: Optional[str] = Query(None, description="搜索关键词"),
    page: int = Query(1, ge=1, description="页码"),
    page_size: int = Query(
        default=settings.DEFAULT_PAGE_SIZE,
        ge=1,
        le=settings.MAX_PAGE_SIZE,
        description="每页数量"
    ),
    db: Session = Depends(get_db)
):
    """
    获取概念列表（支持分页和过滤）
    
    - **branch**: 按学科分支过滤 (algebra, geometry, analysis, etc.)
    - **difficulty**: 按难度过滤
    - **search**: 搜索概念名称或描述
    - **page**: 页码，从1开始
    - **page_size**: 每页数量
    """
    # 构建缓存键
    cache_key = f"concepts:{branch}:{difficulty}:{search}:{page}:{page_size}"
    
    # 尝试从缓存获取
    cached_result = await cache.get(cache_key, prefix="kg")
    if cached_result:
        return ConceptListResponse(**cached_result)
    
    # 从数据库查询
    from ..models.models import KnowledgeGraphNode
    
    query = db.query(KnowledgeGraphNode)
    
    if branch:
        query = query.filter(KnowledgeGraphNode.branch == branch)
    
    if difficulty:
        query = query.filter(KnowledgeGraphNode.difficulty == difficulty)
    
    if search:
        query = query.filter(
            KnowledgeGraphNode.name.contains(search) |
            KnowledgeGraphNode.description.contains(search)
        )
    
    # 执行分页查询
    paginated = paginate_query(
        query=query,
        page=page,
        page_size=page_size,
        request=request
    )
    
    # 转换为响应模型
    items = [
        ConceptResponse(
            id=node.id,
            name=node.name,
            branch=node.branch,
            difficulty=node.difficulty.value if node.difficulty else None,
            description=node.description,
            prerequisites=node.prerequisites or []
        )
        for node in paginated.items
    ]
    
    result = ConceptListResponse(
        items=items,
        total=paginated.total,
        page=paginated.page,
        page_size=paginated.page_size,
        pages=paginated.pages,
        has_next=paginated.has_next,
        has_prev=paginated.has_prev
    )
    
    # 缓存结果
    await cache.set(cache_key, result.dict(), ttl=settings.CACHE_TTL_KNOWLEDGE_GRAPH, prefix="kg")
    
    return result


@router.get("/{concept_id}", response_model=ConceptResponse)
async def get_concept(
    concept_id: str,
    db: Session = Depends(get_db)
):
    """
    获取单个概念详情
    
    - **concept_id**: 概念唯一标识符
    """
    # 尝试从缓存获取
    cached_concept = await cache.get_concept_info(concept_id)
    if cached_concept:
        return ConceptResponse(**cached_concept)
    
    # 从数据库查询
    from ..models.models import KnowledgeGraphNode
    
    concept = db.query(KnowledgeGraphNode).filter(
        KnowledgeGraphNode.id == concept_id
    ).first()
    
    if not concept:
        raise HTTPException(status_code=404, detail="概念不存在")
    
    result = ConceptResponse(
        id=concept.id,
        name=concept.name,
        branch=concept.branch,
        difficulty=concept.difficulty.value if concept.difficulty else None,
        description=concept.description,
        prerequisites=concept.prerequisites or []
    )
    
    # 缓存结果
    await cache.set_concept_info(concept_id, result.dict())
    
    return result


@router.get("/{concept_id}/relations")
async def get_concept_relations(
    concept_id: str,
    relation_type: Optional[str] = Query(None, description="关系类型过滤"),
    direction: str = Query("both", description="方向: in, out, both"),
    db: Session = Depends(get_db)
):
    """
    获取概念的关系
    
    - **concept_id**: 概念ID
    - **relation_type**: 关系类型过滤
    - **direction**: 关系方向 (in=入边, out=出边, both=双向)
    """
    from ..models.models import KnowledgeGraphRelation
    
    query = db.query(KnowledgeGraphRelation)
    
    if direction == "in":
        query = query.filter(KnowledgeGraphRelation.target_id == concept_id)
    elif direction == "out":
        query = query.filter(KnowledgeGraphRelation.source_id == concept_id)
    else:
        query = query.filter(
            (KnowledgeGraphRelation.source_id == concept_id) |
            (KnowledgeGraphRelation.target_id == concept_id)
        )
    
    if relation_type:
        query = query.filter(KnowledgeGraphRelation.relation_type == relation_type)
    
    relations = query.all()
    
    return {
        "concept_id": concept_id,
        "relations": [
            {
                "id": r.id,
                "source": r.source_id,
                "target": r.target_id,
                "type": r.relation_type,
                "weight": r.weight
            }
            for r in relations
        ],
        "count": len(relations)
    }


@router.get("/{concept_id}/prerequisites")
async def get_concept_prerequisites(
    concept_id: str,
    depth: int = Query(1, ge=1, le=5, description="递归深度"),
    db: Session = Depends(get_db)
):
    """
    获取概念的前置依赖（支持多级递归）
    
    - **concept_id**: 概念ID
    - **depth**: 递归深度
    """
    from ..models.models import KnowledgeGraphNode, KnowledgeGraphRelation
    
    def get_prereqs_recursive(cid: str, current_depth: int, visited: set) -> List[Dict]:
        if current_depth > depth or cid in visited:
            return []
        
        visited.add(cid)
        
        # 查询直接前置概念
        relations = db.query(KnowledgeGraphRelation).filter(
            KnowledgeGraphRelation.target_id == cid,
            KnowledgeGraphRelation.relation_type == "prerequisite"
        ).all()
        
        prereqs = []
        for rel in relations:
            source = db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == rel.source_id
            ).first()
            
            if source:
                prereq = {
                    "id": source.id,
                    "name": source.name,
                    "difficulty": source.difficulty.value if source.difficulty else None,
                    "level": current_depth
                }
                
                # 递归获取更深层的前置
                if current_depth < depth:
                    prereq["prerequisites"] = get_prereqs_recursive(
                        source.id, current_depth + 1, visited
                    )
                
                prereqs.append(prereq)
        
        return prereqs
    
    # 检查概念是否存在
    concept = db.query(KnowledgeGraphNode).filter(
        KnowledgeGraphNode.id == concept_id
    ).first()
    
    if not concept:
        raise HTTPException(status_code=404, detail="概念不存在")
    
    prerequisites = get_prereqs_recursive(concept_id, 1, set())
    
    return {
        "concept_id": concept_id,
        "concept_name": concept.name,
        "prerequisites": prerequisites,
        "total_count": len(prerequisites)
    }


@router.get("/graph/stats", response_model=GraphStats)
async def get_graph_stats(
    branch: Optional[str] = Query(None, description="学科分支")
):
    """
    获取知识图谱统计信息
    
    - **branch**: 指定分支，不提供则返回全部统计
    """
    # 尝试从缓存获取
    cache_key = f"stats:{branch or 'all'}"
    cached_stats = await cache.get(cache_key, prefix="kg")
    if cached_stats:
        return GraphStats(**cached_stats)
    
    # 从数据库统计
    from ..models.models import KnowledgeGraphNode, KnowledgeGraphRelation
    from sqlalchemy import func
    
    # 基础查询
    node_query = db.query(KnowledgeGraphNode)
    edge_query = db.query(KnowledgeGraphRelation)
    
    if branch:
        node_query = node_query.filter(KnowledgeGraphNode.branch == branch)
    
    # 统计
    total_nodes = node_query.count()
    total_edges = edge_query.count()
    
    # 分支统计
    branch_stats = db.query(
        KnowledgeGraphNode.branch,
        func.count(KnowledgeGraphNode.id)
    ).group_by(KnowledgeGraphNode.branch).all()
    
    branches = {b: c for b, c in branch_stats}
    
    # 难度分布
    difficulty_stats = node_query.with_entities(
        KnowledgeGraphNode.difficulty,
        func.count(KnowledgeGraphNode.id)
    ).group_by(KnowledgeGraphNode.difficulty).all()
    
    difficulty_distribution = {
        d.value if d else "unknown": c
        for d, c in difficulty_stats
    }
    
    result = GraphStats(
        total_nodes=total_nodes,
        total_edges=total_edges,
        branches=branches,
        difficulty_distribution=difficulty_distribution
    )
    
    # 缓存结果
    await cache.set(cache_key, result.dict(), ttl=settings.CACHE_TTL_KNOWLEDGE_GRAPH, prefix="kg")
    
    return result


@router.post("/cache/clear")
async def clear_kg_cache(
    branch: Optional[str] = Query(None, description="清除特定分支缓存")
):
    """
    清除知识图谱缓存（管理员功能）
    
    - **branch**: 指定分支，不提供则清除全部
    """
    if branch:
        count = await cache.delete_pattern(f"kg:*{branch}*")
    else:
        count = await cache.delete_by_prefix("kg")
    
    return {
        "message": "缓存清除成功",
        "deleted_keys": count
    }
