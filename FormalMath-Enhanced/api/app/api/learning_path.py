"""
学习路径API - 支持异步计算和缓存
"""
from fastapi import APIRouter, Depends, HTTPException, Query, BackgroundTasks
from sqlalchemy.orm import Session
from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
from enum import Enum

from ..core.database import get_db
from ..core.config import settings
from ..cache.redis_cache import cache, cache_evict
from ..tasks.path_tasks import calculate_learning_path, optimize_learning_path
from ..services.task_status import get_task_status

router = APIRouter()


class PathAlgorithm(str, Enum):
    """路径算法"""
    ASTAR = "astar"
    DIJKSTRA = "dijkstra"
    DP = "dp"


class CreatePathRequest(BaseModel):
    """创建路径请求"""
    user_id: int = Field(..., description="用户ID")
    target_concepts: List[str] = Field(..., min_items=1, description="目标概念列表")
    algorithm: PathAlgorithm = Field(default=PathAlgorithm.ASTAR, description="路径算法")
    constraints: Optional[Dict[str, Any]] = Field(default=None, description="约束条件")
    async_mode: bool = Field(default=True, description="是否异步计算")


class PathResponse(BaseModel):
    """路径响应"""
    id: int
    user_id: int
    name: str
    status: str
    nodes_count: int
    estimated_duration: int
    created_at: str


class PathDetailResponse(PathResponse):
    """路径详情响应"""
    nodes: List[Dict[str, Any]]
    difficulty_distribution: Dict[str, int]


class TaskResponse(BaseModel):
    """任务响应"""
    task_id: str
    status: str
    message: str


# ============ API端点 ============

@router.post("", response_model=TaskResponse)
async def create_learning_path(
    request: CreatePathRequest,
    background_tasks: BackgroundTasks = None
):
    """
    创建学习路径
    
    支持同步和异步两种模式：
    - **async_mode=true** (默认): 返回任务ID，通过任务状态接口查询结果
    - **async_mode=false**: 同步返回计算结果（可能导致请求超时）
    """
    if request.async_mode:
        # 异步模式 - 提交Celery任务
        task = calculate_learning_path.delay(
            user_id=request.user_id,
            target_concepts=request.target_concepts,
            algorithm=request.algorithm.value,
            constraints=request.constraints
        )
        
        return TaskResponse(
            task_id=task.id,
            status="queued",
            message="学习路径计算任务已提交，请通过任务状态接口查询结果"
        )
    else:
        # 同步模式 - 直接计算（不推荐用于复杂路径）
        try:
            result = calculate_learning_path.run(
                user_id=request.user_id,
                target_concepts=request.target_concepts,
                algorithm=request.algorithm.value,
                constraints=request.constraints
            )
            
            return TaskResponse(
                task_id="sync",
                status="completed",
                message=f"路径计算完成，包含{result['nodes_count']}个节点"
            )
        except Exception as e:
            raise HTTPException(status_code=500, detail=f"路径计算失败: {str(e)}")


@router.get("/user/{user_id}", response_model=List[PathResponse])
async def get_user_learning_paths(
    user_id: int,
    status: Optional[str] = Query(None, description="状态过滤"),
    db: Session = Depends(get_db)
):
    """
    获取用户的学习路径列表
    
    - **user_id**: 用户ID
    - **status**: 按状态过滤 (active, completed, paused)
    """
    # 尝试从缓存获取
    cache_key = f"user:{user_id}:paths:{status or 'all'}"
    cached_paths = await cache.get_learning_path(user_id)
    
    if cached_paths and status is None:
        return [PathResponse(**p) for p in cached_paths.get("paths", [])]
    
    # 从数据库查询
    from ..models.models import LearningPath
    
    query = db.query(LearningPath).filter(LearningPath.user_id == user_id)
    
    if status:
        query = query.filter(LearningPath.status == status)
    
    paths = query.order_by(LearningPath.created_at.desc()).all()
    
    result = [
        PathResponse(
            id=path.id,
            user_id=path.user_id,
            name=path.name,
            status=path.status.value if path.status else None,
            nodes_count=path.total_nodes,
            estimated_duration=path.estimated_duration or 0,
            created_at=path.created_at.isoformat() if path.created_at else None
        )
        for path in paths
    ]
    
    # 缓存结果
    await cache.set_learning_path(user_id, {"paths": [r.dict() for r in result]})
    
    return result


@router.get("/{path_id}", response_model=PathDetailResponse)
async def get_learning_path_detail(
    path_id: int,
    db: Session = Depends(get_db)
):
    """
    获取学习路径详情
    
    - **path_id**: 路径ID
    """
    from ..models.models import LearningPath
    
    path = db.query(LearningPath).filter(LearningPath.id == path_id).first()
    
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    return PathDetailResponse(
        id=path.id,
        user_id=path.user_id,
        name=path.name,
        status=path.status.value if path.status else None,
        nodes_count=path.total_nodes,
        estimated_duration=path.estimated_duration or 0,
        created_at=path.created_at.isoformat() if path.created_at else None,
        nodes=path.path_data.get("nodes", []) if path.path_data else [],
        difficulty_distribution=path.path_data.get("difficulty_distribution", {}) if path.path_data else {}
    )


@router.post("/{path_id}/optimize")
async def optimize_path(
    path_id: int,
    optimization_type: str = Query("difficulty", description="优化类型"),
    background_tasks: BackgroundTasks = None,
    db: Session = Depends(get_db)
):
    """
    优化现有学习路径
    
    - **path_id**: 路径ID
    - **optimization_type**: 优化类型 (difficulty, time, balance)
    """
    # 检查路径是否存在
    from ..models.models import LearningPath
    
    path = db.query(LearningPath).filter(LearningPath.id == path_id).first()
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    # 提交优化任务
    task = optimize_learning_path.delay(
        path_id=path_id,
        optimization_type=optimization_type
    )
    
    return TaskResponse(
        task_id=task.id,
        status="queued",
        message="路径优化任务已提交"
    )


@router.put("/{path_id}/progress")
@cache_evict(prefix="learning", pattern="user:{user_id}:*")
async def update_path_progress(
    path_id: int,
    completed_nodes: int = Query(..., ge=0, description="已完成节点数"),
    db: Session = Depends(get_db)
):
    """
    更新学习路径进度
    
    更新进度会自动清除相关缓存
    
    - **path_id**: 路径ID
    - **completed_nodes**: 已完成的节点数量
    """
    from ..models.models import LearningPath
    from datetime import datetime
    
    path = db.query(LearningPath).filter(LearningPath.id == path_id).first()
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    path.completed_nodes = completed_nodes
    
    # 如果全部完成，更新状态
    if completed_nodes >= path.total_nodes:
        path.status = "completed"
        path.completed_at = datetime.utcnow()
    
    db.commit()
    
    # 清除用户进度缓存
    await cache.invalidate_learning_path(path.user_id)
    
    return {
        "path_id": path_id,
        "completed_nodes": completed_nodes,
        "total_nodes": path.total_nodes,
        "progress_percentage": round(completed_nodes / path.total_nodes * 100, 2) if path.total_nodes > 0 else 0,
        "status": path.status.value if path.status else None
    }


@router.get("/{path_id}/recommendations")
async def get_path_recommendations(
    path_id: int,
    db: Session = Depends(get_db)
):
    """
    获取学习路径的资源推荐
    
    - **path_id**: 路径ID
    """
    from ..models.models import LearningPath
    
    path = db.query(LearningPath).filter(LearningPath.id == path_id).first()
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    # 获取当前节点
    current_node_index = path.completed_nodes
    nodes = path.path_data.get("nodes", []) if path.path_data else []
    
    if current_node_index >= len(nodes):
        return {"message": "学习路径已完成", "recommendations": []}
    
    current_node = nodes[current_node_index]
    
    # 生成推荐（简化版本）
    recommendations = [
        {
            "type": "video",
            "title": f"{current_node.get('concept_id')} 讲解视频",
            "url": f"/resources/video/{current_node.get('concept_id')}"
        },
        {
            "type": "exercise",
            "title": f"{current_node.get('concept_id')} 练习题",
            "url": f"/resources/exercises/{current_node.get('concept_id')}"
        },
        {
            "type": "reading",
            "title": f"{current_node.get('concept_id')} 参考材料",
            "url": f"/resources/reading/{current_node.get('concept_id')}"
        }
    ]
    
    return {
        "current_node": current_node,
        "recommendations": recommendations
    }


@router.delete("/{path_id}")
async def delete_learning_path(
    path_id: int,
    db: Session = Depends(get_db)
):
    """
    删除学习路径
    
    - **path_id**: 路径ID
    """
    from ..models.models import LearningPath
    
    path = db.query(LearningPath).filter(LearningPath.id == path_id).first()
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    user_id = path.user_id
    
    db.delete(path)
    db.commit()
    
    # 清除缓存
    await cache.invalidate_learning_path(user_id)
    
    return {"message": "学习路径已删除", "path_id": path_id}
