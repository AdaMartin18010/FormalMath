"""
异步任务状态查询API
"""
from fastapi import APIRouter, HTTPException, Query
from pydantic import BaseModel, Field
from typing import Optional, Dict, Any, List
from enum import Enum

from ..tasks.celery_app import celery_app
from ..services.task_status import get_task_status, TaskStatus

router = APIRouter()


class TaskState(str, Enum):
    """任务状态"""
    PENDING = "PENDING"
    STARTED = "STARTED"
    PROGRESS = "PROGRESS"
    SUCCESS = "SUCCESS"
    FAILURE = "FAILURE"
    RETRY = "RETRY"
    REVOKED = "REVOKED"


class TaskInfo(BaseModel):
    """任务信息"""
    task_id: str
    state: str
    status: str
    result: Optional[Dict[str, Any]] = None
    error: Optional[str] = None
    progress: Optional[int] = Field(None, ge=0, le=100)
    message: Optional[str] = None
    date_done: Optional[str] = None
    runtime: Optional[float] = None


class TaskListResponse(BaseModel):
    """任务列表响应"""
    tasks: List[Dict[str, Any]]
    total: int


# ============ API端点 ============

@router.get("/{task_id}", response_model=TaskInfo)
async def get_task_info(task_id: str):
    """
    获取任务状态和结果
    
    - **task_id**: 任务ID（从异步API返回）
    """
    status = get_task_status(task_id)
    
    return TaskInfo(
        task_id=status.task_id,
        state=status.state,
        status=status.status,
        result=status.result,
        error=status.error,
        progress=status.progress,
        message=status.message,
        date_done=status.date_done.isoformat() if status.date_done else None,
        runtime=status.runtime
    )


@router.get("/{task_id}/result")
async def get_task_result(task_id: str):
    """
    获取任务结果（仅当任务完成时）
    
    - **task_id**: 任务ID
    """
    status = get_task_status(task_id)
    
    if status.state not in ["SUCCESS", "FAILURE"]:
        raise HTTPException(
            status_code=400,
            detail=f"任务尚未完成，当前状态: {status.state}"
        )
    
    if status.state == "FAILURE":
        raise HTTPException(
            status_code=500,
            detail={
                "error": status.error,
                "task_id": task_id
            }
        )
    
    return {
        "task_id": task_id,
        "state": status.state,
        "result": status.result
    }


@router.get("/{task_id}/progress")
async def get_task_progress(task_id: str):
    """
    获取任务进度（用于长时任务）
    
    - **task_id**: 任务ID
    """
    status = get_task_status(task_id)
    
    return {
        "task_id": task_id,
        "state": status.state,
        "progress": status.progress or 0,
        "message": status.message or "处理中..."
    }


@router.post("/{task_id}/revoke")
async def revoke_task(
    task_id: str,
    terminate: bool = Query(False, description="是否强制终止运行中的任务")
):
    """
    撤销/取消任务
    
    - **task_id**: 任务ID
    - **terminate**: 是否强制终止（可能导致任务状态不一致）
    """
    try:
        celery_app.control.revoke(task_id, terminate=terminate)
        
        return {
            "task_id": task_id,
            "action": "revoked",
            "terminated": terminate,
            "message": "任务已撤销"
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"撤销任务失败: {str(e)}")


@router.get("", response_model=TaskListResponse)
async def list_tasks(
    state: Optional[str] = Query(None, description="按状态过滤"),
    limit: int = Query(50, ge=1, le=100, description="返回数量限制")
):
    """
    列出活跃任务（检查Celery Worker状态）
    
    - **state**: 状态过滤
    - **limit**: 返回数量
    
    注意：此接口返回Worker当前正在处理的任务，不是历史任务
    """
    try:
        # 获取活跃任务
        inspect = celery_app.control.inspect()
        active_tasks = inspect.active() or {}
        scheduled_tasks = inspect.scheduled() or {}
        reserved_tasks = inspect.reserved() or {}
        
        all_tasks = []
        
        # 处理活跃任务
        for worker, tasks in active_tasks.items():
            for task in tasks:
                if not state or task.get("state") == state:
                    all_tasks.append({
                        "task_id": task.get("id"),
                        "name": task.get("name"),
                        "state": "ACTIVE",
                        "worker": worker,
                        "args": task.get("args"),
                        "kwargs": task.get("kwargs"),
                        "timestamp": task.get("time_start")
                    })
        
        # 处理计划任务
        for worker, tasks in scheduled_tasks.items():
            for task in tasks:
                request = task.get("request", {})
                if not state or state == "PENDING":
                    all_tasks.append({
                        "task_id": request.get("id"),
                        "name": request.get("name"),
                        "state": "SCHEDULED",
                        "worker": worker,
                        "eta": task.get("eta")
                    })
        
        # 处理预留任务
        for worker, tasks in reserved_tasks.items():
            for task in tasks:
                if not state or state == "PENDING":
                    all_tasks.append({
                        "task_id": task.get("id"),
                        "name": task.get("name"),
                        "state": "RESERVED",
                        "worker": worker
                    })
        
        return TaskListResponse(
            tasks=all_tasks[:limit],
            total=len(all_tasks)
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取任务列表失败: {str(e)}")


@router.get("/workers/status")
async def get_workers_status():
    """
    获取Celery Worker状态
    """
    try:
        inspect = celery_app.control.inspect()
        
        stats = inspect.stats() or {}
        active = inspect.active() or {}
        ping = inspect.ping() or {}
        
        workers = []
        for worker_name, worker_stats in stats.items():
            workers.append({
                "name": worker_name,
                "status": "online" if ping.get(worker_name) else "offline",
                "active_tasks": len(active.get(worker_name, [])),
                "processed": worker_stats.get("total", {}).get("tasks", 0),
                "prefetch_count": worker_stats.get("prefetch_count", 0),
                "concurrency": worker_stats.get("pool", {}).get("max-concurrency", 0)
            })
        
        return {
            "workers": workers,
            "total_workers": len(workers),
            "online_workers": len([w for w in workers if w["status"] == "online"])
        }
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"获取Worker状态失败: {str(e)}")


@router.post("/purge")
async def purge_tasks(
    queue: Optional[str] = Query(None, description="指定队列，不提供则清除所有")
):
    """
    清除队列中的等待任务（谨慎使用）
    
    - **queue**: 队列名称 (path_calculation, diagnosis, graph_analysis)
    """
    try:
        if queue:
            count = celery_app.control.purge(queue=queue)
        else:
            count = celery_app.control.purge()
        
        return {
            "purged_count": count,
            "queue": queue or "all",
            "message": f"已清除 {count} 个等待中的任务"
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"清除任务失败: {str(e)}")
