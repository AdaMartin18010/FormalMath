"""
任务状态服务
"""
from dataclasses import dataclass
from typing import Optional, Dict, Any
from datetime import datetime
from celery.result import AsyncResult
from ..tasks.celery_app import celery_app


@dataclass
class TaskStatus:
    """任务状态数据类"""
    task_id: str
    state: str
    status: str
    result: Optional[Dict[str, Any]] = None
    error: Optional[str] = None
    progress: Optional[int] = None
    message: Optional[str] = None
    date_done: Optional[datetime] = None
    runtime: Optional[float] = None


def get_task_status(task_id: str) -> TaskStatus:
    """
    获取Celery任务状态
    
    Args:
        task_id: 任务ID
    
    Returns:
        任务状态对象
    """
    result = AsyncResult(task_id, app=celery_app)
    
    # 基础状态
    state = result.state
    
    # 处理结果
    task_result = None
    error = None
    progress = None
    message = None
    
    if state == "SUCCESS":
        task_result = result.result if isinstance(result.result, dict) else {"result": str(result.result)}
        status = "completed"
    elif state == "FAILURE":
        error = str(result.result) if result.result else "任务执行失败"
        status = "failed"
    elif state == "PENDING":
        status = "pending"
        message = "等待执行..."
    elif state == "STARTED":
        status = "running"
        message = "正在执行..."
    elif state == "PROGRESS":
        status = "running"
        # 从结果中提取进度信息
        if result.result and isinstance(result.result, dict):
            progress = result.result.get("progress")
            message = result.result.get("message", "处理中...")
    elif state == "RETRY":
        status = "retrying"
        message = "正在重试..."
    elif state == "REVOKED":
        status = "cancelled"
        message = "任务已取消"
    else:
        status = state.lower()
    
    # 获取完成时间
    date_done = result.date_done
    
    # 计算运行时间
    runtime = None
    if date_done and hasattr(result, 'date_started') and result.date_started:
        runtime = (date_done - result.date_started).total_seconds()
    
    return TaskStatus(
        task_id=task_id,
        state=state,
        status=status,
        result=task_result,
        error=error,
        progress=progress,
        message=message,
        date_done=date_done,
        runtime=runtime
    )


def wait_for_task(
    task_id: str,
    timeout: int = 30,
    interval: float = 0.5
) -> TaskStatus:
    """
    等待任务完成
    
    Args:
        task_id: 任务ID
        timeout: 超时时间（秒）
        interval: 检查间隔（秒）
    
    Returns:
        任务状态对象
    """
    import time
    
    start_time = time.time()
    
    while time.time() - start_time < timeout:
        status = get_task_status(task_id)
        
        if status.state in ["SUCCESS", "FAILURE", "REVOKED"]:
            return status
        
        time.sleep(interval)
    
    # 超时
    status = get_task_status(task_id)
    status.status = "timeout"
    status.message = f"等待超时（{timeout}秒）"
    
    return status
