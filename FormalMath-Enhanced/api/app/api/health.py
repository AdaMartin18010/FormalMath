"""
健康检查和系统状态API
"""
from fastapi import APIRouter, Depends, HTTPException
from sqlalchemy.orm import Session
from pydantic import BaseModel
from typing import Dict, Any, Optional
from datetime import datetime

from ..core.database import db_manager, get_db
from ..cache.redis_cache import cache
from ..tasks.celery_app import celery_app

router = APIRouter()


class HealthStatus(BaseModel):
    """健康状态模型"""
    status: str
    timestamp: datetime
    version: str


class SystemStatus(BaseModel):
    """系统状态模型"""
    api: Dict[str, Any]
    database: Dict[str, Any]
    redis: Dict[str, Any]
    celery: Dict[str, Any]


@router.get("", response_model=HealthStatus)
async def health_check():
    """基础健康检查"""
    return HealthStatus(
        status="healthy",
        timestamp=datetime.utcnow(),
        version="2.0.0"
    )


@router.get("/detailed", response_model=SystemStatus)
async def detailed_health_check():
    """详细系统状态检查"""
    status = {
        "api": {
            "status": "healthy",
            "timestamp": datetime.utcnow().isoformat()
        },
        "database": await _check_database(),
        "redis": await _check_redis(),
        "celery": await _check_celery()
    }
    
    return SystemStatus(**status)


@router.get("/database")
async def database_health():
    """数据库健康检查"""
    db_status = await _check_database()
    
    if db_status["status"] != "healthy":
        raise HTTPException(status_code=503, detail=db_status)
    
    return db_status


@router.get("/redis")
async def redis_health():
    """Redis健康检查"""
    redis_status = await _check_redis()
    
    if redis_status["status"] != "healthy":
        raise HTTPException(status_code=503, detail=redis_status)
    
    return redis_status


@router.get("/celery")
async def celery_health():
    """Celery健康检查"""
    celery_status = await _check_celery()
    
    if celery_status["status"] != "healthy":
        raise HTTPException(status_code=503, detail=celery_status)
    
    return celery_status


@router.get("/pool")
async def connection_pool_status():
    """获取数据库连接池状态"""
    pool_status = db_manager.get_pool_status()
    return {
        "pool": pool_status,
        "timestamp": datetime.utcnow().isoformat()
    }


# ============ 辅助函数 ============

async def _check_database() -> Dict[str, Any]:
    """检查数据库连接"""
    try:
        if not db_manager._initialized:
            return {"status": "unknown", "message": "数据库未初始化"}
        
        # 获取连接池状态
        pool_status = db_manager.get_pool_status()
        
        return {
            "status": "healthy",
            "pool": pool_status
        }
    except Exception as e:
        return {
            "status": "unhealthy",
            "error": str(e)
        }


async def _check_redis() -> Dict[str, Any]:
    """检查Redis连接"""
    try:
        # 尝试执行PING
        await cache.redis.ping()
        
        # 获取Redis信息
        info = await cache.redis.info()
        
        return {
            "status": "healthy",
            "version": info.get("redis_version"),
            "used_memory_human": info.get("used_memory_human"),
            "connected_clients": info.get("connected_clients"),
        }
    except Exception as e:
        return {
            "status": "unhealthy",
            "error": str(e)
        }


async def _check_celery() -> Dict[str, Any]:
    """检查Celery状态"""
    try:
        # 发送测试任务
        from ..tasks.celery_app import health_check_task
        result = health_check_task.delay()
        
        return {
            "status": "healthy",
            "task_id": result.id,
            "broker_url": celery_app.conf.broker_url.split("@")[-1] if "@" in celery_app.conf.broker_url else "configured"
        }
    except Exception as e:
        return {
            "status": "unhealthy",
            "error": str(e)
        }
