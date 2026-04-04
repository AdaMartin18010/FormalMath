"""
API路由聚合
"""
from fastapi import APIRouter
from . import knowledge_graph, learning_path, tasks, health, search, recommendation

api_router = APIRouter()

# 注册各模块路由
api_router.include_router(
    health.router,
    prefix="/health",
    tags=["健康检查"]
)

api_router.include_router(
    knowledge_graph.router,
    prefix="/concepts",
    tags=["知识图谱"]
)

api_router.include_router(
    learning_path.router,
    prefix="/learning-paths",
    tags=["学习路径"]
)

api_router.include_router(
    tasks.router,
    prefix="/tasks",
    tags=["异步任务"]
)

api_router.include_router(
    search.router,
    prefix="/search",
    tags=["语义搜索"]
)

api_router.include_router(
    recommendation.router,
    prefix="/recommendations",
    tags=["推荐系统"]
)
