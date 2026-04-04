"""
API路由聚合
"""
from fastapi import APIRouter
from . import knowledge_graph, learning_path, tasks, health, search, recommendation, learning_engine, feedback, notifications

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

api_router.include_router(
    learning_engine.router,
    prefix="/learning-engine",
    tags=["个性化学习引擎2.0"]
)

api_router.include_router(
    feedback.router,
    prefix="/feedback",
    tags=["用户反馈系统"]
)

api_router.include_router(
    notifications.router,
    prefix="/notifications",
    tags=["邮件通知系统"]
)
