"""
AI助手服务主入口
FastAPI应用
"""
import logging
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse

from app.core.config import get_settings
from app.api.routes import router as ai_assistant_router

# 获取配置
settings = get_settings()

# 配置日志
logging.basicConfig(
    level=getattr(logging, settings.LOG_LEVEL),
    format=settings.LOG_FORMAT
)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    应用生命周期管理
    """
    # ===== 启动 =====
    logger.info("=" * 50)
    logger.info(f"{settings.APP_NAME} 正在启动...")
    logger.info("=" * 50)
    
    logger.info(f"版本: {settings.APP_VERSION}")
    logger.info(f"调试模式: {settings.DEBUG}")
    logger.info(f"LLM提供商: {settings.LLM_PROVIDER}")
    logger.info(f"LLM模型: {settings.LLM_MODEL}")
    
    logger.info("=" * 50)
    logger.info("启动成功！")
    logger.info("=" * 50)
    
    yield
    
    # ===== 关闭 =====
    logger.info("正在关闭服务...")
    logger.info("服务已安全关闭")


# 创建FastAPI应用
app = FastAPI(
    title=settings.APP_NAME,
    version=settings.APP_VERSION,
    description="""
    FormalMath AI学习助手
    
    提供数学概念问答、证明辅助、学习建议等功能
    
    ## 主要功能
    
    - **概念解释**: 解释数学概念，支持不同难度级别
    - **证明提示**: 提供证明的启发式指导
    - **学习建议**: 个性化学习路径推荐
    - **问题解答**: 数学问题求解
    - **Lean 4支持**: 形式化数学帮助
    
    ## 技术栈
    
    - FastAPI
    - DeepSeek/OpenAI LLM
    - 语义搜索集成
    - 知识图谱
    """,
    lifespan=lifespan,
    docs_url="/docs",
    redoc_url="/redoc",
    openapi_url="/openapi.json"
)

# CORS中间件
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.CORS_ORIGINS,
    allow_credentials=settings.CORS_ALLOW_CREDENTIALS,
    allow_methods=settings.CORS_ALLOW_METHODS,
    allow_headers=settings.CORS_ALLOW_HEADERS,
)


# 健康检查端点
@app.get("/health", tags=["健康检查"])
async def health_check():
    """健康检查"""
    return {
        "status": "healthy",
        "service": settings.APP_NAME,
        "version": settings.APP_VERSION
    }


# 根端点
@app.get("/", tags=["根路径"])
async def root():
    """服务信息"""
    return {
        "name": settings.APP_NAME,
        "version": settings.APP_VERSION,
        "docs_url": "/docs",
        "api_prefix": settings.API_PREFIX + "/ai-assistant",
        "features": [
            "concept_explanation",
            "proof_hint",
            "learning_advice",
            "problem_solving",
            "lean_support",
            "multi_turn_conversation"
        ]
    }


# 注册AI助手路由
app.include_router(
    ai_assistant_router,
    prefix=settings.API_PREFIX
)


# 全局异常处理
@app.exception_handler(Exception)
async def global_exception_handler(request, exc):
    """全局异常处理"""
    logger.error(f"未处理的异常: {exc}", exc_info=True)
    return JSONResponse(
        status_code=500,
        content={
            "error": "服务器内部错误",
            "message": str(exc) if settings.DEBUG else "请稍后重试"
        }
    )


if __name__ == "__main__":
    import uvicorn
    
    uvicorn.run(
        "main:app",
        host=settings.HOST,
        port=settings.PORT,
        reload=settings.DEBUG,
        log_level=settings.LOG_LEVEL.lower()
    )
