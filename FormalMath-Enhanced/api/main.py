"""
FormalMath API - 高性能FastAPI后端服务

特性：
- Redis缓存层
- 数据库连接池
- Celery异步任务
- 响应压缩和ETag
- 分页支持
- 语义搜索（文本嵌入、向量检索、公式搜索）
"""
import logging
import os
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware
from fastapi.responses import JSONResponse
from fastapi.staticfiles import StaticFiles

from app.core.config import settings
from app.core.database import db_manager, init_db
from app.cache.redis_cache import cache
from app.api.router import api_router
from app.middleware.compression import ConditionalCompressionMiddleware
from app.middleware.etag import ETagMiddleware, CacheControlMiddleware

# 语义搜索相关导入
try:
    from app.services.semantic_search_service import get_semantic_search_service
    SEMANTIC_SEARCH_AVAILABLE = True
except ImportError:
    SEMANTIC_SEARCH_AVAILABLE = False

# 配置日志
logging.basicConfig(
    level=logging.INFO if not settings.DEBUG else logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    应用生命周期管理
    
    启动时：
    - 初始化数据库连接池
    - 连接Redis缓存
    
    关闭时：
    - 关闭Redis连接
    """
    # ===== 启动 =====
    logger.info("=" * 50)
    logger.info("FormalMath API 正在启动...")
    logger.info("=" * 50)
    
    try:
        # 初始化数据库
        logger.info("正在初始化数据库...")
        init_db()
        logger.info("✓ 数据库初始化完成")
        
        # 初始化Redis缓存
        logger.info("正在连接Redis缓存...")
        await cache.initialize()
        logger.info("✓ Redis缓存连接成功")
        
        # 记录配置信息
        logger.info(f"API版本: {settings.APP_VERSION}")
        logger.info(f"API前缀: {settings.API_PREFIX}")
        logger.info(f"数据库池大小: {settings.DATABASE_POOL_SIZE}")
        logger.info(f"Redis主机: {settings.REDIS_HOST}:{settings.REDIS_PORT}")
        logger.info(f"Celery Broker: {settings.CELERY_BROKER_URL.split('@')[-1] if '@' in settings.CELERY_BROKER_URL else 'configured'}")
        
        # 初始化语义搜索服务
        if SEMANTIC_SEARCH_AVAILABLE:
            logger.info("正在初始化语义搜索服务...")
            search_service = get_semantic_search_service()
            logger.info("✓ 语义搜索服务初始化完成")
        
        logger.info("=" * 50)
        logger.info("FormalMath API 启动成功！")
        logger.info("=" * 50)
        
    except Exception as e:
        logger.error(f"启动失败: {e}")
        raise
    
    yield
    
    # ===== 关闭 =====
    logger.info("FormalMath API 正在关闭...")
    
    try:
        # 关闭Redis连接
        await cache.close()
        logger.info("✓ Redis连接已关闭")
        
    except Exception as e:
        logger.error(f"关闭时出错: {e}")
    
    logger.info("FormalMath API 已安全关闭")


# 创建FastAPI应用
app = FastAPI(
    title=settings.APP_NAME,
    version=settings.APP_VERSION,
    description="""
    FormalMath 高性能API服务
    
    ## 性能优化特性
    
    - **Redis缓存**: 自动缓存知识图谱查询、用户学习路径等
    - **数据库连接池**: 高效的数据库连接管理
    - **异步任务**: 使用Celery处理耗时操作
    - **响应压缩**: 支持gzip和brotli压缩
    - **HTTP缓存**: ETag和Cache-Control支持
    - **分页**: 大数据集的分页支持
    
    ## 技术栈
    
    - FastAPI + Uvicorn
    - SQLAlchemy + 连接池
    - Redis (缓存 + Celery Broker)
    - Celery (异步任务队列)
    """,
    lifespan=lifespan,
    docs_url="/docs",
    redoc_url="/redoc",
    openapi_url="/openapi.json"
)

# ============ 中间件配置 ============

# CORS中间件
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.CORS_ORIGINS,
    allow_credentials=settings.CORS_ALLOW_CREDENTIALS,
    allow_methods=settings.CORS_ALLOW_METHODS,
    allow_headers=settings.CORS_ALLOW_HEADERS,
)

# 内置GZip压缩（作为后备）
app.add_middleware(
    GZipMiddleware,
    minimum_size=settings.COMPRESSION_MINIMUM_SIZE,
    compresslevel=settings.COMPRESSION_LEVEL
)

# 条件压缩中间件（优先使用brotli）
app.add_middleware(
    ConditionalCompressionMiddleware,
    excluded_paths=["/health", "/docs", "/openapi.json"],
    minimum_size=settings.COMPRESSION_MINIMUM_SIZE
)

# ETag中间件
app.add_middleware(
    ETagMiddleware,
    weak_etag=True
)

# Cache-Control中间件
app.add_middleware(
    CacheControlMiddleware,
    default_cache_control="no-cache",
    path_configs={
        "/api/v1/concepts": "public, max-age=1800",
        "/api/v1/graph/stats": "public, max-age=3600",
    }
)

# ============ 静态文件服务 ============

# 挂载搜索前端页面
static_dir = os.path.join(os.path.dirname(__file__), "app", "static")
if os.path.exists(static_dir):
    app.mount("/static", StaticFiles(directory=static_dir), name="static")
    logger.info(f"✓ 静态文件服务已挂载: {static_dir}")

# ============ 路由注册 ============

# 注册API路由
app.include_router(
    api_router,
    prefix=settings.API_PREFIX
)


# ============ 根端点 ============

@app.get("/")
async def root():
    """根路径 - 服务信息"""
    features = [
        "redis_cache",
        "connection_pool",
        "celery_tasks",
        "response_compression",
        "etag_cache",
        "pagination"
    ]
    
    if SEMANTIC_SEARCH_AVAILABLE:
        features.extend([
            "semantic_search",
            "formula_search",
            "qa_system",
            "hybrid_search"
        ])
    
    return {
        "name": settings.APP_NAME,
        "version": settings.APP_VERSION,
        "status": "running",
        "docs_url": "/docs",
        "search_ui": "/static/search.html",
        "api_prefix": settings.API_PREFIX,
        "features": features
    }


@app.get("/health")
async def simple_health_check():
    """简单健康检查（用于负载均衡）"""
    return {"status": "healthy"}


# ============ 错误处理 ============

@app.exception_handler(Exception)
async def general_exception_handler(request, exc):
    """通用异常处理"""
    logger.error(f"未处理的异常: {exc}", exc_info=True)
    return JSONResponse(
        status_code=500,
        content={
            "error": "Internal Server Error",
            "message": str(exc) if settings.DEBUG else "服务器内部错误"
        }
    )


# ============ 主入口 ============

if __name__ == "__main__":
    import uvicorn
    
    uvicorn.run(
        "main:app",
        host="0.0.0.0",
        port=8000,
        workers=settings.WORKERS,
        reload=settings.DEBUG,
        log_level="info"
    )
