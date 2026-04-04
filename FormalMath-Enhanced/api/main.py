"""
FormalMath API - 高性能FastAPI后端服务

特性：
- Redis缓存层
- 数据库连接池
- Celery异步任务
- 响应压缩和ETag
- 分页支持
- 语义搜索（文本嵌入、向量检索、公式搜索）
- WAF防护
- 安全响应头
- 速率限制
- CORS控制
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

# ============ 错误处理器注册 ============

from app.core.error_handlers import register_error_handlers
register_error_handlers(app)

# ============ 安全中间件配置 ============

# 安全响应头中间件（最先添加，确保所有响应都包含安全头）
try:
    from app.security.headers import SecurityHeadersMiddleware
    from app.security.headers import SecurityHeaders
    
    app.add_middleware(
        SecurityHeadersMiddleware,
        hsts_max_age=31536000,  # 1年
        hsts_include_subdomains=True,
        hsts_preload=True,
        csp_policy=SecurityHeaders.get_api_csp(),
        frame_options="DENY",
        referrer_policy="strict-origin-when-cross-origin"
    )
    logger.info("✓ 安全响应头中间件已启用")
except Exception as e:
    logger.warning(f"安全响应头中间件加载失败: {e}")

# WAF中间件
try:
    from app.security.waf import WAFMiddleware
    
    app.add_middleware(
        WAFMiddleware,
        max_violations=5,
        ip_block_duration=3600,  # 1小时
        enable_logging=True
    )
    logger.info("✓ WAF中间件已启用")
except Exception as e:
    logger.warning(f"WAF中间件加载失败: {e}")

# 输入验证中间件
try:
    from app.security.validation import InputValidationMiddleware
    
    app.add_middleware(
        InputValidationMiddleware,
        max_body_size=10 * 1024 * 1024,  # 10MB
        max_json_depth=10,
        max_string_length=10000
    )
    logger.info("✓ 输入验证中间件已启用")
except Exception as e:
    logger.warning(f"输入验证中间件加载失败: {e}")

# CORS中间件 - 生产环境应限制来源
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.CORS_ORIGINS,
    allow_credentials=settings.CORS_ALLOW_CREDENTIALS,
    allow_methods=settings.CORS_ALLOW_METHODS,
    allow_headers=settings.CORS_ALLOW_HEADERS,
)

# CORS验证中间件（生产环境）
if not settings.DEBUG:
    try:
        from app.security.cors import CORSValidatorMiddleware
        
        app.add_middleware(
            CORSValidatorMiddleware,
            allowed_origins=settings.CORS_ORIGINS,
            log_violations=True
        )
        logger.info("✓ CORS验证中间件已启用")
    except Exception as e:
        logger.warning(f"CORS验证中间件加载失败: {e}")

# 速率限制中间件（可选，基于内存实现）
try:
    from app.middleware.rate_limit import RateLimitMiddleware
    app.add_middleware(
        RateLimitMiddleware,
        requests_per_minute=120,
        burst_size=20,
        excluded_paths=["/health", "/docs", "/openapi.json", "/static"]
    )
    logger.info("✓ 速率限制中间件已启用")
except Exception as e:
    logger.warning(f"速率限制中间件加载失败: {e}")

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
    
    # 安全功能
    features.extend([
        "waf_protection",
        "rate_limiting",
        "security_headers",
        "input_validation"
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
# 注意：错误处理器已在上方注册
# 这里保留用于兼容性

@app.exception_handler(Exception)
async def legacy_exception_handler(request, exc):
    """遗留异常处理（作为后备）"""
    logger.error(f"未处理的异常（遗留处理器）: {exc}", exc_info=True)
    return JSONResponse(
        status_code=500,
        content={
            "success": False,
            "error": {
                "code": "INTERNAL_ERROR",
                "message": "服务器内部错误，请稍后重试" if not settings.DEBUG else str(exc),
                "timestamp": datetime.utcnow().isoformat()
            }
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
