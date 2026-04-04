"""
FormalMath API 核心配置
包含Redis、数据库、Celery等配置
"""
from typing import List, Optional
from functools import lru_cache
from pydantic_settings import BaseSettings


class Settings(BaseSettings):
    """应用配置类"""
    
    # 应用基本信息
    APP_NAME: str = "FormalMath API"
    APP_VERSION: str = "2.0.0"
    API_PREFIX: str = "/api/v1"
    DEBUG: bool = False
    
    # CORS配置
    CORS_ORIGINS: List[str] = ["*"]
    CORS_ALLOW_CREDENTIALS: bool = True
    CORS_ALLOW_METHODS: List[str] = ["*"]
    CORS_ALLOW_HEADERS: List[str] = ["*"]
    
    # Redis配置
    REDIS_HOST: str = "localhost"
    REDIS_PORT: int = 6379
    REDIS_DB: int = 0
    REDIS_PASSWORD: Optional[str] = None
    REDIS_URL: Optional[str] = None
    
    # Redis连接池配置
    REDIS_MAX_CONNECTIONS: int = 100
    REDIS_SOCKET_TIMEOUT: int = 5
    REDIS_SOCKET_CONNECT_TIMEOUT: int = 5
    
    # 缓存TTL配置（秒）
    CACHE_TTL_KNOWLEDGE_GRAPH: int = 3600  # 1小时
    CACHE_TTL_LEARNING_PATH: int = 1800    # 30分钟
    CACHE_TTL_USER_PROGRESS: int = 300     # 5分钟
    CACHE_TTL_CONCEPT_INFO: int = 7200     # 2小时
    CACHE_TTL_DIAGNOSIS: int = 600         # 10分钟
    CACHE_TTL_DEFAULT: int = 300           # 5分钟
    
    # 数据库配置
    DATABASE_URL: str = "sqlite:///./formalmath.db"
    DATABASE_POOL_SIZE: int = 20
    DATABASE_MAX_OVERFLOW: int = 30
    DATABASE_POOL_TIMEOUT: int = 30
    DATABASE_POOL_RECYCLE: int = 3600
    
    # Celery配置
    CELERY_BROKER_URL: str = "redis://localhost:6379/1"
    CELERY_RESULT_BACKEND: str = "redis://localhost:6379/2"
    CELERY_TASK_SERIALIZER: str = "json"
    CELERY_ACCEPT_CONTENT: List[str] = ["json"]
    CELERY_RESULT_SERIALIZER: str = "json"
    CELERY_TIMEZONE: str = "Asia/Shanghai"
    CELERY_ENABLE_UTC: bool = True
    CELERY_TASK_TRACK_STARTED: bool = True
    CELERY_TASK_TIME_LIMIT: int = 3600  # 1小时
    CELERY_WORKER_PREFETCH_MULTIPLIER: int = 4
    
    # 分页配置
    DEFAULT_PAGE_SIZE: int = 20
    MAX_PAGE_SIZE: int = 100
    
    # 压缩配置
    COMPRESSION_MINIMUM_SIZE: int = 1024  # 1KB
    COMPRESSION_LEVEL: int = 6
    
    # 性能配置
    WORKERS: int = 4
    REQUEST_TIMEOUT: int = 30
    
    class Config:
        env_file = ".env"
        case_sensitive = True


@lru_cache()
def get_settings() -> Settings:
    """获取缓存的配置实例"""
    return Settings()


settings = get_settings()
