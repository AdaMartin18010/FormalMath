"""
FormalMath API - 生产环境核心配置
包含PostgreSQL、Redis集群、连接池优化等生产级配置
"""
import os
from typing import List, Optional
from functools import lru_cache
from pydantic_settings import BaseSettings
from pydantic import Field, validator


class ProductionSettings(BaseSettings):
    """生产环境应用配置类"""
    
    # ==================== 应用基本信息 ====================
    APP_NAME: str = "FormalMath API"
    APP_VERSION: str = "2.0.0"
    API_PREFIX: str = "/api/v1"
    DEBUG: bool = False
    ENVIRONMENT: str = "production"
    
    # ==================== CORS配置 ====================
    CORS_ORIGINS: List[str] = Field(default_factory=lambda: [
        "https://formalmath.org",
        "https://app.formalmath.org",
        "https://api.formalmath.org"
    ])
    CORS_ALLOW_CREDENTIALS: bool = True
    CORS_ALLOW_METHODS: List[str] = ["GET", "POST", "PUT", "DELETE", "PATCH", "OPTIONS"]
    CORS_ALLOW_HEADERS: List[str] = ["*"]
    CORS_MAX_AGE: int = 3600
    
    # ==================== PostgreSQL配置 ====================
    # 主数据库
    DATABASE_URL: str = Field(
        default="postgresql://formalmath:password@localhost:5432/formalmath",
        description="主数据库连接URL"
    )
    
    # 只读副本（用于读写分离）
    DATABASE_READ_REPLICA_URLS: List[str] = Field(
        default_factory=list,
        description="只读副本数据库URL列表"
    )
    
    # 连接池配置 - 生产优化
    DATABASE_POOL_SIZE: int = Field(
        default=20,
        description="连接池固定连接数"
    )
    DATABASE_MAX_OVERFLOW: int = Field(
        default=30,
        description="连接池溢出连接数"
    )
    DATABASE_POOL_TIMEOUT: int = Field(
        default=30,
        description="获取连接超时时间(秒)"
    )
    DATABASE_POOL_RECYCLE: int = Field(
        default=3600,
        description="连接回收时间(秒)"
    )
    DATABASE_POOL_PRE_PING: bool = Field(
        default=True,
        description="连接健康检查"
    )
    DATABASE_ECHO: bool = Field(
        default=False,
        description="SQL语句日志"
    )
    
    # 数据库性能优化
    DATABASE_STATEMENT_TIMEOUT: int = Field(
        default=60000,
        description="SQL语句执行超时(毫秒)"
    )
    DATABASE_IDLE_IN_TRANSACTION_TIMEOUT: int = Field(
        default=600000,
        description="空闲事务超时(毫秒)"
    )
    DATABASE_CONNECT_TIMEOUT: int = Field(
        default=10,
        description="连接超时(秒)"
    )
    
    # ==================== Redis集群配置 ====================
    # Redis模式: standalone, sentinel, cluster
    REDIS_MODE: str = Field(
        default="standalone",
        description="Redis运行模式"
    )
    
    # 单机模式配置
    REDIS_HOST: str = "localhost"
    REDIS_PORT: int = 6379
    REDIS_DB: int = 0
    REDIS_PASSWORD: Optional[str] = None
    
    # 集群模式配置
    REDIS_CLUSTER_NODES: List[str] = Field(
        default_factory=lambda: [
            "localhost:6379",
            "localhost:6380",
            "localhost:6381",
            "localhost:6382",
            "localhost:6383",
            "localhost:6384"
        ],
        description="Redis集群节点列表"
    )
    REDIS_CLUSTER_PASSWORD: Optional[str] = None
    REDIS_CLUSTER_SKIP_FULL_COVERAGE_CHECK: bool = True
    REDIS_CLUSTER_MAX_REDIRECTS: int = 5
    
    # Sentinel模式配置
    REDIS_SENTINEL_HOSTS: List[str] = Field(
        default_factory=lambda: [
            "localhost:26379",
            "localhost:26380",
            "localhost:26381"
        ],
        description="Sentinel节点列表"
    )
    REDIS_SENTINEL_MASTER_NAME: str = "formalmath-master"
    REDIS_SENTINEL_PASSWORD: Optional[str] = None
    
    # Redis连接池配置 - 生产优化
    REDIS_MAX_CONNECTIONS: int = Field(
        default=100,
        description="每个节点最大连接数"
    )
    REDIS_MIN_CONNECTIONS: int = Field(
        default=10,
        description="每个节点最小连接数"
    )
    REDIS_SOCKET_TIMEOUT: float = Field(
        default=5.0,
        description="Socket超时(秒)"
    )
    REDIS_SOCKET_CONNECT_TIMEOUT: float = Field(
        default=5.0,
        description="Socket连接超时(秒)"
    )
    REDIS_RETRY_ON_TIMEOUT: bool = True
    REDIS_HEALTH_CHECK_INTERVAL: int = Field(
        default=30,
        description="健康检查间隔(秒)"
    )
    
    # Redis SSL/TLS配置
    REDIS_SSL: bool = Field(default=False)
    REDIS_SSL_CERTFILE: Optional[str] = None
    REDIS_SSL_KEYFILE: Optional[str] = None
    REDIS_SSL_CA_CERTS: Optional[str] = None
    REDIS_SSL_CERT_REQS: str = "required"
    
    # ==================== 缓存TTL配置（秒）====================
    CACHE_TTL_KNOWLEDGE_GRAPH: int = 3600      # 1小时
    CACHE_TTL_LEARNING_PATH: int = 1800        # 30分钟
    CACHE_TTL_USER_PROGRESS: int = 300         # 5分钟
    CACHE_TTL_CONCEPT_INFO: int = 7200         # 2小时
    CACHE_TTL_DIAGNOSIS: int = 600             # 10分钟
    CACHE_TTL_SEARCH_RESULTS: int = 300        # 5分钟
    CACHE_TTL_DEFAULT: int = 300               # 5分钟
    
    # 缓存压缩设置
    CACHE_COMPRESSION_ENABLED: bool = True
    CACHE_COMPRESSION_THRESHOLD: int = 1024    # 1KB以上压缩
    
    # ==================== Celery配置 ====================
    CELERY_BROKER_URL: str = "redis://localhost:6379/1"
    CELERY_RESULT_BACKEND: str = "redis://localhost:6379/2"
    CELERY_TASK_SERIALIZER: str = "json"
    CELERY_ACCEPT_CONTENT: List[str] = ["json"]
    CELERY_RESULT_SERIALIZER: str = "json"
    CELERY_TIMEZONE: str = "Asia/Shanghai"
    CELERY_ENABLE_UTC: bool = True
    CELERY_TASK_TRACK_STARTED: bool = True
    CELERY_TASK_TIME_LIMIT: int = 3600         # 1小时
    CELERY_TASK_SOFT_TIME_LIMIT: int = 3300    # 55分钟
    CELERY_WORKER_PREFETCH_MULTIPLIER: int = 4
    CELERY_WORKER_MAX_TASKS_PER_CHILD: int = 1000
    CELERY_BROKER_CONNECTION_RETRY_ON_STARTUP: bool = True
    
    # Celery结果过期时间
    CELERY_RESULT_EXPIRES: int = 86400         # 1天
    CELERY_TASK_RESULT_EXPIRES: int = 86400
    
    # ==================== 分页配置 ====================
    DEFAULT_PAGE_SIZE: int = 20
    MAX_PAGE_SIZE: int = 100
    
    # ==================== 压缩配置 ====================
    COMPRESSION_ENABLED: bool = True
    COMPRESSION_MINIMUM_SIZE: int = 1024       # 1KB
    COMPRESSION_LEVEL: int = 6                 # 1-9
    
    # ==================== 限流配置 ====================
    RATE_LIMIT_ENABLED: bool = True
    RATE_LIMIT_DEFAULT: str = "100/minute"
    RATE_LIMIT_LOGIN: str = "5/minute"
    RATE_LIMIT_API: str = "1000/minute"
    
    # ==================== 安全配置 ====================
    SECRET_KEY: str = Field(
        default="your-secret-key-change-in-production",
        description="应用密钥"
    )
    JWT_ALGORITHM: str = "HS256"
    JWT_ACCESS_TOKEN_EXPIRE_MINUTES: int = 30
    JWT_REFRESH_TOKEN_EXPIRE_DAYS: int = 7
    
    # 密码强度
    PASSWORD_MIN_LENGTH: int = 8
    PASSWORD_REQUIRE_UPPERCASE: bool = True
    PASSWORD_REQUIRE_LOWERCASE: bool = True
    PASSWORD_REQUIRE_DIGITS: bool = True
    PASSWORD_REQUIRE_SPECIAL: bool = True
    
    # ==================== 监控配置 ====================
    SENTRY_DSN: Optional[str] = None
    SENTRY_ENVIRONMENT: str = "production"
    SENTRY_TRACES_SAMPLE_RATE: float = 0.1
    
    # Prometheus指标
    METRICS_ENABLED: bool = True
    METRICS_PORT: int = 9090
    
    # ==================== 性能配置 ====================
    WORKERS: int = Field(
        default=4,
        description="Uvicorn工作进程数"
    )
    REQUEST_TIMEOUT: int = 30
    KEEPALIVE_TIMEOUT: int = 5
    
    # Gunicorn配置
    GUNICORN_BIND: str = "0.0.0.0:8000"
    GUNICORN_WORKERS: int = 4
    GUNICORN_WORKER_CONNECTIONS: int = 1000
    GUNICORN_MAX_REQUESTS: int = 10000
    GUNICORN_MAX_REQUESTS_JITTER: int = 1000
    GUNICORN_TIMEOUT: int = 120
    GUNICORN_GRACEFUL_TIMEOUT: int = 30
    
    # ==================== 文件上传配置 ====================
    UPLOAD_MAX_SIZE: int = 10 * 1024 * 1024    # 10MB
    UPLOAD_ALLOWED_EXTENSIONS: List[str] = Field(
        default_factory=lambda: [".jpg", ".jpeg", ".png", ".gif", ".pdf"]
    )
    
    # ==================== 外部服务配置 ====================
    # OpenAI API
    OPENAI_API_KEY: Optional[str] = None
    OPENAI_API_BASE: Optional[str] = None
    OPENAI_MODEL: str = "gpt-4"
    
    # 邮件服务
    SMTP_HOST: Optional[str] = None
    SMTP_PORT: int = 587
    SMTP_USER: Optional[str] = None
    SMTP_PASSWORD: Optional[str] = None
    SMTP_TLS: bool = True
    EMAIL_FROM: Optional[str] = None
    
    # ==================== 备份配置 ====================
    BACKUP_ENABLED: bool = True
    BACKUP_SCHEDULE: str = "0 2 * * *"         # 每天凌晨2点
    BACKUP_RETENTION_DAYS: int = 30
    BACKUP_S3_BUCKET: Optional[str] = None
    BACKUP_S3_PREFIX: str = "backups/formalmath"
    
    class Config:
        env_file = ".env.production"
        env_file_encoding = "utf-8"
        case_sensitive = True
        extra = "allow"
    
    # ==================== 验证器 ====================
    @validator("DATABASE_URL")
    def validate_database_url(cls, v):
        """验证数据库URL"""
        if not v.startswith(("postgresql://", "postgresql+asyncpg://")):
            raise ValueError("生产环境必须使用PostgreSQL数据库")
        return v
    
    @validator("SECRET_KEY")
    def validate_secret_key(cls, v):
        """验证密钥强度"""
        if v == "your-secret-key-change-in-production" or len(v) < 32:
            raise ValueError("生产环境必须设置强密钥(至少32字符)")
        return v


@lru_cache()
def get_production_settings() -> ProductionSettings:
    """获取缓存的生产环境配置实例"""
    return ProductionSettings()


# 全局配置实例
settings_production = get_production_settings()
