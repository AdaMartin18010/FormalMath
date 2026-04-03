"""
应用配置
"""
from pydantic_settings import BaseSettings
from typing import List
import os


class Settings(BaseSettings):
    """应用配置类"""
    
    # 应用信息
    APP_NAME: str = "FormalMath认知诊断系统"
    APP_VERSION: str = "1.0.0"
    DEBUG: bool = False
    
    # API配置
    API_V1_PREFIX: str = "/api/v1"
    API_TITLE: str = "FormalMath CDS API"
    API_DESCRIPTION: str = "基于HCD框架的数学认知诊断系统API"
    
    # 数据库配置
    DATABASE_URL: str = "postgresql://postgres:postgres@localhost:5432/formalmath_cds"
    DATABASE_POOL_SIZE: int = 20
    DATABASE_MAX_OVERFLOW: int = 10
    
    # Redis配置
    REDIS_URL: str = "redis://localhost:6379/0"
    
    # JWT配置
    JWT_SECRET_KEY: str = "your-secret-key-change-in-production"
    JWT_ALGORITHM: str = "HS256"
    JWT_ACCESS_TOKEN_EXPIRE_MINUTES: int = 60 * 24  # 24小时
    
    # CORS配置
    CORS_ORIGINS: List[str] = ["http://localhost:3000", "http://localhost:5173"]
    
    # HCD算法配置
    HCD_MAX_ITER: int = 100
    HCD_TOLERANCE: float = 1e-6
    HCD_LEARNING_RATE: float = 0.1
    
    # 诊断配置
    DEFAULT_QUESTION_COUNT: int = 30
    MAX_QUESTION_COUNT: int = 50
    DIAGNOSIS_TIME_LIMIT: int = 90  # 分钟
    
    # 文件路径
    BASE_DIR: str = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    DATA_DIR: str = os.path.join(BASE_DIR, "data")
    QUESTION_BANK_PATH: str = os.path.join(DATA_DIR, "question_bank.yaml")
    
    class Config:
        env_file = ".env"
        case_sensitive = True


settings = Settings()
