"""
应用配置
"""

from typing import List
from pydantic_settings import BaseSettings


class Settings(BaseSettings):
    """应用配置类"""
    
    # 应用配置
    APP_NAME: str = "认知诊断系统"
    DEBUG: bool = True
    
    # 数据库配置
    DATABASE_URL: str = "postgresql://user:password@localhost/formalmath_cd"
    
    # CORS配置
    ALLOWED_HOSTS: List[str] = ["http://localhost:3000", "http://127.0.0.1:3000"]
    
    # 诊断配置
    MAX_DIAGNOSIS_QUESTIONS: int = 30
    DIAGNOSIS_TIME_LIMIT: int = 3600  # 秒
    
    # HCD算法配置
    HCD_MAX_ITERATIONS: int = 100
    HCD_CONVERGENCE_THRESHOLD: float = 0.001
    HCD_LEARNING_RATE: float = 0.1
    
    class Config:
        env_file = ".env"


settings = Settings()
