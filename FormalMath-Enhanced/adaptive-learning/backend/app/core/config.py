"""
核心配置文件 - 自适应学习路径系统
"""
from pydantic_settings import BaseSettings
from typing import List, Optional
import os


class Settings(BaseSettings):
    """应用配置类"""
    
    # 应用基本信息
    APP_NAME: str = "FormalMath Adaptive Learning System"
    APP_VERSION: str = "1.0.0"
    DEBUG: bool = True
    
    # API配置
    API_PREFIX: str = "/api"
    API_V1_STR: str = "/api/v1"
    
    # CORS配置
    CORS_ORIGINS: List[str] = ["http://localhost:3000", "http://127.0.0.1:3000"]
    
    # 数据库配置
    DATABASE_URL: str = "sqlite:///./adaptive_learning.db"
    
    # 知识图谱配置
    KNOWLEDGE_GRAPH_PATH: str = "../../../project/links/cross-branch-links.yaml"
    CONCEPTS_DIR: str = "../../../concept/核心概念"
    
    # 学习路径算法配置
    DEFAULT_ALGORITHM: str = "astar"  # astar, dp, or rl
    MAX_PATH_LENGTH: int = 50
    DIFFICULTY_WEIGHT: float = 0.3
    PREREQUISITE_WEIGHT: float = 0.4
    INTEREST_WEIGHT: float = 0.3
    
    # 自适应调整参数
    MASTERY_THRESHOLD: float = 0.8
    STRUGGLE_THRESHOLD: float = 0.4
    ADJUSTMENT_SENSITIVITY: float = 0.2
    
    # 推荐系统配置
    MAX_RECOMMENDATIONS: int = 10
    MIN_CONFIDENCE: float = 0.6
    
    class Config:
        env_file = ".env"
        case_sensitive = True


settings = Settings()
