"""
AI助手核心配置
"""
import os
from typing import List, Optional
from functools import lru_cache
from pydantic_settings import BaseSettings


class Settings(BaseSettings):
    """AI助手配置类"""
    
    # 应用信息
    APP_NAME: str = "FormalMath AI Assistant"
    APP_VERSION: str = "1.0.0"
    DEBUG: bool = False
    
    # API配置
    API_PREFIX: str = "/api/v1"
    HOST: str = "0.0.0.0"
    PORT: int = 8001
    
    # CORS配置
    CORS_ORIGINS: List[str] = ["*"]
    CORS_ALLOW_CREDENTIALS: bool = True
    CORS_ALLOW_METHODS: List[str] = ["*"]
    CORS_ALLOW_HEADERS: List[str] = ["*"]
    
    # LLM配置
    LLM_PROVIDER: str = "deepseek"  # deepseek, openai
    LLM_MODEL: str = "deepseek-chat"
    LLM_API_KEY: Optional[str] = None
    LLM_BASE_URL: Optional[str] = None
    LLM_TEMPERATURE: float = 0.7
    LLM_MAX_TOKENS: int = 4096
    LLM_TIMEOUT: int = 60
    
    # 对话管理配置
    MAX_SESSIONS_PER_USER: int = 10
    SESSION_TIMEOUT_MINUTES: int = 60
    MAX_MESSAGES_PER_SESSION: int = 100
    
    # 知识库配置
    KNOWLEDGE_GRAPH_PATH: Optional[str] = None
    SEMANTIC_SEARCH_ENABLED: bool = True
    
    # 缓存配置
    CACHE_ENABLED: bool = True
    CACHE_TTL: int = 3600  # 1小时
    
    # 日志配置
    LOG_LEVEL: str = "INFO"
    LOG_FORMAT: str = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    
    class Config:
        env_file = ".env"
        case_sensitive = True


@lru_cache()
def get_settings() -> Settings:
    """获取缓存的配置实例"""
    return Settings()
