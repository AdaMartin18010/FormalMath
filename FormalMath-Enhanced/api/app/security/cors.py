"""
安全CORS配置中间件

提供严格的跨域资源共享控制
"""
import logging
from typing import List, Optional
from fastapi import Request
from fastapi.middleware.cors import CORSMiddleware
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class SecureCORSMiddleware:
    """
    安全CORS配置
    
    生产环境推荐配置：
    - 不允许通配符(*)
    - 明确指定允许的源
    - 限制允许的方法
    - 限制允许的头部
    - 禁止携带凭证时的通配符
    """
    
    # 生产环境允许的源
    PRODUCTION_ORIGINS = [
        "https://formalmath.example.com",
        "https://app.formalmath.example.com",
        "https://admin.formalmath.example.com",
    ]
    
    # 允许的HTTP方法
    ALLOWED_METHODS = ["GET", "POST", "PUT", "DELETE", "PATCH", "OPTIONS"]
    
    # 允许的请求头
    ALLOWED_HEADERS = [
        "Content-Type",
        "Authorization",
        "X-Request-ID",
        "X-API-Key",
        "Accept",
        "Accept-Language",
        "Accept-Encoding",
        "Origin",
        "Referer",
        "User-Agent",
    ]
    
    # 暴露的响应头
    EXPOSED_HEADERS = [
        "X-Request-ID",
        "X-RateLimit-Limit",
        "X-RateLimit-Remaining",
        "X-RateLimit-Reset",
        "X-Total-Count",
    ]
    
    @classmethod
    def get_middleware_config(cls, environment: str = "production") -> dict:
        """
        获取CORS中间件配置
        
        Args:
            environment: 环境类型 (production/staging/development)
        
        Returns:
            CORS配置字典
        """
        if environment == "production":
            return {
                "allow_origins": cls.PRODUCTION_ORIGINS,
                "allow_credentials": True,
                "allow_methods": cls.ALLOWED_METHODS,
                "allow_headers": cls.ALLOWED_HEADERS,
                "expose_headers": cls.EXPOSED_HEADERS,
                "max_age": 600,  # 预检请求缓存10分钟
            }
        elif environment == "staging":
            return {
                "allow_origins": [
                    *cls.PRODUCTION_ORIGINS,
                    "https://staging.formalmath.example.com",
                ],
                "allow_credentials": True,
                "allow_methods": cls.ALLOWED_METHODS,
                "allow_headers": cls.ALLOWED_HEADERS,
                "expose_headers": cls.EXPOSED_HEADERS,
                "max_age": 300,
            }
        else:  # development
            logger.warning("使用开发环境CORS配置（允许所有来源）")
            return {
                "allow_origins": ["*"],
                "allow_credentials": False,  # 通配符时不能为True
                "allow_methods": ["*"],
                "allow_headers": ["*"],
                "max_age": 600,
            }


class CORSValidatorMiddleware(BaseHTTPMiddleware):
    """
    CORS请求验证中间件
    
    额外验证：
    - Origin头的有效性
    - 防止null origin攻击
    - 日志记录跨域请求
    """
    
    def __init__(
        self,
        app: ASGIApp,
        allowed_origins: List[str],
        log_violations: bool = True
    ):
        super().__init__(app)
        self.allowed_origins = set(allowed_origins)
        self.log_violations = log_violations
    
    def _is_valid_origin(self, origin: str) -> bool:
        """验证Origin是否有效"""
        if not origin:
            return True  # 同源请求
        
        # 阻止null origin（用于绕过CORS限制的攻击）
        if origin.lower() == "null":
            return False
        
        # 检查是否在允许列表中
        return origin in self.allowed_origins
    
    async def dispatch(self, request: Request, call_next):
        origin = request.headers.get("origin")
        
        if origin and not self._is_valid_origin(origin):
            if self.log_violations:
                logger.warning(
                    f"阻止来自未授权源的CORS请求: {origin}, "
                    f"Path: {request.url.path}"
                )
            
            from fastapi import HTTPException
            raise HTTPException(
                status_code=403,
                detail={
                    "error": "CORS Error",
                    "message": "请求来源未被授权"
                }
            )
        
        # 记录跨域请求
        if origin and self.log_violations:
            logger.info(f"CORS请求: {request.method} {request.url.path} from {origin}")
        
        return await call_next(request)


def create_cors_middleware(app: ASGIApp, environment: str = "production"):
    """
    创建并应用安全CORS中间件
    
    Args:
        app: FastAPI应用
        environment: 环境类型
    """
    config = SecureCORSMiddleware.get_middleware_config(environment)
    
    app.add_middleware(
        CORSMiddleware,
        **config
    )
    
    # 添加额外的验证中间件（生产环境）
    if environment == "production":
        app.add_middleware(
            CORSValidatorMiddleware,
            allowed_origins=config["allow_origins"]
        )
    
    logger.info(f"CORS中间件已配置 - 环境: {environment}")
