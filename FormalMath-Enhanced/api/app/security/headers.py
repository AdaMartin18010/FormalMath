"""
安全HTTP响应头中间件

添加各种安全相关的HTTP响应头
"""
import logging
from typing import Dict, Optional
from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class SecurityHeadersMiddleware(BaseHTTPMiddleware):
    """
    安全响应头中间件
    
    添加的安全头：
    - Strict-Transport-Security (HSTS)
    - X-Content-Type-Options
    - X-Frame-Options
    - X-XSS-Protection
    - Content-Security-Policy
    - Referrer-Policy
    - Permissions-Policy
    """
    
    def __init__(
        self,
        app: ASGIApp,
        hsts_max_age: int = 31536000,  # 1年
        hsts_include_subdomains: bool = True,
        hsts_preload: bool = True,
        csp_policy: Optional[str] = None,
        frame_options: str = "DENY",
        referrer_policy: str = "strict-origin-when-cross-origin"
    ):
        super().__init__(app)
        self.hsts_max_age = hsts_max_age
        self.hsts_include_subdomains = hsts_include_subdomains
        self.hsts_preload = hsts_preload
        self.frame_options = frame_options
        self.referrer_policy = referrer_policy
        
        # 默认CSP策略
        self.csp_policy = csp_policy or (
            "default-src 'self'; "
            "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net; "
            "style-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net; "
            "img-src 'self' data: https:; "
            "font-src 'self' https://cdn.jsdelivr.net; "
            "connect-src 'self' https://api.formalmath.example.com; "
            "frame-ancestors 'none'; "
            "base-uri 'self'; "
            "form-action 'self';"
        )
    
    async def dispatch(self, request: Request, call_next):
        """处理请求并添加安全头"""
        response = await call_next(request)
        
        # HSTS - 强制HTTPS
        if self.hsts_max_age > 0:
            hsts_value = f"max-age={self.hsts_max_age}"
            if self.hsts_include_subdomains:
                hsts_value += "; includeSubDomains"
            if self.hsts_preload:
                hsts_value += "; preload"
            response.headers["Strict-Transport-Security"] = hsts_value
        
        # 防止MIME类型嗅探
        response.headers["X-Content-Type-Options"] = "nosniff"
        
        # 防止点击劫持
        response.headers["X-Frame-Options"] = self.frame_options
        
        # XSS保护（现代浏览器主要依赖CSP，但此头仍有用）
        response.headers["X-XSS-Protection"] = "1; mode=block"
        
        # 内容安全策略
        response.headers["Content-Security-Policy"] = self.csp_policy
        
        # Referrer策略
        response.headers["Referrer-Policy"] = self.referrer_policy
        
        # 权限策略（限制浏览器功能）
        response.headers["Permissions-Policy"] = (
            "accelerometer=(), "
            "camera=(), "
            "geolocation=(), "
            "gyroscope=(), "
            "magnetometer=(), "
            "microphone=(), "
            "payment=(), "
            "usb=()"
        )
        
        # 移除可能泄露信息的头
        response.headers.pop("Server", None)
        response.headers.pop("X-Powered-By", None)
        
        return response


class SecurityHeaders:
    """
    安全响应头配置类
    
    提供不同环境下的推荐配置
    """
    
    @staticmethod
    def get_strict_csp() -> str:
        """获取严格的内容安全策略"""
        return (
            "default-src 'none'; "
            "script-src 'self'; "
            "style-src 'self'; "
            "img-src 'self' data:; "
            "font-src 'self'; "
            "connect-src 'self'; "
            "frame-ancestors 'none'; "
            "base-uri 'self'; "
            "form-action 'self';"
        )
    
    @staticmethod
    def get_api_csp() -> str:
        """获取API服务的CSP（更宽松，主要用于Swagger UI）"""
        return (
            "default-src 'self'; "
            "script-src 'self' 'unsafe-inline' 'unsafe-eval' https://cdn.jsdelivr.net https://unpkg.com; "
            "style-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net https://fonts.googleapis.com; "
            "img-src 'self' data: https:; "
            "font-src 'self' https://fonts.gstatic.com; "
            "connect-src 'self' http://localhost:* https:; "
            "frame-ancestors 'none';"
        )
    
    @staticmethod
    def get_development_csp() -> str:
        """获取开发环境的CSP（最宽松）"""
        return (
            "default-src * 'unsafe-inline' 'unsafe-eval'; "
            "script-src * 'unsafe-inline' 'unsafe-eval'; "
            "style-src * 'unsafe-inline'; "
            "img-src * data: blob:; "
            "connect-src *;"
        )
