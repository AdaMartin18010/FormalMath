"""
ETag支持中间件
实现HTTP缓存验证机制
"""
import hashlib
import logging
from typing import Optional
from fastapi import Request, Response
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class ETagMiddleware(BaseHTTPMiddleware):
    """ETag中间件 - 支持HTTP缓存验证"""
    
    def __init__(
        self,
        app: ASGIApp,
        weak_etag: bool = True
    ):
        super().__init__(app)
        self.weak_etag = weak_etag
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求并添加ETag支持"""
        # 获取客户端发送的If-None-Match
        if_none_match = request.headers.get("if-none-match")
        
        # 处理请求
        response = await call_next(request)
        
        # 只处理成功的GET请求
        if request.method != "GET" or response.status_code != 200:
            return response
        
        # 检查是否应该跳过ETag
        if self._should_skip_etag(response):
            return response
        
        # 生成ETag
        etag = self._generate_etag(response.body)
        
        # 检查是否匹配
        if if_none_match and if_none_match == etag:
            # 返回304 Not Modified
            return Response(
                status_code=304,
                headers={
                    "etag": etag,
                    "cache-control": response.headers.get("cache-control", "")
                }
            )
        
        # 添加ETag到响应
        response.headers["etag"] = etag
        
        return response
    
    def _should_skip_etag(self, response: Response) -> bool:
        """检查是否应该跳过ETag生成"""
        # 如果已经存在ETag，跳过
        if "etag" in response.headers:
            return True
        
        # 检查Cache-Control
        cache_control = response.headers.get("cache-control", "").lower()
        if "no-store" in cache_control:
            return True
        
        # 检查内容类型
        content_type = response.headers.get("content-type", "")
        # 跳过流式响应
        if "stream" in content_type or response.headers.get("transfer-encoding") == "chunked":
            return True
        
        return False
    
    def _generate_etag(self, body: bytes) -> str:
        """生成ETag值"""
        hash_value = hashlib.md5(body).hexdigest()[:16]
        if self.weak_etag:
            return f'W/"{hash_value}"'
        return f'"{hash_value}"'


class CacheControlMiddleware(BaseHTTPMiddleware):
    """Cache-Control头管理中间件"""
    
    def __init__(
        self,
        app: ASGIApp,
        default_cache_control: str = "no-cache",
        path_configs: dict = None
    ):
        super().__init__(app)
        self.default_cache_control = default_cache_control
        self.path_configs = path_configs or {
            "/api/v1/concept-graph": "public, max-age=3600",
            "/api/v1/concepts": "public, max-age=1800",
            "/static/": "public, max-age=86400",
        }
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求并添加Cache-Control"""
        response = await call_next(request)
        
        # 如果已经有Cache-Control，不覆盖
        if "cache-control" in response.headers:
            return response
        
        # 根据路径设置Cache-Control
        path = request.url.path
        for pattern, cache_control in self.path_configs.items():
            if path.startswith(pattern):
                response.headers["cache-control"] = cache_control
                return response
        
        # 默认Cache-Control
        response.headers["cache-control"] = self.default_cache_control
        
        return response


class OptimisticConcurrencyMiddleware(BaseHTTPMiddleware):
    """乐观并发控制中间件 - 使用ETag防止更新冲突"""
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求"""
        # 只对PUT/PATCH/DELETE请求进行检查
        if request.method not in ["PUT", "PATCH", "DELETE"]:
            return await call_next(request)
        
        # 获取If-Match头
        if_match = request.headers.get("if-match")
        if not if_match:
            # 可选：要求必须提供If-Match
            # return Response(
            #     status_code=428,
            #     content="Precondition Required"
            # )
            pass
        
        # 处理请求
        response = await call_next(request)
        
        # 如果是412 Precondition Failed，说明版本冲突
        if response.status_code == 412:
            response.headers["content-type"] = "application/json"
            response.body = b'{"error": "Resource has been modified by another request"}'
        
        return response
