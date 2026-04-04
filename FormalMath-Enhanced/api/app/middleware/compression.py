"""
响应压缩中间件
支持gzip和brotli压缩
"""
import gzip
import brotli
import logging
from typing import Optional
from fastapi import Request, Response
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp
from ..core.config import settings

logger = logging.getLogger(__name__)


class CompressionMiddleware(BaseHTTPMiddleware):
    """响应压缩中间件"""
    
    def __init__(
        self,
        app: ASGIApp,
        minimum_size: int = None,
        compression_level: int = None
    ):
        super().__init__(app)
        self.minimum_size = minimum_size or settings.COMPRESSION_MINIMUM_SIZE
        self.compression_level = compression_level or settings.COMPRESSION_LEVEL
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求并压缩响应"""
        # 获取客户端支持的压缩方式
        accept_encoding = request.headers.get("accept-encoding", "").lower()
        
        # 继续处理请求
        response = await call_next(request)
        
        # 检查是否应该压缩
        if not self._should_compress(response, accept_encoding):
            return response
        
        # 选择压缩算法
        encoding = self._select_encoding(accept_encoding)
        if not encoding:
            return response
        
        # 执行压缩
        try:
            compressed_body = self._compress_response(response.body, encoding)
            
            # 更新响应
            response.body = compressed_body
            response.headers["content-encoding"] = encoding
            response.headers["content-length"] = str(len(compressed_body))
            response.headers["vary"] = "accept-encoding"
            
            logger.debug(f"响应已使用 {encoding} 压缩: {len(response.body)} -> {len(compressed_body)}")
            
        except Exception as e:
            logger.error(f"响应压缩失败: {e}")
        
        return response
    
    def _should_compress(self, response: Response, accept_encoding: str) -> bool:
        """检查是否应该压缩响应"""
        # 检查是否已编码
        if "content-encoding" in response.headers:
            return False
        
        # 检查内容类型
        content_type = response.headers.get("content-type", "")
        compressible_types = [
            "application/json",
            "application/javascript",
            "text/",
            "application/xml",
            "application/rss+xml",
        ]
        
        if not any(content_type.startswith(ct) for ct in compressible_types):
            return False
        
        # 检查内容长度
        content_length = response.headers.get("content-length")
        if content_length and int(content_length) < self.minimum_size:
            return False
        
        # 检查是否有可接受的编码
        if not accept_encoding:
            return False
        
        return True
    
    def _select_encoding(self, accept_encoding: str) -> Optional[str]:
        """选择压缩编码方式"""
        # 优先选择brotli
        if "br" in accept_encoding:
            return "br"
        # 其次选择gzip
        if "gzip" in accept_encoding:
            return "gzip"
        return None
    
    def _compress_response(self, body: bytes, encoding: str) -> bytes:
        """压缩响应体"""
        if encoding == "gzip":
            return gzip.compress(body, compresslevel=self.compression_level)
        elif encoding == "br":
            return brotli.compress(body, quality=self.compression_level)
        else:
            raise ValueError(f"不支持的编码方式: {encoding}")


class ConditionalCompressionMiddleware(BaseHTTPMiddleware):
    """条件压缩中间件 - 根据路径和条件选择是否压缩"""
    
    def __init__(
        self,
        app: ASGIApp,
        excluded_paths: list = None,
        minimum_size: int = None
    ):
        super().__init__(app)
        self.excluded_paths = excluded_paths or [
            "/health",
            "/api/docs",
            "/api/openapi.json",
        ]
        self.minimum_size = minimum_size or settings.COMPRESSION_MINIMUM_SIZE
        self.compression_middleware = CompressionMiddleware(app, minimum_size)
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求"""
        # 检查是否在排除路径中
        path = request.url.path
        if any(path.startswith(excluded) for excluded in self.excluded_paths):
            return await call_next(request)
        
        # 使用标准压缩中间件
        return await self.compression_middleware.dispatch(request, call_next)
