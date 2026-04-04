"""
速率限制中间件

防止API滥用和DDoS攻击
"""
import time
import logging
from typing import Dict, List, Optional, Callable
from collections import defaultdict
from fastapi import Request, HTTPException
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

logger = logging.getLogger(__name__)


class RateLimitMiddleware(BaseHTTPMiddleware):
    """
    速率限制中间件
    
    基于IP地址和用户ID进行速率限制
    
    配置选项:
    - requests_per_minute: 每分钟最大请求数
    - burst_size: 突发请求容量
    - excluded_paths: 排除限制的路径
    """
    
    def __init__(
        self,
        app: ASGIApp,
        requests_per_minute: int = 60,
        burst_size: int = 10,
        excluded_paths: Optional[List[str]] = None,
        key_func: Optional[Callable[[Request], str]] = None
    ):
        super().__init__(app)
        self.requests_per_minute = requests_per_minute
        self.burst_size = burst_size
        self.excluded_paths = excluded_paths or ["/health", "/docs", "/openapi.json"]
        self.key_func = key_func or self._default_key_func
        
        # 存储请求历史: {key: [(timestamp, count), ...]}
        self._requests: Dict[str, List[float]] = defaultdict(list)
        
        # 清理计数器
        self._cleanup_counter = 0
    
    def _default_key_func(self, request: Request) -> str:
        """默认键生成函数 - 基于IP地址"""
        forwarded = request.headers.get("x-forwarded-for")
        if forwarded:
            return forwarded.split(",")[0].strip()
        return request.client.host if request.client else "unknown"
    
    def _should_skip(self, request: Request) -> bool:
        """检查是否应该跳过限制"""
        path = request.url.path
        return any(path.startswith(excluded) for excluded in self.excluded_paths)
    
    def _cleanup_old_requests(self, key: str, now: float):
        """清理旧的请求记录"""
        cutoff = now - 60  # 1分钟前
        self._requests[key] = [
            ts for ts in self._requests[key] if ts > cutoff
        ]
    
    def _is_rate_limited(self, key: str) -> bool:
        """检查是否超出速率限制"""
        now = time.time()
        
        # 定期清理（每100次请求）
        self._cleanup_counter += 1
        if self._cleanup_counter % 100 == 0:
            self._cleanup_old_requests(key, now)
        
        # 获取当前请求数
        self._cleanup_old_requests(key, now)
        request_count = len(self._requests[key])
        
        # 检查是否超过限制
        if request_count >= self.requests_per_minute:
            return True
        
        # 记录本次请求
        self._requests[key].append(now)
        return False
    
    async def dispatch(self, request: Request, call_next) -> None:
        """处理请求"""
        # 检查是否跳过
        if self._should_skip(request):
            return await call_next(request)
        
        # 获取限制键
        key = self.key_func(request)
        
        # 检查速率限制
        if self._is_rate_limited(key):
            logger.warning(f"速率限制触发: {key}")
            raise HTTPException(
                status_code=429,
                detail={
                    "error": "Rate limit exceeded",
                    "message": f"请求过于频繁，请稍后再试",
                    "limit": self.requests_per_minute,
                    "window": "1 minute"
                },
                headers={
                    "Retry-After": "60",
                    "X-RateLimit-Limit": str(self.requests_per_minute),
                    "X-RateLimit-Window": "60"
                }
            )
        
        # 继续处理请求
        response = await call_next(request)
        
        # 添加速率限制头
        remaining = max(0, self.requests_per_minute - len(self._requests[key]))
        response.headers["X-RateLimit-Limit"] = str(self.requests_per_minute)
        response.headers["X-RateLimit-Remaining"] = str(remaining)
        
        return response


class SlidingWindowRateLimitMiddleware(BaseHTTPMiddleware):
    """
    滑动窗口速率限制中间件
    
    相比固定窗口，滑动窗口能更平滑地处理突发流量
    """
    
    def __init__(
        self,
        app: ASGIApp,
        requests_per_minute: int = 60,
        window_size: int = 60,  # 窗口大小（秒）
        excluded_paths: Optional[List[str]] = None
    ):
        super().__init__(app)
        self.requests_per_minute = requests_per_minute
        self.window_size = window_size
        self.excluded_paths = excluded_paths or ["/health"]
        self._requests: Dict[str, List[float]] = defaultdict(list)
    
    def _should_skip(self, request: Request) -> bool:
        """检查是否应该跳过限制"""
        path = request.url.path
        return any(path.startswith(excluded) for excluded in self.excluded_paths)
    
    def _get_request_count(self, key: str, now: float) -> int:
        """获取窗口内的请求数"""
        cutoff = now - self.window_size
        self._requests[key] = [
            ts for ts in self._requests[key] if ts > cutoff
        ]
        return len(self._requests[key])
    
    async def dispatch(self, request: Request, call_next) -> None:
        """处理请求"""
        if self._should_skip(request):
            return await call_next(request)
        
        key = request.client.host if request.client else "unknown"
        now = time.time()
        
        # 检查是否超出限制
        current_count = self._get_request_count(key, now)
        if current_count >= self.requests_per_minute:
            # 计算重置时间
            if self._requests[key]:
                reset_time = int(self._requests[key][0] + self.window_size - now)
            else:
                reset_time = self.window_size
            
            raise HTTPException(
                status_code=429,
                detail={
                    "error": "Rate limit exceeded",
                    "message": "请求过于频繁，请稍后再试",
                    "retry_after": max(1, reset_time)
                },
                headers={"Retry-After": str(max(1, reset_time))}
            )
        
        # 记录请求
        self._requests[key].append(now)
        
        # 继续处理
        response = await call_next(request)
        
        # 添加限制头
        remaining = self.requests_per_minute - current_count - 1
        response.headers["X-RateLimit-Limit"] = str(self.requests_per_minute)
        response.headers["X-RateLimit-Remaining"] = str(max(0, remaining))
        
        return response


class UserBasedRateLimitMiddleware(BaseHTTPMiddleware):
    """
    基于用户的速率限制
    
    结合用户认证信息进行更精细的速率控制
    """
    
    def __init__(
        self,
        app: ASGIApp,
        anonymous_limit: int = 30,  # 匿名用户限制
        authenticated_limit: int = 120,  # 认证用户限制
        excluded_paths: Optional[List[str]] = None
    ):
        super().__init__(app)
        self.anonymous_limit = anonymous_limit
        self.authenticated_limit = authenticated_limit
        self.excluded_paths = excluded_paths or ["/health", "/api/v1/health"]
        self._requests: Dict[str, Dict[str, List[float]]] = defaultdict(
            lambda: defaultdict(list)
        )
    
    def _get_user_limit(self, request: Request) -> tuple:
        """获取用户的限制配置"""
        # 这里应该集成认证系统
        # 简化示例：通过header判断
        user_id = request.headers.get("x-user-id")
        if user_id:
            return user_id, self.authenticated_limit
        
        # 匿名用户使用IP
        ip = request.client.host if request.client else "unknown"
        return f"anon:{ip}", self.anonymous_limit
    
    def _should_skip(self, request: Request) -> bool:
        """检查是否应该跳过限制"""
        path = request.url.path
        return any(path.startswith(excluded) for excluded in self.excluded_paths)
    
    async def dispatch(self, request: Request, call_next) -> None:
        """处理请求"""
        if self._should_skip(request):
            return await call_next(request)
        
        key, limit = self._get_user_limit(request)
        now = time.time()
        
        # 清理旧记录
        cutoff = now - 60
        path = request.url.path
        self._requests[key][path] = [
            ts for ts in self._requests[key][path] if ts > cutoff
        ]
        
        # 检查限制
        current_count = len(self._requests[key][path])
        if current_count >= limit:
            raise HTTPException(
                status_code=429,
                detail={
                    "error": "Rate limit exceeded",
                    "message": f"用户 {key[:10]}... 请求过于频繁",
                    "limit": limit,
                    "path": path
                }
            )
        
        # 记录请求
        self._requests[key][path].append(now)
        
        response = await call_next(request)
        
        # 添加限制头
        remaining = limit - current_count - 1
        response.headers["X-RateLimit-Limit"] = str(limit)
        response.headers["X-RateLimit-Remaining"] = str(max(0, remaining))
        
        return response
