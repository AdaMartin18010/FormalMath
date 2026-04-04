"""
API缓存中间件更新
与CDN缓存策略保持一致的增强版缓存中间件
"""

from functools import wraps
import hashlib
import json
import logging
from typing import Optional, Callable, Any
from fastapi import Request, Response
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.types import ASGIApp

from api.app.cache.redis_cache import cache

logger = logging.getLogger(__name__)


class CDNCacheHeaderMiddleware(BaseHTTPMiddleware):
    """
    CDN友好的缓存头中间件
    根据API端点自动设置最优的Cache-Control头
    """
    
    def __init__(
        self,
        app: ASGIApp,
        default_cache_control: str = "no-cache",
        endpoint_configs: dict = None
    ):
        super().__init__(app)
        self.default_cache_control = default_cache_control
        # CDN优化的端点配置
        self.endpoint_configs = endpoint_configs or {
            # 知识图谱 - 可缓存1小时
            "/api/v1/concept-graph": {
                "cache_control": "public, max-age=3600, stale-while-revalidate=300",
                "cdn_ttl": 3600,
                "vary": "Accept-Encoding"
            },
            # 概念列表 - 30分钟
            "/api/v1/concepts": {
                "cache_control": "public, max-age=1800, stale-while-revalidate=300",
                "cdn_ttl": 1800,
                "vary": "Accept-Encoding"
            },
            # 概念详情 - 1小时
            "/api/v1/concepts/": {
                "cache_control": "public, max-age=3600",
                "cdn_ttl": 3600,
                "vary": "Accept-Encoding"
            },
            # 搜索API - 1分钟
            "/api/v1/search": {
                "cache_control": "public, max-age=60, stale-while-revalidate=10",
                "cdn_ttl": 60,
                "vary": "Accept-Encoding"
            },
            # 题目列表 - 1小时
            "/api/v1/problems": {
                "cache_control": "public, max-age=3600",
                "cdn_ttl": 3600,
                "vary": "Accept-Encoding"
            },
            # IMO题目 - 1天(题目不会变)
            "/api/v1/problems/imo/": {
                "cache_control": "public, max-age=86400, immutable",
                "cdn_ttl": 86400,
                "vary": "Accept-Encoding"
            },
            # 定理详情 - 1小时
            "/api/v1/theorems/": {
                "cache_control": "public, max-age=3600",
                "cdn_ttl": 3600,
                "vary": "Accept-Encoding"
            },
            # 统计信息 - 5分钟
            "/api/v1/stats": {
                "cache_control": "public, max-age=300",
                "cdn_ttl": 300,
                "vary": "Accept-Encoding"
            },
            # Mathlib4引用 - 2小时
            "/api/v1/references/mathlib4": {
                "cache_control": "public, max-age=7200",
                "cdn_ttl": 7200,
                "vary": "Accept-Encoding"
            },
            # 用户进度 - 私有，5分钟
            "/api/v1/progress": {
                "cache_control": "private, max-age=300",
                "cdn_ttl": 0,  # 不在CDN缓存
                "vary": "Accept-Encoding, Authorization"
            },
            # 学习路径 - 私有，5分钟
            "/api/v1/learning-paths": {
                "cache_control": "private, max-age=300",
                "cdn_ttl": 0,
                "vary": "Accept-Encoding, Authorization"
            },
            # 推荐 - 私有，5分钟
            "/api/v1/recommendations": {
                "cache_control": "private, max-age=300",
                "cdn_ttl": 0,
                "vary": "Accept-Encoding, Authorization"
            },
            # 健康检查 - 不缓存
            "/health": {
                "cache_control": "no-cache, no-store, must-revalidate",
                "cdn_ttl": 0,
                "pragma": "no-cache",
                "expires": "0"
            },
            # 认证端点 - 不缓存
            "/api/v1/auth": {
                "cache_control": "no-cache, no-store, must-revalidate, private",
                "cdn_ttl": 0,
                "pragma": "no-cache"
            }
        }
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求并添加CDN优化的缓存头"""
        response = await call_next(request)
        
        # 如果已经有Cache-Control，保留它
        if "cache-control" in response.headers:
            return response
        
        path = request.url.path
        method = request.method
        
        # 只缓存GET请求
        if method != "GET":
            response.headers["cache-control"] = "no-cache, no-store"
            return response
        
        # 查找匹配的配置
        config = None
        for pattern, cfg in self.endpoint_configs.items():
            if path.startswith(pattern):
                config = cfg
                break
        
        if config:
            # 应用缓存配置
            response.headers["cache-control"] = config["cache_control"]
            
            if "vary" in config:
                response.headers["vary"] = config["vary"]
            
            # 添加CDN特定的头
            if config.get("cdn_ttl", 0) > 0:
                response.headers["CDN-Cache-Control"] = f"max-age={config['cdn_ttl']}"
                response.headers["Cloudflare-CDN-Cache-Control"] = f"max-age={config['cdn_ttl']}"
            else:
                # 指示CDN不缓存
                response.headers["CDN-Cache-Control"] = "no-cache"
            
            # 添加调试头(开发环境)
            if request.headers.get("X-Debug-Cache"):
                response.headers["X-Cache-Config"] = json.dumps(config)
        else:
            # 默认不缓存
            response.headers["cache-control"] = self.default_cache_control
        
        return response


class SurrogateKeyMiddleware(BaseHTTPMiddleware):
    """
    Surrogate Key中间件
    用于细粒度的CDN缓存控制，支持通过标签批量清除缓存
    """
    
    def __init__(self, app: ASGIApp):
        super().__init__(app)
        # 端点到surrogate key的映射
        self.key_patterns = {
            "/api/v1/concept-graph": ["knowledge-graph", "concepts-all"],
            "/api/v1/concepts": ["concepts-list"],
            "/api/v1/concepts/": ["concept-{id}", "concepts-all"],
            "/api/v1/theorems/": ["theorem-{id}", "theorems-all"],
            "/api/v1/problems": ["problems-list"],
            "/api/v1/problems/imo/": ["imo-{year}-{number}", "problems-imo"],
            "/api/v1/references/mathlib4": ["mathlib-refs"],
            "/api/v1/stats": ["stats"]
        }
    
    def _generate_keys(self, path: str) -> list:
        """根据路径生成surrogate keys"""
        keys = []
        
        for pattern, key_templates in self.key_patterns.items():
            if path.startswith(pattern):
                # 提取路径参数
                parts = path[len(pattern):].strip("/").split("/")
                
                for template in key_templates:
                    key = template
                    # 替换占位符
                    for i, part in enumerate(parts):
                        key = key.replace(f"{{{i}}}", part)
                        # 替换命名参数
                        if i == 0:
                            key = key.replace("{id}", part)
                        elif i == 0 and "year" in template:
                            key = key.replace("{year}", part)
                        elif i == 1 and "number" in template:
                            key = key.replace("{number}", part)
                    
                    keys.append(key)
        
        return keys
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """添加Surrogate-Key头用于CDN缓存标签"""
        response = await call_next(request)
        
        # 只处理可缓存的GET请求
        if request.method != "GET":
            return response
        
        # 生成surrogate keys
        keys = self._generate_keys(request.url.path)
        
        if keys:
            # Fastly格式
            response.headers["Surrogate-Key"] = " ".join(keys)
            # CloudFlare格式(使用自定义头)
            response.headers["Cache-Tag"] = ",".join(keys)
        
        return response


class CacheKeyMiddleware(BaseHTTPMiddleware):
    """
    缓存键优化中间件
    控制哪些查询参数参与缓存键生成
    """
    
    def __init__(
        self,
        app: ASGIApp,
        param_configs: dict = None
    ):
        super().__init__(app)
        # 每个端点的缓存键配置
        self.param_configs = param_configs or {
            "/api/v1/concepts": {
                "include": ["page", "per_page", "category", "sort", "order"],
                "exclude": ["callback", "_", "timestamp", "utm_source", "utm_medium"]
            },
            "/api/v1/concept-graph": {
                "include": ["branch", "depth", "format", "include_deprecated"],
                "exclude": ["callback", "_"]
            },
            "/api/v1/search": {
                "include": ["q", "type", "category", "page", "per_page"],
                "exclude": ["callback", "_", "timestamp"],
                "normalize": True,  # 规范化查询词
                "max_length": 100
            },
            "/api/v1/problems": {
                "include": ["category", "difficulty", "page", "per_page", "sort"],
                "exclude": ["callback", "_"]
            }
        }
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """处理请求并添加缓存键相关信息"""
        response = await call_next(request)
        
        path = request.url.path
        
        # 检查是否有缓存键配置
        for pattern, config in self.param_configs.items():
            if path.startswith(pattern):
                # 生成规范化缓存键(用于调试)
                query_params = dict(request.query_params)
                
                # 过滤参数
                filtered_params = {}
                for key, value in query_params.items():
                    if key in config.get("exclude", []):
                        continue
                    if "include" in config and key not in config["include"]:
                        continue
                    
                    # 规范化
                    if config.get("normalize") and key == "q":
                        value = value.lower().strip()[:config.get("max_length", 100)]
                    
                    filtered_params[key] = value
                
                # 生成缓存键哈希(用于调试)
                cache_key = hashlib.md5(
                    json.dumps(filtered_params, sort_keys=True).encode()
                ).hexdigest()[:8]
                
                response.headers["X-Cache-Key"] = cache_key
                break
        
        return response


class StaleWhileRevalidateMiddleware(BaseHTTPMiddleware):
    """
    异步刷新中间件
    实现stale-while-revalidate模式，提高响应速度
    """
    
    def __init__(
        self,
        app: ASGIApp,
        grace_period: int = 300  # 5分钟宽限期
    ):
        super().__init__(app)
        self.grace_period = grace_period
    
    async def dispatch(self, request: Request, call_next) -> Response:
        """
        实现SWR模式的简化版本
        实际实现需要Redis记录缓存元数据
        """
        # 检查是否是后台刷新请求
        is_bg_refresh = request.headers.get("X-Background-Refresh") == "true"
        
        response = await call_next(request)
        
        # 添加SWR支持的头
        if "stale-while-revalidate" not in response.headers.get("cache-control", ""):
            current_cc = response.headers.get("cache-control", "")
            if "max-age=" in current_cc and "private" not in current_cc:
                # 如果还没有swr指令，添加一个默认的
                if "stale-while-revalidate" not in current_cc:
                    response.headers["cache-control"] = f"{current_cc}, stale-while-revalidate={self.grace_period}"
        
        # 标记后台刷新响应
        if is_bg_refresh:
            response.headers["X-Background-Refresh"] "completed"
        
        return response


# ============ 缓存装饰器增强 ============

def cached_with_tags(
    ttl: int = None,
    prefix: str = None,
    tags: list = None,
    key_func: Optional[Callable] = None
):
    """
    带标签的缓存装饰器
    支持通过标签批量失效缓存
    
    Args:
        ttl: 缓存过期时间
        prefix: 键前缀
        tags: 缓存标签列表，支持 {param} 格式的占位符
        key_func: 自定义缓存键生成函数
    """
    def decorator(func: Callable) -> Callable:
        @wraps(func)
        async def async_wrapper(*args, **kwargs):
            # 生成缓存键
            if key_func:
                cache_key = key_func(*args, **kwargs)
            else:
                cache_key = cache._hash_query(func.__name__, *args, **kwargs)
            
            # 尝试从缓存获取
            result = await cache.get(cache_key, prefix)
            
            if result is not None:
                # 添加标签元数据
                if tags and isinstance(result, dict):
                    result["_cache_metadata"] = {
                        "tags": tags,
                        "cached_at": "from_cache"
                    }
                return result
            
            # 执行函数
            result = await func(*args, **kwargs)
            
            # 写入缓存
            await cache.set(cache_key, result, ttl=ttl, prefix=prefix)
            
            # 存储标签映射(用于批量失效)
            if tags:
                for tag in tags:
                    tag_key = f"tag:{tag}:{prefix}:{cache_key}"
                    await cache.set(tag_key, "1", ttl=ttl)
            
            return result
        
        return async_wrapper
    return decorator


def invalidate_by_tag(tag: str):
    """
    通过标签使缓存失效
    
    Args:
        tag: 要失效的标签
    """
    async def invalidate():
        pattern = f"tag:{tag}:*"
        # 查找所有匹配的tag键
        keys = []
        async for key in cache.redis.scan_iter(match=pattern, count=1000):
            # 提取原始缓存键
            parts = key.decode().split(":")
            if len(parts) >= 3:
                original_key = ":".join(parts[2:])
                keys.append(original_key)
        
        # 删除原始缓存
        for key in keys:
            await cache.delete(key)
        
        logger.info(f"通过标签'{tag}'使{len(keys)}个缓存失效")
        return len(keys)
    
    return invalidate


# ============ 导出中间件列表 ============

cdn_middleware = [
    CDNCacheHeaderMiddleware,
    SurrogateKeyMiddleware,
    CacheKeyMiddleware,
    StaleWhileRevalidateMiddleware
]
