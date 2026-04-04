"""
Redis缓存层实现
提供高性能的缓存服务，用于知识图谱查询、用户学习路径等
"""
import json
import pickle
import hashlib
import logging
from typing import Optional, Any, Union, Callable
from functools import wraps
import asyncio
from redis.asyncio import Redis
from redis.asyncio.connection import ConnectionPool
from ..core.config import settings

logger = logging.getLogger(__name__)


class RedisCache:
    """Redis缓存管理器"""
    
    _instance: Optional['RedisCache'] = None
    _lock = asyncio.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._initialized = False
        return cls._instance
    
    def __init__(self):
        if self._initialized:
            return
        
        self._redis: Optional[Redis] = None
        self._pool: Optional[ConnectionPool] = None
        self._initialized = True
    
    async def initialize(self):
        """初始化Redis连接池"""
        if self._redis is not None:
            return
        
        try:
            # 构建Redis URL
            if settings.REDIS_URL:
                url = settings.REDIS_URL
            else:
                auth = f":{settings.REDIS_PASSWORD}@" if settings.REDIS_PASSWORD else ""
                url = f"redis://{auth}{settings.REDIS_HOST}:{settings.REDIS_PORT}/{settings.REDIS_DB}"
            
            # 创建连接池
            self._pool = ConnectionPool.from_url(
                url,
                max_connections=settings.REDIS_MAX_CONNECTIONS,
                socket_timeout=settings.REDIS_SOCKET_TIMEOUT,
                socket_connect_timeout=settings.REDIS_SOCKET_CONNECT_TIMEOUT,
                decode_responses=False  # 保持二进制以支持pickle
            )
            
            self._redis = Redis(connection_pool=self._pool)
            
            # 测试连接
            await self._redis.ping()
            logger.info(f"Redis缓存初始化成功: {settings.REDIS_HOST}:{settings.REDIS_PORT}")
            
        except Exception as e:
            logger.error(f"Redis缓存初始化失败: {e}")
            self._redis = None
            raise
    
    async def close(self):
        """关闭Redis连接"""
        if self._pool:
            await self._pool.disconnect()
            self._pool = None
            self._redis = None
            logger.info("Redis连接已关闭")
    
    @property
    def redis(self) -> Redis:
        """获取Redis客户端"""
        if self._redis is None:
            raise RuntimeError("Redis缓存未初始化，请先调用initialize()")
        return self._redis
    
    def _serialize(self, value: Any) -> bytes:
        """序列化值"""
        return pickle.dumps(value)
    
    def _deserialize(self, value: bytes) -> Any:
        """反序列化值"""
        return pickle.loads(value)
    
    def _make_key(self, key: str, prefix: Optional[str] = None) -> str:
        """构建缓存键"""
        if prefix:
            return f"{prefix}:{key}"
        return key
    
    def _hash_query(self, *args, **kwargs) -> str:
        """为查询参数生成哈希键"""
        key_data = json.dumps({"args": args, "kwargs": kwargs}, sort_keys=True, default=str)
        return hashlib.md5(key_data.encode()).hexdigest()
    
    # ============ 基本缓存操作 ============
    
    async def get(self, key: str, prefix: Optional[str] = None) -> Optional[Any]:
        """获取缓存值"""
        try:
            full_key = self._make_key(key, prefix)
            value = await self.redis.get(full_key)
            if value is None:
                return None
            return self._deserialize(value)
        except Exception as e:
            logger.error(f"缓存获取失败 [{key}]: {e}")
            return None
    
    async def set(
        self,
        key: str,
        value: Any,
        ttl: int = None,
        prefix: Optional[str] = None
    ) -> bool:
        """设置缓存值"""
        try:
            full_key = self._make_key(key, prefix)
            serialized = self._serialize(value)
            
            if ttl:
                await self.redis.setex(full_key, ttl, serialized)
            else:
                await self.redis.set(full_key, serialized)
            
            return True
        except Exception as e:
            logger.error(f"缓存设置失败 [{key}]: {e}")
            return False
    
    async def delete(self, key: str, prefix: Optional[str] = None) -> bool:
        """删除缓存"""
        try:
            full_key = self._make_key(key, prefix)
            await self.redis.delete(full_key)
            return True
        except Exception as e:
            logger.error(f"缓存删除失败 [{key}]: {e}")
            return False
    
    async def exists(self, key: str, prefix: Optional[str] = None) -> bool:
        """检查缓存是否存在"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.exists(full_key) > 0
        except Exception as e:
            logger.error(f"缓存检查失败 [{key}]: {e}")
            return False
    
    async def ttl(self, key: str, prefix: Optional[str] = None) -> int:
        """获取缓存剩余TTL"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.ttl(full_key)
        except Exception as e:
            logger.error(f"获取TTL失败 [{key}]: {e}")
            return -2
    
    # ============ 批量操作 ============
    
    async def mget(self, keys: list, prefix: Optional[str] = None) -> list:
        """批量获取"""
        try:
            full_keys = [self._make_key(k, prefix) for k in keys]
            values = await self.redis.mget(full_keys)
            return [self._deserialize(v) if v else None for v in values]
        except Exception as e:
            logger.error(f"批量获取失败: {e}")
            return [None] * len(keys)
    
    async def mset(self, mapping: dict, ttl: int = None, prefix: Optional[str] = None) -> bool:
        """批量设置"""
        try:
            full_mapping = {
                self._make_key(k, prefix): self._serialize(v)
                for k, v in mapping.items()
            }
            
            async with self.redis.pipeline() as pipe:
                for key, value in full_mapping.items():
                    if ttl:
                        pipe.setex(key, ttl, value)
                    else:
                        pipe.set(key, value)
                await pipe.execute()
            
            return True
        except Exception as e:
            logger.error(f"批量设置失败: {e}")
            return False
    
    # ============ 模式匹配删除 ============
    
    async def delete_pattern(self, pattern: str) -> int:
        """删除匹配模式的缓存"""
        try:
            keys = []
            async for key in self.redis.scan_iter(match=pattern, count=1000):
                keys.append(key)
            
            if keys:
                await self.redis.delete(*keys)
            
            return len(keys)
        except Exception as e:
            logger.error(f"模式删除失败 [{pattern}]: {e}")
            return 0
    
    async def delete_by_prefix(self, prefix: str) -> int:
        """删除指定前缀的所有缓存"""
        return await self.delete_pattern(f"{prefix}:*")
    
    # ============ 特定业务缓存方法 ============
    
    async def get_knowledge_graph(self, branch: Optional[str] = None) -> Optional[dict]:
        """获取知识图谱缓存"""
        key = f"graph:{branch}" if branch else "graph:all"
        return await self.get(key, prefix="kg")
    
    async def set_knowledge_graph(
        self,
        data: dict,
        branch: Optional[str] = None,
        ttl: int = None
    ) -> bool:
        """缓存知识图谱"""
        key = f"graph:{branch}" if branch else "graph:all"
        ttl = ttl or settings.CACHE_TTL_KNOWLEDGE_GRAPH
        return await self.set(key, data, ttl=ttl, prefix="kg")
    
    async def get_learning_path(self, user_id: int, path_id: Optional[int] = None) -> Optional[dict]:
        """获取用户学习路径缓存"""
        key = f"user:{user_id}:path:{path_id}" if path_id else f"user:{user_id}:paths"
        return await self.get(key, prefix="learning")
    
    async def set_learning_path(
        self,
        user_id: int,
        data: dict,
        path_id: Optional[int] = None,
        ttl: int = None
    ) -> bool:
        """缓存用户学习路径"""
        key = f"user:{user_id}:path:{path_id}" if path_id else f"user:{user_id}:paths"
        ttl = ttl or settings.CACHE_TTL_LEARNING_PATH
        return await self.set(key, data, ttl=ttl, prefix="learning")
    
    async def invalidate_learning_path(self, user_id: int) -> int:
        """使学习路径缓存失效"""
        return await self.delete_pattern(f"learning:user:{user_id}:*")
    
    async def get_user_progress(self, user_id: int) -> Optional[dict]:
        """获取用户进度缓存"""
        return await self.get(f"user:{user_id}", prefix="progress")
    
    async def set_user_progress(
        self,
        user_id: int,
        data: dict,
        ttl: int = None
    ) -> bool:
        """缓存用户进度"""
        ttl = ttl or settings.CACHE_TTL_USER_PROGRESS
        return await self.set(f"user:{user_id}", data, ttl=ttl, prefix="progress")
    
    async def get_concept_info(self, concept_id: str) -> Optional[dict]:
        """获取概念信息缓存"""
        return await self.get(concept_id, prefix="concept")
    
    async def set_concept_info(
        self,
        concept_id: str,
        data: dict,
        ttl: int = None
    ) -> bool:
        """缓存概念信息"""
        ttl = ttl or settings.CACHE_TTL_CONCEPT_INFO
        return await self.set(concept_id, data, ttl=ttl, prefix="concept")


# 全局缓存实例
cache = RedisCache()


# ============ 装饰器 ============

def cached(
    ttl: int = None,
    prefix: str = None,
    key_func: Optional[Callable] = None
):
    """缓存装饰器 - 用于自动缓存函数结果"""
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
                logger.debug(f"缓存命中: {prefix}:{cache_key}")
                return result
            
            # 执行函数
            result = await func(*args, **kwargs)
            
            # 写入缓存
            await cache.set(cache_key, result, ttl=ttl, prefix=prefix)
            logger.debug(f"缓存写入: {prefix}:{cache_key}")
            
            return result
        
        @wraps(func)
        def sync_wrapper(*args, **kwargs):
            # 同步版本，用于Celery任务
            if key_func:
                cache_key = key_func(*args, **kwargs)
            else:
                cache_key = cache._hash_query(func.__name__, *args, **kwargs)
            
            # 注意：同步版本需要使用同步Redis客户端
            # 这里简化处理，实际使用时可能需要单独的同步Redis连接
            return func(*args, **kwargs)
        
        return async_wrapper if asyncio.iscoroutinefunction(func) else sync_wrapper
    return decorator


def cache_evict(prefix: str, pattern: Optional[str] = None):
    """缓存失效装饰器 - 用于在数据更新时清除缓存"""
    def decorator(func: Callable) -> Callable:
        @wraps(func)
        async def async_wrapper(*args, **kwargs):
            result = await func(*args, **kwargs)
            
            # 清除缓存
            if pattern:
                deleted = await cache.delete_pattern(f"{prefix}:{pattern}")
            else:
                deleted = await cache.delete_by_prefix(prefix)
            
            logger.debug(f"缓存清除: {prefix}, 删除{deleted}个键")
            return result
        
        return async_wrapper
    return decorator
