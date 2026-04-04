"""
Redis缓存层更新
与CDN策略协同工作的增强版Redis缓存
"""

import json
import pickle
import hashlib
import logging
from typing import Optional, Any, Union, Callable, List
from functools import wraps
import asyncio
from datetime import datetime, timedelta
from redis.asyncio import Redis
from redis.asyncio.connection import ConnectionPool

# 假设settings从配置导入
try:
    from api.app.core.config import settings
except ImportError:
    class Settings:
        REDIS_URL = "redis://localhost:6379/0"
        REDIS_MAX_CONNECTIONS = 100
        REDIS_SOCKET_TIMEOUT = 5
        REDIS_SOCKET_CONNECT_TIMEOUT = 5
        CACHE_TTL_KNOWLEDGE_GRAPH = 7200
        CACHE_TTL_LEARNING_PATH = 600
        CACHE_TTL_USER_PROGRESS = 300
        CACHE_TTL_CONCEPT_INFO = 3600
    settings = Settings()

logger = logging.getLogger(__name__)


class TieredCacheManager:
    """
    分层缓存管理器
    L1: 内存缓存 (进程内)
    L2: Redis缓存 (分布式)
    L3: CDN缓存 (边缘)
    """
    
    def __init__(self):
        self._memory_cache = {}  # L1: 内存缓存
        self._memory_ttl = {}
        self._redis: Optional[Redis] = None  # L2: Redis
        self._initialized = False
        self._lock = asyncio.Lock()
    
    async def initialize(self):
        """初始化Redis连接"""
        if self._initialized:
            return
        
        async with self._lock:
            if self._initialized:
                return
            
            try:
                pool = ConnectionPool.from_url(
                    settings.REDIS_URL,
                    max_connections=settings.REDIS_MAX_CONNECTIONS,
                    socket_timeout=settings.REDIS_SOCKET_TIMEOUT,
                    socket_connect_timeout=settings.REDIS_SOCKET_CONNECT_TIMEOUT,
                    decode_responses=False
                )
                self._redis = Redis(connection_pool=pool)
                await self._redis.ping()
                self._initialized = True
                logger.info("分层缓存管理器初始化成功")
            except Exception as e:
                logger.error(f"Redis初始化失败: {e}")
                self._redis = None
    
    # ============ L1: 内存缓存 ============
    
    def _memory_get(self, key: str) -> Optional[Any]:
        """从内存缓存获取"""
        if key not in self._memory_cache:
            return None
        
        # 检查过期
        if key in self._memory_ttl:
            if datetime.now() > self._memory_ttl[key]:
                del self._memory_cache[key]
                del self._memory_ttl[key]
                return None
        
        return self._memory_cache[key]
    
    def _memory_set(self, key: str, value: Any, ttl: int = 60):
        """设置内存缓存"""
        self._memory_cache[key] = value
        if ttl:
            self._memory_ttl[key] = datetime.now() + timedelta(seconds=ttl)
    
    def _memory_delete(self, key: str):
        """删除内存缓存"""
        self._memory_cache.pop(key, None)
        self._memory_ttl.pop(key, None)
    
    # ============ L2: Redis缓存 ============
    
    def _serialize(self, value: Any) -> bytes:
        """序列化值"""
        return pickle.dumps(value)
    
    def _deserialize(self, value: bytes) -> Any:
        """反序列化值"""
        return pickle.loads(value)
    
    async def _redis_get(self, key: str) -> Optional[Any]:
        """从Redis获取"""
        if not self._redis:
            return None
        
        try:
            value = await self._redis.get(key)
            if value is None:
                return None
            return self._deserialize(value)
        except Exception as e:
            logger.error(f"Redis获取失败: {e}")
            return None
    
    async def _redis_set(self, key: str, value: Any, ttl: int = None):
        """设置Redis缓存"""
        if not self._redis:
            return False
        
        try:
            serialized = self._serialize(value)
            if ttl:
                await self._redis.setex(key, ttl, serialized)
            else:
                await self._redis.set(key, serialized)
            return True
        except Exception as e:
            logger.error(f"Redis设置失败: {e}")
            return False
    
    async def _redis_delete(self, key: str):
        """删除Redis缓存"""
        if not self._redis:
            return False
        
        try:
            await self._redis.delete(key)
            return True
        except Exception as e:
            logger.error(f"Redis删除失败: {e}")
            return False
    
    # ============ 分层缓存接口 ============
    
    async def get(
        self,
        key: str,
        use_l1: bool = True,
        use_l2: bool = True
    ) -> Optional[Any]:
        """
        分层获取缓存
        L1 -> L2 -> None
        """
        # L1: 内存缓存
        if use_l1:
            value = self._memory_get(key)
            if value is not None:
                logger.debug(f"L1缓存命中: {key}")
                return value
        
        # L2: Redis缓存
        if use_l2 and self._redis:
            value = await self._redis_get(key)
            if value is not None:
                logger.debug(f"L2缓存命中: {key}")
                # 回填L1
                if use_l1:
                    self._memory_set(key, value, ttl=60)
                return value
        
        return None
    
    async def set(
        self,
        key: str,
        value: Any,
        l1_ttl: int = 60,    # L1默认60秒
        l2_ttl: int = None   # L2默认无过期
    ):
        """分层设置缓存"""
        # L1
        if l1_ttl > 0:
            self._memory_set(key, value, ttl=l1_ttl)
        
        # L2
        if l2_ttl is not None and self._redis:
            await self._redis_set(key, value, ttl=l2_ttl)
    
    async def delete(self, key: str, cascade: bool = True):
        """删除缓存"""
        self._memory_delete(key)
        if cascade and self._redis:
            await self._redis_delete(key)
    
    async def get_with_stale(
        self,
        key: str,
        fresh_ttl: int = 3600,
        stale_ttl: int = 86400
    ) -> tuple[Optional[Any], bool]:
        """
        获取缓存，支持stale-while-revalidate模式
        
        Returns:
            (value, is_stale): 缓存值和是否过期
        """
        # 尝试从Redis获取
        if not self._redis:
            return None, False
        
        try:
            # 获取值和TTL
            pipe = self._redis.pipeline()
            pipe.get(key)
            pipe.ttl(key)
            result = await pipe.execute()
            
            value_bytes = result[0]
            ttl = result[1]
            
            if value_bytes is None:
                return None, False
            
            value = self._deserialize(value_bytes)
            
            # 判断是否是stale数据
            is_stale = ttl < 0 or ttl < (fresh_ttl - stale_ttl)
            
            return value, is_stale
            
        except Exception as e:
            logger.error(f"获取缓存失败: {e}")
            return None, False
    
    # ============ 批量操作 ============
    
    async def mget(self, keys: List[str]) -> List[Optional[Any]]:
        """批量获取"""
        if not self._redis:
            return [None] * len(keys)
        
        try:
            values = await self._redis.mget(keys)
            return [self._deserialize(v) if v else None for v in values]
        except Exception as e:
            logger.error(f"批量获取失败: {e}")
            return [None] * len(keys)
    
    async def mset(self, mapping: dict, ttl: int = None):
        """批量设置"""
        if not self._redis:
            return False
        
        try:
            serialized = {k: self._serialize(v) for k, v in mapping.items()}
            
            async with self._redis.pipeline() as pipe:
                for k, v in serialized.items():
                    if ttl:
                        pipe.setex(k, ttl, v)
                    else:
                        pipe.set(k, v)
                await pipe.execute()
            
            return True
        except Exception as e:
            logger.error(f"批量设置失败: {e}")
            return False
    
    # ============ 标签管理 ============
    
    async def set_with_tags(
        self,
        key: str,
        value: Any,
        tags: List[str],
        ttl: int = None
    ):
        """设置带标签的缓存"""
        # 设置值
        await self._redis_set(key, value, ttl)
        
        # 添加标签索引
        if tags:
            async with self._redis.pipeline() as pipe:
                for tag in tags:
                    tag_key = f"_tag:{tag}"
                    pipe.sadd(tag_key, key)
                    if ttl:
                        pipe.expire(tag_key, ttl)
                await pipe.execute()
    
    async def delete_by_tag(self, tag: str) -> int:
        """通过标签删除缓存"""
        if not self._redis:
            return 0
        
        try:
            tag_key = f"_tag:{tag}"
            
            # 获取所有带此标签的键
            keys = await self._redis.smembers(tag_key)
            if not keys:
                return 0
            
            # 删除缓存
            keys = [k.decode() if isinstance(k, bytes) else k for k in keys]
            await self._redis.delete(*keys)
            
            # 删除标签
            await self._redis.delete(tag_key)
            
            logger.info(f"通过标签'{tag}'删除{len(keys)}个缓存")
            return len(keys)
            
        except Exception as e:
            logger.error(f"通过标签删除失败: {e}")
            return 0
    
    # ============ 缓存统计 ============
    
    async def get_stats(self) -> dict:
        """获取缓存统计"""
        stats = {
            "l1_memory_keys": len(self._memory_cache),
            "l1_memory_size": len(str(self._memory_cache)),
        }
        
        if self._redis:
            try:
                info = await self._redis.info()
                stats["l2_redis_keys"] = info.get("db0", {}).get("keys", 0)
                stats["l2_redis_memory"] = info.get("used_memory_human", "N/A")
                stats["l2_redis_hits"] = info.get("keyspace_hits", 0)
                stats["l2_redis_misses"] = info.get("keyspace_misses", 0)
                
                # 计算命中率
                hits = stats["l2_redis_hits"]
                misses = stats["l2_redis_misses"]
                if hits + misses > 0:
                    stats["l2_hit_rate"] = hits / (hits + misses)
            except Exception as e:
                logger.error(f"获取Redis统计失败: {e}")
        
        return stats
    
    async def close(self):
        """关闭连接"""
        if self._redis:
            await self._redis.close()
            self._initialized = False


# 全局实例
tiered_cache = TieredCacheManager()


# ============ 增强的装饰器 ============

def tiered_cached(
    l1_ttl: int = 60,      # L1: 1分钟
    l2_ttl: int = 3600,    # L2: 1小时
    key_prefix: str = None,
    tags: List[str] = None
):
    """
    分层缓存装饰器
    
    Args:
        l1_ttl: 内存缓存TTL(秒)
        l2_ttl: Redis缓存TTL(秒)
        key_prefix: 键前缀
        tags: 缓存标签列表
    """
    def decorator(func: Callable) -> Callable:
        @wraps(func)
        async def async_wrapper(*args, **kwargs):
            # 生成缓存键
            key_data = json.dumps({"args": args, "kwargs": kwargs}, sort_keys=True, default=str)
            cache_key = hashlib.md5(key_data.encode()).hexdigest()[:16]
            
            if key_prefix:
                cache_key = f"{key_prefix}:{cache_key}"
            
            # 尝试获取缓存
            result = await tiered_cache.get(cache_key)
            if result is not None:
                logger.debug(f"缓存命中: {cache_key}")
                return result
            
            # 执行函数
            result = await func(*args, **kwargs)
            
            # 写入缓存
            await tiered_cache.set(cache_key, result, l1_ttl=l1_ttl, l2_ttl=l2_ttl)
            
            # 添加标签
            if tags and tiered_cache._redis:
                await tiered_cache.set_with_tags(cache_key, result, tags, ttl=l2_ttl)
            
            return result
        
        return async_wrapper
    return decorator


def swr_cached(
    fresh_ttl: int = 3600,    # 新鲜期1小时
    stale_ttl: int = 86400,   # 过期后仍可服务1天
    key_prefix: str = None
):
    """
    Stale-While-Revalidate 缓存装饰器
    
    返回过期数据的同时，异步刷新缓存
    """
    def decorator(func: Callable) -> Callable:
        @wraps(func)
        async def async_wrapper(*args, **kwargs):
            key_data = json.dumps({"args": args, "kwargs": kwargs}, sort_keys=True, default=str)
            cache_key = hashlib.md5(key_data.encode()).hexdigest()[:16]
            
            if key_prefix:
                cache_key = f"{key_prefix}:{cache_key}"
            
            # 尝试获取缓存(支持过期数据)
            result, is_stale = await tiered_cache.get_with_stale(
                cache_key, fresh_ttl, stale_ttl
            )
            
            if result is not None and not is_stale:
                # 新鲜缓存，直接返回
                return result
            
            if result is not None and is_stale:
                # 过期缓存，先返回，再异步刷新
                asyncio.create_task(_refresh_cache(func, args, kwargs, cache_key, stale_ttl))
                return result
            
            # 无缓存，执行函数
            result = await func(*args, **kwargs)
            await tiered_cache.set(cache_key, result, l2_ttl=stale_ttl)
            return result
        
        return async_wrapper
    return decorator


async def _refresh_cache(func, args, kwargs, key, ttl):
    """异步刷新缓存"""
    try:
        result = await func(*args, **kwargs)
        await tiered_cache.set(key, result, l2_ttl=ttl)
        logger.debug(f"异步刷新缓存: {key}")
    except Exception as e:
        logger.error(f"异步刷新缓存失败: {e}")
