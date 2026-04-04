"""
FormalMath API - Redis集群缓存层实现
支持Redis Standalone、Sentinel、Cluster三种模式
"""
import json
import pickle
import hashlib
import logging
from typing import Optional, Any, Union, Callable, List
from functools import wraps
import asyncio
from redis.asyncio import Redis
from redis.asyncio.connection import ConnectionPool, BlockingConnectionPool
from redis.asyncio.sentinel import Sentinel
from redis.asyncio.cluster import RedisCluster
from ..core.config_production import settings_production as settings

logger = logging.getLogger(__name__)


class RedisClusterCache:
    """Redis集群缓存管理器 - 支持多种部署模式"""
    
    _instance: Optional['RedisClusterCache'] = None
    _lock = asyncio.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._initialized = False
        return cls._instance
    
    def __init__(self):
        if self._initialized:
            return
        
        self._redis: Optional[Union[Redis, RedisCluster]] = None
        self._pool: Optional[ConnectionPool] = None
        self._initialized = True
    
    async def initialize(self):
        """初始化Redis连接 - 根据配置自动选择模式"""
        if self._redis is not None:
            return
        
        try:
            if settings.REDIS_MODE == "cluster":
                await self._init_cluster_mode()
            elif settings.REDIS_MODE == "sentinel":
                await self._init_sentinel_mode()
            else:
                await self._init_standalone_mode()
            
            # 测试连接
            await self._redis.ping()
            logger.info(f"Redis缓存初始化成功: 模式={settings.REDIS_MODE}")
            
        except Exception as e:
            logger.error(f"Redis缓存初始化失败: {e}")
            self._redis = None
            raise
    
    async def _init_standalone_mode(self):
        """初始化单机模式"""
        # 构建Redis URL
        if hasattr(settings, 'REDIS_URL') and settings.REDIS_URL:
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
            retry_on_timeout=settings.REDIS_RETRY_ON_TIMEOUT,
            health_check_interval=settings.REDIS_HEALTH_CHECK_INTERVAL,
            decode_responses=False
        )
        
        self._redis = Redis(connection_pool=self._pool)
    
    async def _init_sentinel_mode(self):
        """初始化Sentinel模式"""
        sentinel_hosts = []
        for host_port in settings.REDIS_SENTINEL_HOSTS:
            host, port = host_port.split(":")
            sentinel_hosts.append((host, int(port)))
        
        sentinel = Sentinel(
            sentinel_hosts,
            password=settings.REDIS_SENTINEL_PASSWORD,
            socket_timeout=settings.REDIS_SOCKET_TIMEOUT,
            socket_connect_timeout=settings.REDIS_SOCKET_CONNECT_TIMEOUT,
            retry_on_timeout=settings.REDIS_RETRY_ON_TIMEOUT,
        )
        
        # 获取主节点
        self._redis = sentinel.master_for(
            settings.REDIS_SENTINEL_MASTER_NAME,
            password=settings.REDIS_PASSWORD,
            max_connections=settings.REDIS_MAX_CONNECTIONS,
            decode_responses=False
        )
    
    async def _init_cluster_mode(self):
        """初始化集群模式"""
        startup_nodes = []
        for node in settings.REDIS_CLUSTER_NODES:
            host, port = node.split(":")
            startup_nodes.append({"host": host, "port": int(port)})
        
        self._redis = await RedisCluster.from_startup_nodes(
            startup_nodes,
            password=settings.REDIS_CLUSTER_PASSWORD or settings.REDIS_PASSWORD,
            skip_full_coverage_check=settings.REDIS_CLUSTER_SKIP_FULL_COVERAGE_CHECK,
            max_connections_per_node=settings.REDIS_MAX_CONNECTIONS,
            socket_timeout=settings.REDIS_SOCKET_TIMEOUT,
            socket_connect_timeout=settings.REDIS_SOCKET_CONNECT_TIMEOUT,
            retry_on_timeout=settings.REDIS_RETRY_ON_TIMEOUT,
            decode_responses=False
        )
    
    async def close(self):
        """关闭Redis连接"""
        if self._redis:
            await self._redis.close()
            self._redis = None
        if self._pool:
            await self._pool.disconnect()
            self._pool = None
        logger.info("Redis连接已关闭")
    
    @property
    def redis(self) -> Union[Redis, RedisCluster]:
        """获取Redis客户端"""
        if self._redis is None:
            raise RuntimeError("Redis缓存未初始化，请先调用initialize()")
        return self._redis
    
    def _serialize(self, value: Any) -> bytes:
        """序列化值 - 使用pickle保证兼容性"""
        return pickle.dumps(value, protocol=pickle.HIGHEST_PROTOCOL)
    
    def _deserialize(self, value: bytes) -> Any:
        """反序列化值"""
        return pickle.loads(value)
    
    def _make_key(self, key: str, prefix: Optional[str] = None) -> str:
        """构建缓存键 - 添加命名空间"""
        namespace = f"{settings.ENVIRONMENT}:formalmath"
        if prefix:
            return f"{namespace}:{prefix}:{key}"
        return f"{namespace}:{key}"
    
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
        prefix: Optional[str] = None,
        nx: bool = False,  # 仅当键不存在时设置
        xx: bool = False,  # 仅当键存在时设置
    ) -> bool:
        """设置缓存值"""
        try:
            full_key = self._make_key(key, prefix)
            serialized = self._serialize(value)
            
            if nx:
                result = await self.redis.setnx(full_key, serialized)
                if result and ttl:
                    await self.redis.expire(full_key, ttl)
                return bool(result)
            elif xx:
                result = await self.redis.set(full_key, serialized, xx=True, ex=ttl)
                return result is not None
            else:
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
        """获取缓存剩余TTL（秒）"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.ttl(full_key)
        except Exception as e:
            logger.error(f"获取TTL失败 [{key}]: {e}")
            return -2
    
    async def expire(self, key: str, seconds: int, prefix: Optional[str] = None) -> bool:
        """设置键的过期时间"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.expire(full_key, seconds)
        except Exception as e:
            logger.error(f"设置过期时间失败 [{key}]: {e}")
            return False
    
    async def incr(self, key: str, amount: int = 1, prefix: Optional[str] = None) -> int:
        """原子递增"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.incrby(full_key, amount)
        except Exception as e:
            logger.error(f"递增失败 [{key}]: {e}")
            return 0
    
    async def decr(self, key: str, amount: int = 1, prefix: Optional[str] = None) -> int:
        """原子递减"""
        try:
            full_key = self._make_key(key, prefix)
            return await self.redis.decrby(full_key, amount)
        except Exception as e:
            logger.error(f"递减失败 [{key}]: {e}")
            return 0
    
    # ============ 批量操作 ============
    
    async def mget(self, keys: List[str], prefix: Optional[str] = None) -> List[Any]:
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
    
    # ============ 分布式锁 ============
    
    async def acquire_lock(
        self, 
        lock_name: str, 
        timeout: int = 30, 
        blocking_timeout: int = 10
    ) -> bool:
        """获取分布式锁"""
        try:
            lock_key = self._make_key(f"lock:{lock_name}")
            # 使用 SET NX EX 实现锁
            result = await self.redis.set(
                lock_key, 
                "1", 
                nx=True, 
                ex=timeout
            )
            return result is not None
        except Exception as e:
            logger.error(f"获取锁失败 [{lock_name}]: {e}")
            return False
    
    async def release_lock(self, lock_name: str) -> bool:
        """释放分布式锁"""
        try:
            lock_key = self._make_key(f"lock:{lock_name}")
            await self.redis.delete(lock_key)
            return True
        except Exception as e:
            logger.error(f"释放锁失败 [{lock_name}]: {e}")
            return False
    
    # ============ 模式匹配删除 ============
    
    async def delete_pattern(self, pattern: str) -> int:
        """删除匹配模式的缓存"""
        try:
            keys = []
            async for key in self.redis.scan_iter(match=pattern, count=1000):
                keys.append(key)
            
            if keys:
                # 分批删除，每批1000个
                batch_size = 1000
                for i in range(0, len(keys), batch_size):
                    batch = keys[i:i + batch_size]
                    await self.redis.delete(*batch)
            
            return len(keys)
        except Exception as e:
            logger.error(f"模式删除失败 [{pattern}]: {e}")
            return 0
    
    async def delete_by_prefix(self, prefix: str) -> int:
        """删除指定前缀的所有缓存"""
        namespace = f"{settings.ENVIRONMENT}:formalmath:{prefix}"
        return await self.delete_pattern(f"{namespace}:*")
    
    # ============ 计数器和限流 ============
    
    async def rate_limit_check(
        self, 
        key: str, 
        limit: int, 
        window: int
    ) -> tuple[bool, int, int]:
        """
        滑动窗口限流检查
        
        Returns:
            (是否允许, 当前计数, 重置时间)
        """
        try:
            full_key = self._make_key(f"ratelimit:{key}")
            now = asyncio.get_event_loop().time()
            
            # 使用Redis sorted set实现滑动窗口
            pipe = self.redis.pipeline()
            
            # 移除窗口外的记录
            pipe.zremrangebyscore(full_key, 0, now - window)
            
            # 获取当前计数
            pipe.zcard(full_key)
            
            # 添加当前请求
            pipe.zadd(full_key, {str(now): now})
            
            # 设置过期时间
            pipe.expire(full_key, window + 1)
            
            results = await pipe.execute()
            current_count = results[1]
            
            # 获取最早记录的过期时间（近似）
            oldest = await self.redis.zrange(full_key, 0, 0, withscores=True)
            reset_time = int(oldest[0][1] + window) if oldest else int(now + window)
            
            allowed = current_count <= limit
            return allowed, current_count, reset_time
            
        except Exception as e:
            logger.error(f"限流检查失败 [{key}]: {e}")
            # 失败时允许访问
            return True, 0, 0
    
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
    
    async def invalidate_knowledge_graph(self, branch: Optional[str] = None) -> int:
        """使知识图谱缓存失效"""
        if branch:
            return await self.delete(f"graph:{branch}", prefix="kg")
        else:
            return await self.delete_by_prefix("kg")
    
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
    
    async def health_check(self) -> dict:
        """Redis健康检查"""
        try:
            start = asyncio.get_event_loop().time()
            await self.redis.ping()
            latency = (asyncio.get_event_loop().time() - start) * 1000
            
            info = await self.redis.info()
            
            return {
                "status": "healthy",
                "mode": settings.REDIS_MODE,
                "latency_ms": round(latency, 2),
                "version": info.get("redis_version", "unknown"),
                "connected_clients": info.get("connected_clients", 0),
                "used_memory_human": info.get("used_memory_human", "unknown"),
                "hit_rate": info.get("keyspace_hits", 0) / (
                    info.get("keyspace_hits", 0) + info.get("keyspace_misses", 1)
                ) if info.get("keyspace_hits") else 0
            }
        except Exception as e:
            return {
                "status": "unhealthy",
                "error": str(e)
            }


# 全局缓存实例
cache = RedisClusterCache()


# ============ 装饰器 ============

def cached(
    ttl: int = None,
    prefix: str = None,
    key_func: Optional[Callable] = None,
    cache_none: bool = False
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
            if result is not None or cache_none:
                logger.debug(f"缓存命中: {prefix}:{cache_key}")
                return result
            
            # 执行函数
            result = await func(*args, **kwargs)
            
            # 写入缓存（如果结果不为None或允许缓存None）
            if result is not None or cache_none:
                await cache.set(cache_key, result, ttl=ttl, prefix=prefix)
                logger.debug(f"缓存写入: {prefix}:{cache_key}")
            
            return result
        
        return async_wrapper
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
