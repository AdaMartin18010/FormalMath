"""
FormalMath - 缓存策略配置
实现多层缓存架构，优化应用性能
"""

import os
from functools import wraps
from typing import Optional, Any, Callable
import hashlib
import json
import pickle

# Redis配置
REDIS_CONFIG = {
    'host': os.getenv('REDIS_HOST', 'redis'),
    'port': int(os.getenv('REDIS_PORT', 6379)),
    'db': int(os.getenv('REDIS_DB', 0)),
    'password': os.getenv('REDIS_PASSWORD'),
    'socket_timeout': int(os.getenv('REDIS_SOCKET_TIMEOUT', 5)),
    'socket_connect_timeout': int(os.getenv('REDIS_CONNECTION_TIMEOUT', 5)),
    'max_connections': int(os.getenv('REDIS_MAX_CONNECTIONS', 100)),
    'retry_on_timeout': True,
    'health_check_interval': 30,
}

# 缓存过期时间配置（秒）
CACHE_TTL = {
    'user_session': 3600 * 24,  # 24小时
    'api_response': 300,  # 5分钟
    'search_results': 600,  # 10分钟
    'static_data': 3600,  # 1小时
    'math_concepts': 3600 * 24,  # 24小时
    'lean_theorems': 3600 * 24,  # 24小时
    'calculation_result': 1800,  # 30分钟
    'user_progress': 300,  # 5分钟
    'leaderboard': 60,  # 1分钟
    'rate_limit': 60,  # 1分钟
}

# 缓存键前缀
CACHE_PREFIX = {
    'user': 'fm:user:',
    'session': 'fm:session:',
    'api': 'fm:api:',
    'search': 'fm:search:',
    'math': 'fm:math:',
    'lean': 'fm:lean:',
    'rate_limit': 'fm:ratelimit:',
    'lock': 'fm:lock:',
}


class CacheManager:
    """缓存管理器 - 统一管理多级缓存"""
    
    def __init__(self):
        self._redis = None
        self._local_cache = {}
        self._local_cache_ttl = {}
    
    @property
    def redis(self):
        """延迟初始化Redis连接"""
        if self._redis is None:
            try:
                import redis
                self._redis = redis.Redis(**REDIS_CONFIG)
            except ImportError:
                pass
        return self._redis
    
    def _generate_key(self, prefix: str, identifier: str) -> str:
        """生成缓存键"""
        return f"{CACHE_PREFIX.get(prefix, 'fm:')}{identifier}"
    
    def _hash_key(self, *args, **kwargs) -> str:
        """生成参数的哈希键"""
        key_data = json.dumps({'args': args, 'kwargs': kwargs}, sort_keys=True)
        return hashlib.md5(key_data.encode()).hexdigest()
    
    def get(self, key: str, prefix: str = 'api') -> Optional[Any]:
        """
        获取缓存值
        优先级：本地缓存 -> Redis缓存
        """
        cache_key = self._generate_key(prefix, key)
        
        # 检查本地缓存
        if cache_key in self._local_cache:
            import time
            if time.time() < self._local_cache_ttl.get(cache_key, 0):
                return self._local_cache[cache_key]
            else:
                # 清理过期本地缓存
                del self._local_cache[cache_key]
                del self._local_cache_ttl[cache_key]
        
        # 检查Redis缓存
        if self.redis:
            try:
                value = self.redis.get(cache_key)
                if value:
                    return pickle.loads(value)
            except Exception:
                pass
        
        return None
    
    def set(
        self,
        key: str,
        value: Any,
        prefix: str = 'api',
        ttl: Optional[int] = None,
        use_local: bool = False,
        local_ttl: int = 5
    ) -> bool:
        """
        设置缓存值
        
        Args:
            key: 缓存键
            value: 缓存值
            prefix: 键前缀
            ttl: Redis过期时间（秒）
            use_local: 是否同时缓存到本地
            local_ttl: 本地缓存过期时间（秒）
        """
        cache_key = self._generate_key(prefix, key)
        
        # 本地缓存
        if use_local:
            import time
            self._local_cache[cache_key] = value
            self._local_cache_ttl[cache_key] = time.time() + local_ttl
        
        # Redis缓存
        if self.redis:
            try:
                serialized = pickle.dumps(value)
                if ttl:
                    self.redis.setex(cache_key, ttl, serialized)
                else:
                    self.redis.set(cache_key, serialized)
                return True
            except Exception:
                pass
        
        return False
    
    def delete(self, key: str, prefix: str = 'api') -> bool:
        """删除缓存"""
        cache_key = self._generate_key(prefix, key)
        
        # 删除本地缓存
        if cache_key in self._local_cache:
            del self._local_cache[cache_key]
            del self._local_cache_ttl[cache_key]
        
        # 删除Redis缓存
        if self.redis:
            try:
                self.redis.delete(cache_key)
                return True
            except Exception:
                pass
        
        return False
    
    def invalidate_pattern(self, pattern: str, prefix: str = 'api') -> int:
        """按模式删除缓存"""
        cache_pattern = self._generate_key(prefix, pattern)
        
        if self.redis:
            try:
                keys = self.redis.keys(f"{cache_pattern}*")
                if keys:
                    return self.redis.delete(*keys)
            except Exception:
                pass
        
        return 0
    
    def get_or_set(
        self,
        key: str,
        getter: Callable,
        prefix: str = 'api',
        ttl: Optional[int] = None,
        use_local: bool = False
    ) -> Any:
        """
        获取或设置缓存
        
        Args:
            key: 缓存键
            getter: 获取数据的回调函数
            prefix: 键前缀
            ttl: 过期时间
            use_local: 是否使用本地缓存
        """
        # 尝试获取缓存
        value = self.get(key, prefix)
        if value is not None:
            return value
        
        # 获取数据
        value = getter()
        
        # 设置缓存
        self.set(key, value, prefix, ttl, use_local)
        
        return value


def cached(
    prefix: str = 'api',
    ttl: Optional[int] = None,
    key_builder: Optional[Callable] = None,
    unless: Optional[Callable] = None
):
    """
    缓存装饰器
    
    Args:
        prefix: 缓存键前缀
        ttl: 过期时间（秒）
        key_builder: 自定义键生成函数
        unless: 条件函数，返回True时不缓存
    """
    def decorator(func: Callable) -> Callable:
        cache_manager = CacheManager()
        
        @wraps(func)
        def wrapper(*args, **kwargs):
            # 检查unless条件
            if unless and unless(*args, **kwargs):
                return func(*args, **kwargs)
            
            # 生成缓存键
            if key_builder:
                cache_key = key_builder(*args, **kwargs)
            else:
                cache_key = cache_manager._hash_key(
                    func.__module__,
                    func.__name__,
                    *args,
                    **kwargs
                )
            
            # 获取或设置缓存
            return cache_manager.get_or_set(
                cache_key,
                lambda: func(*args, **kwargs),
                prefix=prefix,
                ttl=ttl or CACHE_TTL.get(prefix, 300)
            )
        
        # 添加清除缓存的方法
        wrapper.cache_clear = lambda: cache_manager.invalidate_pattern(
            '*', prefix
        )
        
        return wrapper
    return decorator


def cache_invalidate(pattern: str, prefix: str = 'api'):
    """清除匹配的缓存"""
    cache_manager = CacheManager()
    return cache_manager.invalidate_pattern(pattern, prefix)


# 预连接池管理
class ConnectionPool:
    """数据库连接池管理"""
    
    _instance = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._pools = {}
        return cls._instance
    
    def get_pool(self, db_url: str, **kwargs):
        """获取或创建连接池"""
        if db_url not in self._pools:
            from sqlalchemy import create_engine
            from sqlalchemy.pool import QueuePool
            
            self._pools[db_url] = create_engine(
                db_url,
                poolclass=QueuePool,
                pool_size=kwargs.get('pool_size', 20),
                max_overflow=kwargs.get('max_overflow', 10),
                pool_timeout=kwargs.get('pool_timeout', 30),
                pool_recycle=kwargs.get('pool_recycle', 3600),
                pool_pre_ping=True,
            )
        
        return self._pools[db_url]


# 全局缓存管理器实例
cache = CacheManager()
connection_pool = ConnectionPool()
