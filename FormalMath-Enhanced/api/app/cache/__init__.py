"""
缓存模块
"""
from .redis_cache import cache, RedisCache, cached, cache_evict

__all__ = ["cache", "RedisCache", "cached", "cache_evict"]
