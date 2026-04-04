/**
 * 缓存工具
 * 提供客户端缓存功能
 */

interface CacheOptions {
  ttl?: number; // 过期时间（毫秒）
  maxSize?: number; // 最大条目数
}

interface CacheEntry<T> {
  value: T;
  timestamp: number;
  expiresAt: number;
}

class Cache {
  private storage: Map<string, CacheEntry<unknown>> = new Map();
  private options: Required<CacheOptions>;

  constructor(options: CacheOptions = {}) {
    this.options = {
      ttl: options.ttl || 5 * 60 * 1000, // 默认5分钟
      maxSize: options.maxSize || 100, // 默认100条
    };
  }

  /**
   * 获取缓存值
   */
  get<T>(key: string): T | undefined {
    const entry = this.storage.get(key);
    
    if (!entry) {
      return undefined;
    }

    // 检查是否过期
    if (Date.now() > entry.expiresAt) {
      this.delete(key);
      return undefined;
    }

    return entry.value as T;
  }

  /**
   * 设置缓存值
   */
  set<T>(key: string, value: T, ttl?: number): void {
    // 检查容量
    if (this.storage.size >= this.options.maxSize && !this.storage.has(key)) {
      this.evictLRU();
    }

    const now = Date.now();
    const entry: CacheEntry<T> = {
      value,
      timestamp: now,
      expiresAt: now + (ttl || this.options.ttl),
    };

    this.storage.set(key, entry as CacheEntry<unknown>);
  }

  /**
   * 删除缓存
   */
  delete(key: string): boolean {
    return this.storage.delete(key);
  }

  /**
   * 检查是否存在
   */
  has(key: string): boolean {
    const entry = this.storage.get(key);
    if (!entry) return false;
    
    if (Date.now() > entry.expiresAt) {
      this.delete(key);
      return false;
    }
    
    return true;
  }

  /**
   * 清空缓存
   */
  clear(): void {
    this.storage.clear();
  }

  /**
   * 获取缓存大小
   */
  size(): number {
    return this.storage.size;
  }

  /**
   * 获取所有键
   */
  keys(): string[] {
    return Array.from(this.storage.keys());
  }

  /**
   * LRU 淘汰
   */
  private evictLRU(): void {
    const entries = Array.from(this.storage.entries());
    if (entries.length === 0) return;

    // 找到最旧的条目
    const oldest = entries.reduce((min, entry) =>
      entry[1].timestamp < min[1].timestamp ? entry : min
    );

    this.storage.delete(oldest[0]);
  }

  /**
   * 清理过期条目
   */
  cleanup(): number {
    const now = Date.now();
    let cleaned = 0;

    for (const [key, entry] of this.storage.entries()) {
      if (now > entry.expiresAt) {
        this.storage.delete(key);
        cleaned++;
      }
    }

    return cleaned;
  }

  /**
   * 带缓存的函数包装
   */
  wrap<T, Args extends unknown[]>(
    fn: (...args: Args) => Promise<T>,
    keyGenerator?: (...args: Args) => string
  ): (...args: Args) => Promise<T> {
    return async (...args: Args): Promise<T> => {
      const key = keyGenerator ? keyGenerator(...args) : JSON.stringify(args);
      
      const cached = this.get<T>(key);
      if (cached !== undefined) {
        return cached;
      }

      const result = await fn(...args);
      this.set(key, result);
      return result;
    };
  }
}

// 默认缓存实例
export const cache = new Cache();

// 创建新缓存实例
export function createCache(options: CacheOptions): Cache {
  return new Cache(options);
}

// 内存缓存（不持久化）
export const memoryCache = new Cache({ ttl: 60 * 1000 }); // 1分钟

// API 响应缓存
export const apiCache = new Cache({ ttl: 5 * 60 * 1000 }); // 5分钟

// 会话缓存
export const sessionCache = new Cache({ ttl: 30 * 60 * 1000 }); // 30分钟

export default cache;
