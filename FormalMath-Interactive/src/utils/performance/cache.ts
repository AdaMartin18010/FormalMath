/**
 * 缓存管理工具
 * 性能优化：智能缓存策略
 */

interface CacheEntry<T> {
  value: T;
  timestamp: number;
  expiresAt: number;
  accessCount: number;
}

interface CacheOptions {
  /** 默认TTL（毫秒） */
  ttl?: number;
  /** 最大缓存项数 */
  maxSize?: number;
  /** 清理间隔（毫秒） */
  cleanupInterval?: number;
}

/**
 * LRU缓存实现
 */
export class LRUCache<T> {
  private cache: Map<string, CacheEntry<T>>;
  private options: Required<CacheOptions>;
  private cleanupTimer: ReturnType<typeof setInterval> | null = null;

  constructor(options: CacheOptions = {}) {
    this.options = {
      ttl: 5 * 60 * 1000, // 5分钟
      maxSize: 100,
      cleanupInterval: 60 * 1000, // 1分钟
      ...options,
    };
    
    this.cache = new Map();
    this.startCleanup();
  }

  /**
   * 获取缓存项
   */
  get(key: string): T | undefined {
    const entry = this.cache.get(key);
    
    if (!entry) {
      return undefined;
    }

    // 检查是否过期
    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      return undefined;
    }

    // 更新访问信息
    entry.accessCount++;
    entry.timestamp = Date.now();
    
    // 移到最新（LRU）
    this.cache.delete(key);
    this.cache.set(key, entry);

    return entry.value;
  }

  /**
   * 设置缓存项
   */
  set(key: string, value: T, ttl?: number): void {
    // 清理过期项
    this.evictIfNeeded();

    const now = Date.now();
    const entry: CacheEntry<T> = {
      value,
      timestamp: now,
      expiresAt: now + (ttl ?? this.options.ttl),
      accessCount: 1,
    };

    this.cache.set(key, entry);
  }

  /**
   * 删除缓存项
   */
  delete(key: string): boolean {
    return this.cache.delete(key);
  }

  /**
   * 检查缓存项是否存在且未过期
   */
  has(key: string): boolean {
    const entry = this.cache.get(key);
    if (!entry) return false;
    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      return false;
    }
    return true;
  }

  /**
   * 清空缓存
   */
  clear(): void {
    this.cache.clear();
  }

  /**
   * 获取缓存大小
   */
  size(): number {
    return this.cache.size;
  }

  /**
   * 获取缓存统计
   */
  getStats(): {
    size: number;
    maxSize: number;
    entries: Array<{ key: string; age: number; accessCount: number }>;
  } {
    const now = Date.now();
    return {
      size: this.cache.size,
      maxSize: this.options.maxSize,
      entries: Array.from(this.cache.entries()).map(([key, entry]) => ({
        key,
        age: now - entry.timestamp,
        accessCount: entry.accessCount,
      })),
    };
  }

  /**
   * 需要时清理旧项
   */
  private evictIfNeeded(): void {
    if (this.cache.size < this.options.maxSize) {
      return;
    }

    // 删除最旧的项
    const firstKey = this.cache.keys().next().value;
    if (firstKey) {
      this.cache.delete(firstKey);
    }
  }

  /**
   * 清理过期项
   */
  private cleanup(): void {
    const now = Date.now();
    for (const [key, entry] of this.cache.entries()) {
      if (now > entry.expiresAt) {
        this.cache.delete(key);
      }
    }
  }

  /**
   * 启动自动清理
   */
  private startCleanup(): void {
    this.cleanupTimer = setInterval(() => {
      this.cleanup();
    }, this.options.cleanupInterval);
  }

  /**
   * 停止自动清理
   */
  stopCleanup(): void {
    if (this.cleanupTimer) {
      clearInterval(this.cleanupTimer);
      this.cleanupTimer = null;
    }
  }

  /**
   * 销毁缓存
   */
  destroy(): void {
    this.stopCleanup();
    this.clear();
  }
}

/**
 * 带缓存的函数包装器
 */
export function withCache<T extends (...args: any[]) => any>(
  fn: T,
  options: CacheOptions & {
    /** 生成缓存键的函数 */
    keyGenerator?: (...args: Parameters<T>) => string;
  } = {}
): T & { cache: LRUCache<ReturnType<T>>; invalidate: (...args: Parameters<T>) => void } {
  const cache = new LRUCache<ReturnType<T>>(options);
  
  const keyGenerator = options.keyGenerator || 
    ((...args: Parameters<T>) => JSON.stringify(args));

  const cachedFn = ((...args: Parameters<T>): ReturnType<T> => {
    const key = keyGenerator(...args);
    
    const cached = cache.get(key);
    if (cached !== undefined) {
      return cached;
    }

    const result = fn(...args);
    cache.set(key, result);
    return result;
  }) as T & { cache: LRUCache<ReturnType<T>>; invalidate: (...args: Parameters<T>) => void };

  cachedFn.cache = cache;
  
  cachedFn.invalidate = (...args: Parameters<T>) => {
    const key = keyGenerator(...args);
    cache.delete(key);
  };

  return cachedFn;
}

/**
 * 内存存储（使用localStorage/sessionStorage）
 */
export const storageCache = {
  /**
   * 设置本地存储缓存
   */
  set<T>(key: string, value: T, ttl?: number): void {
    const entry = {
      value,
      expiresAt: ttl ? Date.now() + ttl : null,
    };
    localStorage.setItem(`cache:${key}`, JSON.stringify(entry));
  },

  /**
   * 获取本地存储缓存
   */
  get<T>(key: string): T | null {
    const stored = localStorage.getItem(`cache:${key}`);
    if (!stored) return null;

    try {
      const entry = JSON.parse(stored);
      
      if (entry.expiresAt && Date.now() > entry.expiresAt) {
        localStorage.removeItem(`cache:${key}`);
        return null;
      }

      return entry.value;
    } catch {
      return null;
    }
  },

  /**
   * 删除本地存储缓存
   */
  remove(key: string): void {
    localStorage.removeItem(`cache:${key}`);
  },

  /**
   * 清理过期缓存
   */
  cleanup(): void {
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i);
      if (key?.startsWith('cache:')) {
        try {
          const entry = JSON.parse(localStorage.getItem(key) || '{}');
          if (entry.expiresAt && Date.now() > entry.expiresAt) {
            localStorage.removeItem(key);
          }
        } catch {
          // 忽略解析错误
        }
      }
    }
  },
};

export default LRUCache;
