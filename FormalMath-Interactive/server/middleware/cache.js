/**
 * 服务器端缓存中间件
 * 提供响应缓存和 ETag 支持
 */

const crypto = require('crypto');

// 内存缓存存储
class MemoryCache {
  constructor(options = {}) {
    this.cache = new Map();
    this.maxSize = options.maxSize || 1000;
    this.defaultTTL = options.defaultTTL || 5 * 60 * 1000; // 5分钟
    this.stats = {
      hits: 0,
      misses: 0,
      evictions: 0,
    };
  }

  generateKey(req) {
    const data = `${req.method}:${req.originalUrl}:${JSON.stringify(req.query)}`;
    return crypto.createHash('md5').update(data).digest('hex');
  }

  get(key) {
    const entry = this.cache.get(key);
    
    if (!entry) {
      this.stats.misses++;
      return null;
    }

    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      this.stats.misses++;
      return null;
    }

    this.stats.hits++;
    return entry.value;
  }

  set(key, value, ttl) {
    // LRU 淘汰
    if (this.cache.size >= this.maxSize && !this.cache.has(key)) {
      this.evictLRU();
    }

    const expiresAt = Date.now() + (ttl || this.defaultTTL);
    this.cache.set(key, {
      value,
      expiresAt,
      accessTime: Date.now(),
    });
  }

  evictLRU() {
    let oldest = null;
    let oldestKey = null;

    for (const [key, entry] of this.cache.entries()) {
      if (!oldest || entry.accessTime < oldest.accessTime) {
        oldest = entry;
        oldestKey = key;
      }
    }

    if (oldestKey) {
      this.cache.delete(oldestKey);
      this.stats.evictions++;
    }
  }

  delete(key) {
    return this.cache.delete(key);
  }

  clear() {
    this.cache.clear();
    this.stats = { hits: 0, misses: 0, evictions: 0 };
  }

  getStats() {
    const hitRate = this.stats.hits + this.stats.misses > 0
      ? (this.stats.hits / (this.stats.hits + this.stats.misses)) * 100
      : 0;

    return {
      ...this.stats,
      hitRate: hitRate.toFixed(2) + '%',
      size: this.cache.size,
      maxSize: this.maxSize,
    };
  }
}

// 全局缓存实例
const responseCache = new MemoryCache({
  maxSize: 2000,
  defaultTTL: 5 * 60 * 1000,
});

/**
 * 缓存中间件
 */
function cacheMiddleware(options = {}) {
  const {
    ttl = 5 * 60 * 1000,
    keyGenerator = null,
    condition = () => true,
    vary = [],
  } = options;

  return (req, res, next) => {
    // 只缓存 GET 请求
    if (req.method !== 'GET') {
      return next();
    }

    // 检查缓存条件
    if (!condition(req)) {
      return next();
    }

    const cacheKey = keyGenerator
      ? keyGenerator(req)
      : responseCache.generateKey(req);

    // 检查缓存
    const cached = responseCache.get(cacheKey);
    if (cached) {
      // 设置缓存命中头
      res.setHeader('X-Cache', 'HIT');
      res.setHeader('X-Cache-Key', cacheKey);
      return res.json(cached);
    }

    // 缓存原始 json 方法
    const originalJson = res.json.bind(res);

    // 重写 json 方法以缓存响应
    res.json = function(data) {
      // 只缓存成功响应
      if (res.statusCode >= 200 && res.statusCode < 300) {
        responseCache.set(cacheKey, data, ttl);
        res.setHeader('X-Cache', 'MISS');
        
        // 设置 Vary 头
        if (vary.length > 0) {
          res.setHeader('Vary', vary.join(', '));
        }
      }

      return originalJson(data);
    };

    next();
  };
}

/**
 * ETag 中间件
 */
function etagMiddleware(options = {}) {
  const { weak = true } = options;

  return (req, res, next) => {
    if (req.method !== 'GET' && req.method !== 'HEAD') {
      return next();
    }

    const originalJson = res.json.bind(res);
    const originalSend = res.send.bind(res);

    function generateETag(data) {
      const hash = crypto
        .createHash('md5')
        .update(JSON.stringify(data))
        .digest('hex');
      return weak ? `W/"${hash}"` : `"${hash}"`;
    }

    res.json = function(data) {
      const etag = generateETag(data);
      const ifNoneMatch = req.headers['if-none-match'];

      if (ifNoneMatch === etag) {
        res.status(304);
        return res.end();
      }

      res.setHeader('ETag', etag);
      return originalJson(data);
    };

    res.send = function(data) {
      if (typeof data === 'object') {
        const etag = generateETag(data);
        const ifNoneMatch = req.headers['if-none-match'];

        if (ifNoneMatch === etag) {
          res.status(304);
          return res.end();
        }

        res.setHeader('ETag', etag);
      }

      return originalSend(data);
    };

    next();
  };
}

/**
 * 压缩中间件配置
 */
function compressionConfig() {
  return {
    filter: (req, res) => {
      if (req.headers['x-no-compression']) {
        return false;
      }
      return true;
    },
    level: 6, // 压缩级别 (1-9)
    threshold: 1024, // 大于1KB才压缩
    memLevel: 8, // 内存使用级别
  };
}

/**
 * 速率限制配置
 */
function rateLimitConfig(options = {}) {
  const requests = new Map();
  const { windowMs = 15 * 60 * 1000, max = 100 } = options;

  return (req, res, next) => {
    const key = req.ip || req.connection.remoteAddress;
    const now = Date.now();

    if (!requests.has(key)) {
      requests.set(key, []);
    }

    const userRequests = requests.get(key);
    
    // 清理过期请求记录
    const validRequests = userRequests.filter(
      time => now - time < windowMs
    );

    if (validRequests.length >= max) {
      res.status(429).json({
        error: 'Too many requests',
        retryAfter: Math.ceil(windowMs / 1000),
      });
      return;
    }

    validRequests.push(now);
    requests.set(key, validRequests);

    // 设置限制头
    res.setHeader('X-RateLimit-Limit', max);
    res.setHeader('X-RateLimit-Remaining', max - validRequests.length);

    next();
  };
}

/**
 * 条件缓存控制
 */
function setCacheControl(options = {}) {
  const {
    public = true,
    maxAge = 0,
    sMaxAge = null,
    noCache = false,
    noStore = false,
    mustRevalidate = false,
    staleWhileRevalidate = null,
  } = options;

  return (req, res, next) => {
    const directives = [];

    if (noStore) {
      directives.push('no-store');
    } else {
      if (public) {
        directives.push('public');
      } else {
        directives.push('private');
      }

      if (maxAge > 0) {
        directives.push(`max-age=${maxAge}`);
      }

      if (sMaxAge !== null) {
        directives.push(`s-maxage=${sMaxAge}`);
      }

      if (noCache) {
        directives.push('no-cache');
      }

      if (mustRevalidate) {
        directives.push('must-revalidate');
      }

      if (staleWhileRevalidate !== null) {
        directives.push(`stale-while-revalidate=${staleWhileRevalidate}`);
      }
    }

    if (directives.length > 0) {
      res.setHeader('Cache-Control', directives.join(', '));
    }

    next();
  };
}

/**
 * 数据库查询优化中间件
 */
function queryOptimizer(req, res, next) {
  // 添加查询优化方法到请求对象
  req.optimizeQuery = function(query, options = {}) {
    const {
      select = null,
      populate = null,
      lean = true,
      limit = 100,
      timeout = 30000,
    } = options;

    let optimized = query;

    // 选择特定字段
    if (select) {
      optimized = optimized.select(select);
    }

    // 填充引用
    if (populate) {
      if (Array.isArray(populate)) {
        populate.forEach(p => {
          optimized = optimized.populate(p);
        });
      } else {
        optimized = optimized.populate(populate);
      }
    }

    // 使用 lean 模式
    if (lean) {
      optimized = optimized.lean();
    }

    // 限制返回数量
    if (limit) {
      optimized = optimized.limit(limit);
    }

    // 设置超时
    if (timeout) {
      optimized = optimized.maxTimeMS(timeout);
    }

    return optimized;
  };

  // 添加分页方法
  req.paginate = function(query, page = 1, pageSize = 20) {
    const skip = (page - 1) * pageSize;
    return query.skip(skip).limit(pageSize);
  };

  next();
}

module.exports = {
  MemoryCache,
  responseCache,
  cacheMiddleware,
  etagMiddleware,
  compressionConfig,
  rateLimitConfig,
  setCacheControl,
  queryOptimizer,
};
