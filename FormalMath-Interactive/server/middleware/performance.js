/**
 * 性能监控和优化中间件
 */

const os = require('os');

// 请求计时中间件
function requestTimer(req, res, next) {
  const start = process.hrtime();
  const startMemory = process.memoryUsage();

  // 监听响应完成
  res.on('finish', () => {
    const diff = process.hrtime(start);
    const duration = diff[0] * 1000 + diff[1] / 1e6; // 转换为毫秒
    
    const endMemory = process.memoryUsage();
    const memoryDiff = {
      rss: (endMemory.rss - startMemory.rss) / 1024 / 1024, // MB
      heapUsed: (endMemory.heapUsed - startMemory.heapUsed) / 1024 / 1024, // MB
    };

    // 记录慢请求
    if (duration > 1000) {
      console.warn(`[Slow Request] ${req.method} ${req.originalUrl} - ${duration.toFixed(2)}ms`);
    }

    // 设置性能头
    res.setHeader('X-Response-Time', `${duration.toFixed(2)}ms`);
    
    // 记录请求日志
    if (process.env.NODE_ENV === 'development') {
      console.log(
        `[${new Date().toISOString()}] ${req.method} ${req.originalUrl} - ` +
        `${res.statusCode} - ${duration.toFixed(2)}ms - ` +
        `Memory: +${memoryDiff.heapUsed.toFixed(2)}MB`
      );
    }
  });

  next();
}

// 性能指标收集
class PerformanceMetrics {
  constructor() {
    this.metrics = {
      requests: 0,
      totalDuration: 0,
      errors: 0,
      byRoute: new Map(),
      byStatus: new Map(),
    };
    this.startTime = Date.now();
  }

  record(req, res, duration) {
    this.metrics.requests++;
    this.metrics.totalDuration += duration;

    // 按路由统计
    const route = `${req.method} ${req.route?.path || req.originalUrl}`;
    if (!this.metrics.byRoute.has(route)) {
      this.metrics.byRoute.set(route, {
        count: 0,
        totalDuration: 0,
        errors: 0,
      });
    }
    const routeMetrics = this.metrics.byRoute.get(route);
    routeMetrics.count++;
    routeMetrics.totalDuration += duration;
    if (res.statusCode >= 400) {
      routeMetrics.errors++;
      this.metrics.errors++;
    }

    // 按状态码统计
    const status = res.statusCode.toString();
    this.metrics.byStatus.set(
      status,
      (this.metrics.byStatus.get(status) || 0) + 1
    );
  }

  getStats() {
    const uptime = Date.now() - this.startTime;
    const avgDuration = this.metrics.requests > 0
      ? this.metrics.totalDuration / this.metrics.requests
      : 0;

    return {
      uptime: uptime,
      requests: this.metrics.requests,
      avgDuration: avgDuration.toFixed(2) + 'ms',
      rps: ((this.metrics.requests / uptime) * 1000).toFixed(2),
      errorRate: this.metrics.requests > 0
        ? ((this.metrics.errors / this.metrics.requests) * 100).toFixed(2) + '%'
        : '0%',
      byRoute: Object.fromEntries(this.metrics.byRoute),
      byStatus: Object.fromEntries(this.metrics.byStatus),
    };
  }
}

const metrics = new PerformanceMetrics();

// 性能统计中间件
function performanceStats(req, res, next) {
  const start = process.hrtime();

  res.on('finish', () => {
    const diff = process.hrtime(start);
    const duration = diff[0] * 1000 + diff[1] / 1e6;
    metrics.record(req, res, duration);
  });

  next();
}

// 健康检查中间件
function healthCheck(req, res) {
  const systemInfo = {
    status: 'ok',
    timestamp: new Date().toISOString(),
    uptime: process.uptime(),
    memory: process.memoryUsage(),
    cpu: process.cpuUsage(),
    system: {
      platform: os.platform(),
      arch: os.arch(),
      cpus: os.cpus().length,
      totalMemory: (os.totalmem() / 1024 / 1024 / 1024).toFixed(2) + 'GB',
      freeMemory: (os.freemem() / 1024 / 1024 / 1024).toFixed(2) + 'GB',
      loadAverage: os.loadavg(),
    },
    performance: metrics.getStats(),
  };

  res.json(systemInfo);
}

// 数据库连接池监控
function poolMonitor(pool) {
  return (req, res, next) => {
    req.dbPool = {
      size: pool.size,
      available: pool.available,
      pending: pool.pending,
    };
    next();
  };
}

// 响应优化中间件
function responseOptimizer(req, res, next) {
  // 移除不必要的头
  res.removeHeader('X-Powered-By');

  // 添加安全头
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('X-XSS-Protection', '1; mode=block');

  // 启用 Keep-Alive
  res.setHeader('Connection', 'keep-alive');

  next();
}

// 请求大小限制中间件
function requestSizeLimit(options = {}) {
  const { maxSize = 10 * 1024 * 1024 } = options; // 默认10MB

  return (req, res, next) => {
    const contentLength = parseInt(req.headers['content-length'] || '0', 10);

    if (contentLength > maxSize) {
      res.status(413).json({
        error: 'Payload too large',
        maxSize: maxSize,
        received: contentLength,
      });
      return;
    }

    next();
  };
}

// 连接池管理
class ConnectionPool {
  constructor(options = {}) {
    this.min = options.min || 2;
    this.max = options.max || 10;
    this.connections = [];
    this.waiting = [];
    this.stats = {
      created: 0,
      acquired: 0,
      released: 0,
      destroyed: 0,
    };
  }

  async acquire() {
    const available = this.connections.find(c => !c.inUse);
    
    if (available) {
      available.inUse = true;
      this.stats.acquired++;
      return available.connection;
    }

    if (this.connections.length < this.max) {
      const connection = await this.createConnection();
      this.connections.push({
        connection,
        inUse: true,
        createdAt: Date.now(),
      });
      this.stats.acquired++;
      return connection;
    }

    // 等待可用连接
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        reject(new Error('Connection pool timeout'));
      }, 30000);

      this.waiting.push({
        resolve: (conn) => {
          clearTimeout(timeout);
          resolve(conn);
        },
        reject: (err) => {
          clearTimeout(timeout);
          reject(err);
        },
      });
    });
  }

  release(connection) {
    const poolEntry = this.connections.find(c => c.connection === connection);
    
    if (poolEntry) {
      poolEntry.inUse = false;
      this.stats.released++;

      // 检查等待队列
      if (this.waiting.length > 0) {
        const waiter = this.waiting.shift();
        poolEntry.inUse = true;
        this.stats.acquired++;
        waiter.resolve(connection);
      }
    }
  }

  async createConnection() {
    this.stats.created++;
    // 子类实现
    return null;
  }

  getStats() {
    return {
      total: this.connections.length,
      inUse: this.connections.filter(c => c.inUse).length,
      available: this.connections.filter(c => !c.inUse).length,
      waiting: this.waiting.length,
      ...this.stats,
    };
  }
}

// 导出
module.exports = {
  requestTimer,
  performanceStats,
  healthCheck,
  poolMonitor,
  responseOptimizer,
  requestSizeLimit,
  ConnectionPool,
  metrics,
  PerformanceMetrics,
};
