/**
 * 数据库优化配置
 * MongoDB 性能优化设置
 */

const mongoose = require('mongoose');

// 数据库连接配置
const connectionOptions = {
  // 连接池配置
  maxPoolSize: 50,              // 最大连接数
  minPoolSize: 10,              // 最小连接数
  maxIdleTimeMS: 30000,         // 连接最大空闲时间
  waitQueueTimeoutMS: 5000,     // 等待连接超时时间
  serverSelectionTimeoutMS: 5000, // 服务器选择超时
  socketTimeoutMS: 45000,       // Socket超时时间
  
  // 重连配置
  retryWrites: true,
  retryReads: true,
  
  // 心跳检测
  heartbeatFrequencyMS: 10000,
  
  // 读取偏好
  readPreference: 'primaryPreferred',
  
  // 写入关注
  w: 'majority',
  wtimeoutMS: 5000,
  journal: true,
};

// 索引配置
const indexConfig = {
  // 笔记集合索引
  notes: [
    { key: { author: 1, createdAt: -1 }, name: 'author_created_idx' },
    { key: { title: 'text', content: 'text' }, name: 'text_search_idx' },
    { key: { tags: 1 }, name: 'tags_idx' },
    { key: { folder: 1 }, name: 'folder_idx' },
    { key: { isPinned: -1, updatedAt: -1 }, name: 'pinned_updated_idx' },
    { key: { 'shareSettings.isPublic': 1 }, name: 'public_share_idx' },
    { key: { 'shareSettings.shareLink': 1 }, name: 'share_link_idx', unique: true, sparse: true },
    { key: { type: 1, status: 1 }, name: 'type_status_idx' },
    { key: { author: 1, isFavorite: -1 }, name: 'author_favorite_idx' },
  ],
  
  // 标签集合索引
  tags: [
    { key: { user: 1, name: 1 }, name: 'user_name_idx', unique: true },
    { key: { user: 1, count: -1 }, name: 'user_count_idx' },
  ],
  
  // 文件夹集合索引
  folders: [
    { key: { user: 1, name: 1 }, name: 'user_name_idx' },
    { key: { user: 1, parent: 1 }, name: 'user_parent_idx' },
  ],
  
  // 版本历史索引
  versions: [
    { key: { note: 1, version: -1 }, name: 'note_version_idx' },
    { key: { createdBy: 1, createdAt: -1 }, name: 'creator_time_idx' },
  ],
  
  // 用户集合索引
  users: [
    { key: { email: 1 }, name: 'email_idx', unique: true, sparse: true },
    { key: { username: 1 }, name: 'username_idx', unique: true },
    { key: { 'preferences.language': 1 }, name: 'language_idx' },
  ],
  
  // 讨论主题索引
  topics: [
    { key: { category: 1, createdAt: -1 }, name: 'category_time_idx' },
    { key: { author: 1, createdAt: -1 }, name: 'author_time_idx' },
    { key: { isPinned: -1, createdAt: -1 }, name: 'pinned_time_idx' },
    { key: { views: -1 }, name: 'views_idx' },
    { key: { likes: -1 }, name: 'likes_idx' },
  ],
  
  // 问题集合索引
  questions: [
    { key: { status: 1, createdAt: -1 }, name: 'status_time_idx' },
    { key: { difficulty: 1 }, name: 'difficulty_idx' },
    { key: { conceptId: 1 }, name: 'concept_idx' },
    { key: { bounty: -1 }, name: 'bounty_idx' },
    { key: { votes: -1 }, name: 'votes_idx' },
  ],
  
  // 积分记录索引
  points: [
    { key: { userId: 1, createdAt: -1 }, name: 'user_time_idx' },
    { key: { userId: 1, type: 1 }, name: 'user_type_idx' },
    { key: { type: 1, createdAt: -1 }, name: 'type_time_idx' },
  ],
  
  // 通知索引
  notifications: [
    { key: { userId: 1, isRead: 1, createdAt: -1 }, name: 'user_read_time_idx' },
    { key: { userId: 1, type: 1 }, name: 'user_type_idx' },
  ],
};

// 创建索引
async function createIndexes(connection) {
  console.log('Creating database indexes...');
  
  for (const [collectionName, indexes] of Object.entries(indexConfig)) {
    try {
      const collection = connection.collection(collectionName);
      
      for (const index of indexes) {
        try {
          await collection.createIndex(index.key, {
            name: index.name,
            unique: index.unique || false,
            sparse: index.sparse || false,
            background: true, // 后台创建，不阻塞
          });
          console.log(`  ✓ Created index: ${collectionName}.${index.name}`);
        } catch (err) {
          if (err.code === 86) {
            console.log(`  ℹ Index ${index.name} already exists`);
          } else {
            console.error(`  ✗ Failed to create index ${index.name}:`, err.message);
          }
        }
      }
    } catch (err) {
      console.error(`  ✗ Failed to access collection ${collectionName}:`, err.message);
    }
  }
  
  console.log('Index creation completed');
}

// 数据库连接函数
async function connectDatabase(uri, options = {}) {
  try {
    const mergedOptions = { ...connectionOptions, ...options };
    
    const connection = await mongoose.connect(uri, mergedOptions);
    
    console.log('Database connected successfully');
    console.log(`  Host: ${connection.connection.host}`);
    console.log(`  Database: ${connection.connection.name}`);
    console.log(`  Port: ${connection.connection.port}`);
    
    // 创建索引
    await createIndexes(connection.connection);
    
    // 连接事件监听
    connection.connection.on('error', (err) => {
      console.error('Database connection error:', err);
    });
    
    connection.connection.on('disconnected', () => {
      console.warn('Database disconnected');
    });
    
    connection.connection.on('reconnected', () => {
      console.log('Database reconnected');
    });
    
    return connection;
  } catch (error) {
    console.error('Database connection failed:', error);
    throw error;
  }
}

// 查询优化器
class QueryOptimizer {
  constructor() {
    this.slowQueries = [];
    this.threshold = 100; // 慢查询阈值（毫秒）
  }
  
  // 优化查询选项
  static optimize(query, options = {}) {
    const {
      select = null,
      populate = null,
      lean = true,
      limit = null,
      skip = null,
      sort = null,
      maxTimeMS = 30000,
      hint = null,
    } = options;
    
    let optimized = query;
    
    // 选择字段
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
    
    // 使用 lean 模式（返回纯 JavaScript 对象）
    if (lean) {
      optimized = optimized.lean();
    }
    
    // 排序
    if (sort) {
      optimized = optimized.sort(sort);
    }
    
    // 分页
    if (skip) {
      optimized = optimized.skip(skip);
    }
    if (limit) {
      optimized = optimized.limit(limit);
    }
    
    // 最大执行时间
    if (maxTimeMS) {
      optimized = optimized.maxTimeMS(maxTimeMS);
    }
    
    // 使用指定索引
    if (hint) {
      optimized = optimized.hint(hint);
    }
    
    return optimized;
  }
  
  // 记录慢查询
  recordSlowQuery(collection, operation, duration, query = {}) {
    if (duration > this.threshold) {
      this.slowQueries.push({
        collection,
        operation,
        duration,
        query,
        timestamp: new Date(),
      });
      
      // 保持最近100条慢查询记录
      if (this.slowQueries.length > 100) {
        this.slowQueries.shift();
      }
      
      console.warn(`[Slow Query] ${collection}.${operation}: ${duration}ms`);
    }
  }
  
  // 获取慢查询统计
  getSlowQueryStats() {
    return {
      count: this.slowQueries.length,
      queries: this.slowQueries.slice(-20),
      byCollection: this.slowQueries.reduce((acc, q) => {
        acc[q.collection] = (acc[q.collection] || 0) + 1;
        return acc;
      }, {}),
    };
  }
  
  // 分析查询性能
  async analyzeQuery(collection, query, options = {}) {
    const start = Date.now();
    
    try {
      // 获取查询计划
      const explain = await collection.find(query).explain('executionStats');
      const duration = Date.now() - start;
      
      return {
        duration,
        indexUsed: explain.queryPlanner.winningPlan.inputStage?.indexName || 'COLLSCAN',
        docsExamined: explain.executionStats.totalDocsExamined,
        docsReturned: explain.executionStats.nReturned,
        executionTimeMillis: explain.executionStats.executionTimeMillis,
        stage: explain.queryPlanner.winningPlan.stage,
      };
    } catch (error) {
      return {
        error: error.message,
        duration: Date.now() - start,
      };
    }
  }
}

// 缓存策略
class DatabaseCache {
  constructor(options = {}) {
    this.cache = new Map();
    this.ttl = options.ttl || 5 * 60 * 1000; // 默认5分钟
    this.maxSize = options.maxSize || 1000;
  }
  
  get(key) {
    const entry = this.cache.get(key);
    if (!entry) return null;
    
    if (Date.now() > entry.expiresAt) {
      this.cache.delete(key);
      return null;
    }
    
    return entry.value;
  }
  
  set(key, value, ttl) {
    if (this.cache.size >= this.maxSize) {
      // LRU 淘汰
      const oldest = this.cache.entries().next().value;
      if (oldest) {
        this.cache.delete(oldest[0]);
      }
    }
    
    this.cache.set(key, {
      value,
      expiresAt: Date.now() + (ttl || this.ttl),
    });
  }
  
  delete(key) {
    return this.cache.delete(key);
  }
  
  clear() {
    this.cache.clear();
  }
  
  // 缓存包装器
  wrap(fn, keyGenerator, ttl) {
    return async (...args) => {
      const key = keyGenerator ? keyGenerator(...args) : JSON.stringify(args);
      
      const cached = this.get(key);
      if (cached !== null) {
        return cached;
      }
      
      const result = await fn(...args);
      this.set(key, result, ttl);
      return result;
    };
  }
  
  // 缓存失效模式
  invalidate(pattern) {
    for (const key of this.cache.keys()) {
      if (key.includes(pattern)) {
        this.cache.delete(key);
      }
    }
  }
}

module.exports = {
  connectionOptions,
  indexConfig,
  connectDatabase,
  createIndexes,
  QueryOptimizer,
  DatabaseCache,
};
