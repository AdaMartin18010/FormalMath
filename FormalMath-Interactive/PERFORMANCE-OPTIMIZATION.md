# FormalMath Interactive - 性能优化指南

## 目录
1. [优化概述](#优化概述)
2. [前端加载性能](#前端加载性能)
3. [API响应时间优化](#api响应时间优化)
4. [数据库查询优化](#数据库查询优化)
5. [静态资源优化](#静态资源优化)
6. [性能监控](#性能监控)
7. [性能测试](#性能测试)

---

## 优化概述

本次性能优化涵盖了系统的各个层面，目标是实现：
- **LCP < 2.5s** (Largest Contentful Paint)
- **FCP < 1.8s** (First Contentful Paint)
- **CLS < 0.1** (Cumulative Layout Shift)
- **TTFB < 600ms** (Time to First Byte)
- **API响应 < 200ms** (p95)

---

## 前端加载性能

### 1. 代码分割优化

Vite 配置已优化为更细粒度的代码分割：

```typescript
// vite.config.ts
manualChunks: {
  'vendor-core': ['react', 'react-dom'],
  'vendor-router': ['react-router-dom', 'react-helmet-async'],
  'vendor-state': ['zustand', 'react-query'],
  'vendor-d3': ['d3', 'd3-selection', 'd3-scale', 'd3-hierarchy', 'd3-force-3d'],
  'vendor-three': ['three', '@react-three/fiber', '@react-three/drei'],
  'vendor-mermaid': ['mermaid'],
  'vendor-utils': ['axios', 'clsx', 'tailwind-merge'],
  'vendor-markdown': ['react-markdown', 'rehype-katex', 'remark-math'],
  'vendor-icons': ['lucide-react'],
}
```

### 2. 懒加载策略

使用增强的懒加载工具：

```typescript
import { lazyLoad, preloadComponent } from '@utils/performance';

// 智能懒加载（支持预加载和重试）
const KnowledgeGraph = lazyLoad(
  () => import('@pages/KnowledgeGraph'),
  { preload: true, retry: 3 }
);

// 延迟预加载
const preloadAnalytics = preloadComponent(
  () => import('@pages/Analytics'),
  5000  // 5秒后预加载
);
```

### 3. 资源预加载

```typescript
import { preloadResources } from '@utils/performance';

// 预加载关键资源
preloadResources([
  { href: '/assets/fonts/main.woff2', as: 'font', type: 'font/woff2' },
  { href: '/assets/images/hero.webp', as: 'image' },
]);
```

### 4. 图片懒加载

```typescript
import { useImageLazyLoad } from '@utils/performance';

function OptimizedImage({ src, alt }) {
  const { ref, src: lazySrc, isLoaded, handleLoad } = useImageLazyLoad(src);
  
  return (
    <img
      ref={ref}
      src={lazySrc}
      alt={alt}
      onLoad={handleLoad}
      className={isLoaded ? 'loaded' : 'loading'}
    />
  );
}
```

---

## API响应时间优化

### 1. 请求去重

```typescript
import { dedupeRequest, cachedRequest } from '@utils/performance';

// 自动去重相同请求
const data = await dedupeRequest(
  `api/users/${id}`,
  () => fetchUser(id)
);

// 带缓存的请求
const cached = await cachedRequest(
  `api/config`,
  () => fetchConfig(),
  10 * 60 * 1000  // 10分钟缓存
);
```

### 2. 请求合并

```typescript
import { RequestBatcher } from '@utils/performance';

// 批量请求处理
const batcher = new RequestBatcher(
  async (ids) => {
    // 发送批量请求
    const response = await fetch('/api/batch', {
      method: 'POST',
      body: JSON.stringify({ ids }),
    });
    return response.json();
  },
  50,   // 50ms 延迟
  100   // 最大100个/批
);

// 使用
const result = await batcher.add(itemId);
```

### 3. 智能重试

```typescript
import { smartRetry } from '@utils/performance';

const result = await smartRetry(
  () => fetchCriticalData(),
  {
    maxRetries: 3,
    baseDelay: 1000,
    retryableErrors: (error) => error.status >= 500,
  }
);
```

### 4. 乐观更新

```typescript
import { optimisticUpdate } from '@utils/performance';

// 乐观更新 UI
const newState = await optimisticUpdate(
  currentState,
  (state) => applyOptimisticChange(state, change),
  () => submitChangeToServer(change),
  (error, original) => {
    // 错误回滚
    rollbackTo(original);
  }
);
```

---

## 数据库查询优化

### 1. 索引配置

已配置的索引列表（位于 `server/config/database.js`）：

| 集合 | 索引 | 用途 |
|------|------|------|
| notes | author + createdAt | 用户笔记列表查询 |
| notes | title + content (text) | 全文搜索 |
| notes | tags | 标签筛选 |
| notes | shareSettings.shareLink | 分享链接查询 |
| tags | user + name | 用户标签唯一性 |
| topics | category + createdAt | 分类排序 |

### 2. 查询优化

```javascript
const { QueryOptimizer } = require('./server/config/database');

// 优化查询
const query = QueryOptimizer.optimize(
  Note.find({ author: userId }),
  {
    select: 'title content updatedAt',
    populate: { path: 'tags', select: 'name color' },
    lean: true,
    limit: 20,
    sort: { updatedAt: -1 },
  }
);
```

### 3. 连接池配置

```javascript
const connectionOptions = {
  maxPoolSize: 50,
  minPoolSize: 10,
  maxIdleTimeMS: 30000,
  waitQueueTimeoutMS: 5000,
};
```

### 4. 数据库缓存

```javascript
const { DatabaseCache } = require('./server/config/database');

const cache = new DatabaseCache({ ttl: 5 * 60 * 1000 });

// 缓存包装器
const getUserStats = cache.wrap(
  async (userId) => {
    return await calculateUserStats(userId);
  },
  (userId) => `user:stats:${userId}`
);
```

---

## 静态资源优化

### 1. 构建优化

```typescript
// vite.config.ts
build: {
  minify: 'terser',
  terserOptions: {
    compress: {
      drop_console: true,
      drop_debugger: true,
      pure_funcs: ['console.log', 'console.info'],
      passes: 2,
    },
  },
  assetsInlineLimit: 4096,
  cssCodeSplit: true,
  reportCompressedSize: true,
}
```

### 2. 压缩中间件配置

```javascript
const { compressionConfig } = require('./server/middleware/cache');

app.use(require('compression')(compressionConfig()));
```

### 3. CDN 配置建议

在 `vite.config.ts` 中配置 CDN：

```typescript
experimental: {
  renderBuiltUrl(filename, { hostType }) {
    // 生产环境使用 CDN
    if (process.env.NODE_ENV === 'production') {
      return {
        js: `https://cdn.example.com/js/${filename}`,
        css: `https://cdn.example.com/css/${filename}`,
      }[hostType];
    }
    return { relative: true };
  },
}
```

### 4. Service Worker 缓存策略

```typescript
// vite.config.ts - PWA 配置
workbox: {
  runtimeCaching: [
    {
      urlPattern: /\.(?:png|jpg|jpeg|svg|gif|webp)$/i,
      handler: 'CacheFirst',
      options: {
        cacheName: 'images-cache',
        expiration: {
          maxEntries: 100,
          maxAgeSeconds: 60 * 60 * 24 * 30, // 30天
        },
      },
    },
  ],
}
```

---

## 性能监控

### 1. Web Vitals 监控

```typescript
import { initPerformanceMonitoring } from '@utils/performance';

// 自动监控 Core Web Vitals
initPerformanceMonitoring();
```

### 2. 性能指标获取

```typescript
import { performanceMonitor } from '@utils/performance';

// 获取当前指标
const metrics = performanceMonitor.getMetrics();
console.log(`LCP: ${metrics.lcp}ms`);
console.log(`FCP: ${metrics.fcp}ms`);
console.log(`CLS: ${metrics.cls}`);

// 订阅性能事件
const unsubscribe = performanceMonitor.on('lcp', (data) => {
  if (data.value > 2500) {
    analytics.track('Slow LCP', { value: data.value });
  }
});
```

### 3. 长任务监控

```typescript
import { observeLongTasks } from '@utils/performance';

const cleanup = observeLongTasks((duration) => {
  console.warn(`Long task detected: ${duration}ms`);
});

// 清理
cleanup();
```

### 4. 服务器端监控

```javascript
const { requestTimer, healthCheck } = require('./server/middleware/performance');

// 请求计时
app.use(requestTimer);

// 健康检查端点
app.get('/health', healthCheck);
```

---

## 性能测试

### 1. 运行 Lighthouse 审计

```bash
# 安装依赖
npm install --save-dev lighthouse chrome-launcher puppeteer

# 运行 Lighthouse 审计
node scripts/lighthouse-audit.js
```

### 2. 运行性能测试

```bash
# 运行性能测试
node scripts/performance-test.js
```

### 3. 构建分析

```bash
# 分析构建产物
npm run build -- --analyze
```

---

## 优化检查清单

### 前端优化
- [ ] 代码分割配置生效
- [ ] 懒加载策略实施
- [ ] 关键资源预加载
- [ ] 图片懒加载
- [ ] 字体加载优化

### API优化
- [ ] 请求去重启用
- [ ] 响应缓存配置
- [ ] 压缩中间件启用
- [ ] ETag 支持

### 数据库优化
- [ ] 索引创建完成
- [ ] 查询优化器使用
- [ ] 连接池配置
- [ ] 慢查询监控

### 部署优化
- [ ] CDN 配置
- [ ] Gzip/Brotli 压缩
- [ ] HTTP/2 启用
- [ ] 静态资源缓存头

---

## 性能预算

| 指标 | 目标 | 警告阈值 | 错误阈值 |
|------|------|----------|----------|
| LCP | < 2.5s | 2.5s - 4s | > 4s |
| FCP | < 1.8s | 1.8s - 3s | > 3s |
| CLS | < 0.1 | 0.1 - 0.25 | > 0.25 |
| TTFB | < 600ms | 600ms - 1s | > 1s |
| TBT | < 200ms | 200ms - 500ms | > 500ms |
| Bundle Size | < 200KB | 200KB - 500KB | > 500KB |

---

## 后续优化建议

1. **SSR 考虑**: 对首屏关键页面实施服务端渲染
2. **边缘缓存**: 使用 CloudFlare 或 AWS CloudFront 缓存
3. **图像优化**: 实施响应式图片和 AVIF 格式
4. **预渲染**: 对静态页面进行预渲染
5. **Web Workers**: 将复杂计算移至 Web Workers
