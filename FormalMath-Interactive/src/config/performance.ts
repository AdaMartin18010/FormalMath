// @ts-nocheck
/**
 * 性能优化配置文件
 * 集中管理所有性能相关配置
 */

// 懒加载配置
export const lazyLoadConfig = {
  // 默认重试次数
  defaultRetry: 3,
  // 默认预加载延迟 (ms)
  defaultPreloadDelay: 2000,
  // 超时时间 (ms)
  timeout: 10000,
  // 重试退避基数 (ms)
  retryBaseDelay: 1000,
};

// 缓存配置
export const cacheConfig = {
  // API 缓存 TTL (ms)
  apiCacheTTL: 5 * 60 * 1000, // 5分钟
  // 会话缓存 TTL (ms)
  sessionCacheTTL: 30 * 60 * 1000, // 30分钟
  // 内存缓存 TTL (ms)
  memoryCacheTTL: 60 * 1000, // 1分钟
  // 最大缓存条目数
  maxCacheSize: 1000,
  // 清理间隔 (ms)
  cleanupInterval: 60 * 1000,
};

// 请求优化配置
export const requestConfig = {
  // 请求去重超时 (ms)
  dedupeTimeout: 30000,
  // 默认防抖延迟 (ms)
  debounceDelay: 300,
  // 智能重试配置
  retry: {
    maxRetries: 3,
    baseDelay: 1000,
    maxDelay: 30000,
  },
  // 批量请求配置
  batch: {
    delay: 50,
    maxSize: 100,
  },
  // 请求队列配置
  queue: {
    maxConcurrent: 6,
  },
};

// 虚拟列表配置
export const virtualListConfig = {
  // 默认项目高度 (px)
  defaultItemHeight: 50,
  // 默认过扫描数量
  defaultOverscan: 5,
  // 最小缓冲高度 (px)
  minBufferHeight: 200,
};

// 性能监控配置
export const monitoringConfig = {
  // 是否启用性能监控
  enabled: process.env.NODE_ENV === 'production',
  // 采样率 (0-1)
  sampleRate: 1.0,
  // 慢查询阈值 (ms)
  slowQueryThreshold: 100,
  // 慢渲染阈值 (ms)
  slowRenderThreshold: 16.67,
  // 长任务阈值 (ms)
  longTaskThreshold: 50,
  // 是否上报到分析服务
  reportToAnalytics: true,
};

// 资源加载配置
export const resourceConfig = {
  // 预加载延迟 (ms)
  preloadDelay: 2000,
  // 图片懒加载偏移 (px)
  lazyLoadOffset: 50,
  // 资源优先级映射
  priorities: {
    critical: ['high', 'high'],
    important: ['high', 'auto'],
    normal: ['auto', 'auto'],
    low: ['low', 'low'],
  },
};

// 动画性能配置
export const animationConfig = {
  // 是否启用 GPU 加速
  gpuAcceleration: true,
  // 默认过渡时长 (ms)
  defaultDuration: 300,
  // 减少动画偏好检测
  respectReducedMotion: true,
};

// 构建优化配置
export const buildConfig = {
  // 代码分割阈值 (bytes)
  chunkSizeWarningLimit: 1000,
  // 资源内联阈值 (bytes)
  assetsInlineLimit: 4096,
  // CSS 代码分割
  cssCodeSplit: true,
  // 源映射
  sourcemap: process.env.NODE_ENV !== 'production',
  // 压缩配置
  minify: {
    dropConsole: true,
    dropDebugger: true,
    passes: 2,
  },
};

// CDN 配置
export const cdnConfig = {
  // 是否启用 CDN
  enabled: process.env.NODE_ENV === 'production',
  // CDN 基础 URL
  baseUrl: process.env.VITE_CDN_URL || '',
  // 资源类型映射
  assetTypes: {
    js: '/js/',
    css: '/css/',
    images: '/images/',
    fonts: '/fonts/',
  },
};

// 服务端渲染配置 (未来使用)
export const ssrConfig = {
  enabled: false,
  // 预渲染路由
  prerenderRoutes: ['/'],
  // 排除路由
  excludeRoutes: ['/admin/*'],
};

// 性能预算配置
export const performanceBudget = {
  // JavaScript 预算
  javascript: {
    warning: 200 * 1024,  // 200KB
    error: 500 * 1024,    // 500KB
  },
  // CSS 预算
  css: {
    warning: 50 * 1024,   // 50KB
    error: 100 * 1024,    // 100KB
  },
  // 图片预算
  images: {
    warning: 500 * 1024,  // 500KB
    error: 1024 * 1024,   // 1MB
  },
  // 总资源预算
  total: {
    warning: 1024 * 1024, // 1MB
    error: 2 * 1024 * 1024, // 2MB
  },
  // Web Vitals 预算
  webVitals: {
    lcp: { good: 2500, poor: 4000 },
    fcp: { good: 1800, poor: 3000 },
    cls: { good: 0.1, poor: 0.25 },
    ttfb: { good: 600, poor: 1000 },
    fid: { good: 100, poor: 300 },
    tbt: { good: 200, poor: 500 },
  },
};

// 导出完整配置
export const performanceConfig = {
  lazyLoad: lazyLoadConfig,
  cache: cacheConfig,
  request: requestConfig,
  virtualList: virtualListConfig,
  monitoring: monitoringConfig,
  resource: resourceConfig,
  animation: animationConfig,
  build: buildConfig,
  cdn: cdnConfig,
  ssr: ssrConfig,
  budget: performanceBudget,
};

export default performanceConfig;
