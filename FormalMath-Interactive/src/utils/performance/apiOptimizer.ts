/**
 * API 请求优化工具
 * 提供请求去重、合并、缓存等功能
 */

import { apiCache, sessionCache } from './cache';

interface RequestConfig {
  dedupe?: boolean;
  debounce?: number;
  cache?: boolean;
  cacheTtl?: number;
  retry?: number;
  retryDelay?: number;
}

interface PendingRequest {
  promise: Promise<unknown>;
  timestamp: number;
  abortController: AbortController;
}

// 待处理请求映射
const pendingRequests = new Map<string, PendingRequest>();

/**
 * 请求去重
 * 相同请求在pending期间只发送一次
 */
export function dedupeRequest<T>(
  key: string,
  requestFn: () => Promise<T>,
  timeout = 30000
): Promise<T> {
  // 检查是否有待处理的相同请求
  const pending = pendingRequests.get(key);
  
  if (pending) {
    // 检查是否超时
    if (Date.now() - pending.timestamp < timeout) {
      return pending.promise as Promise<T>;
    }
    // 超时取消旧请求
    pending.abortController.abort();
    pendingRequests.delete(key);
  }
  
  const abortController = new AbortController();
  
  const promise = requestFn().finally(() => {
    pendingRequests.delete(key);
  });
  
  pendingRequests.set(key, {
    promise,
    timestamp: Date.now(),
    abortController,
  });
  
  return promise;
}

/**
 * 带缓存的请求
 */
export async function cachedRequest<T>(
  key: string,
  requestFn: () => Promise<T>,
  ttl = 5 * 60 * 1000
): Promise<T> {
  const cached = apiCache.get<T>(key);
  
  if (cached !== undefined) {
    return cached;
  }
  
  const result = await requestFn();
  apiCache.set(key, result, ttl);
  return result;
}

/**
 * 请求合并器
 * 将短时间内的多个请求合并为一个批量请求
 */
export class RequestBatcher<T, R> {
  private items: T[] = [];
  private timeoutId: ReturnType<typeof setTimeout> | null = null;
  private resolvers: Array<(value: R) => void> = [];
  private rejecters: Array<(reason: unknown) => void> = [];
  
  constructor(
    private batchFn: (items: T[]) => Promise<R[]>,
    private delay = 50,
    private maxBatchSize = 100
  ) {}
  
  async add(item: T): Promise<R> {
    return new Promise((resolve, reject) => {
      this.items.push(item);
      this.resolvers.push(resolve);
      this.rejecters.push(reject);
      
      // 达到最大批量立即执行
      if (this.items.length >= this.maxBatchSize) {
        this.flush();
        return;
      }
      
      // 延迟执行
      if (this.timeoutId) {
        clearTimeout(this.timeoutId);
      }
      
      this.timeoutId = setTimeout(() => this.flush(), this.delay);
    });
  }
  
  private async flush(): Promise<void> {
    if (this.timeoutId) {
      clearTimeout(this.timeoutId);
      this.timeoutId = null;
    }
    
    if (this.items.length === 0) return;
    
    const currentItems = [...this.items];
    const currentResolvers = [...this.resolvers];
    const currentRejecters = [...this.rejecters];
    
    this.items = [];
    this.resolvers = [];
    this.rejecters = [];
    
    try {
      const results = await this.batchFn(currentItems);
      
      results.forEach((result, index) => {
        if (currentResolvers[index]) {
          currentResolvers[index](result);
        }
      });
    } catch (error) {
      currentRejecters.forEach(reject => reject(error));
    }
  }
  
  destroy(): void {
    if (this.timeoutId) {
      clearTimeout(this.timeoutId);
    }
    this.rejecters.forEach(reject => 
      reject(new Error('RequestBatcher destroyed'))
    );
    this.items = [];
    this.resolvers = [];
    this.rejecters = [];
  }
}

/**
 * 智能重试
 */
export async function smartRetry<T>(
  fn: () => Promise<T>,
  options: {
    maxRetries?: number;
    baseDelay?: number;
    maxDelay?: number;
    retryableErrors?: (error: Error) => boolean;
  } = {}
): Promise<T> {
  const {
    maxRetries = 3,
    baseDelay = 1000,
    maxDelay = 30000,
    retryableErrors = () => true,
  } = options;
  
  let lastError: Error | null = null;
  
  for (let attempt = 0; attempt <= maxRetries; attempt++) {
    try {
      return await fn();
    } catch (error) {
      lastError = error as Error;
      
      if (attempt === maxRetries || !retryableErrors(lastError)) {
        throw lastError;
      }
      
      // 指数退避 + 抖动
      const delay = Math.min(
        baseDelay * Math.pow(2, attempt) + Math.random() * 1000,
        maxDelay
      );
      
      await new Promise(resolve => setTimeout(resolve, delay));
    }
  }
  
  throw lastError;
}

/**
 * 防抖请求
 */
export function debounceRequest<T, Args extends unknown[]>(
  fn: (...args: Args) => Promise<T>,
  delay = 300
): (...args: Args) => Promise<T> {
  let timeoutId: ReturnType<typeof setTimeout> | null = null;
  let resolve: ((value: T) => void) | null = null;
  let reject: ((reason: unknown) => void) | null = null;
  let pendingArgs: Args | null = null;
  
  return (...args: Args): Promise<T> => {
    pendingArgs = args;
    
    return new Promise((res, rej) => {
      resolve = res;
      reject = rej;
      
      if (timeoutId) {
        clearTimeout(timeoutId);
      }
      
      timeoutId = setTimeout(async () => {
        try {
          const result = await fn(...pendingArgs!);
          resolve?.(result);
        } catch (error) {
          reject?.(error);
        } finally {
          timeoutId = null;
          pendingArgs = null;
        }
      }, delay);
    });
  };
}

/**
 * 请求优先级队列
 */
export class RequestQueue {
  private queue: Array<{
    id: string;
    fn: () => Promise<unknown>;
    priority: number;
    resolve: (value: unknown) => void;
    reject: (reason: unknown) => void;
  }> = [];
  private running = 0;
  private maxConcurrent: number;
  
  constructor(maxConcurrent = 6) {
    this.maxConcurrent = maxConcurrent;
  }
  
  async add<T>(
    id: string,
    fn: () => Promise<T>,
    priority = 0
  ): Promise<T> {
    return new Promise((resolve, reject) => {
      // 检查是否已存在相同id的请求
      const existingIndex = this.queue.findIndex(item => item.id === id);
      if (existingIndex !== -1) {
        // 移除旧请求
        const oldItem = this.queue[existingIndex];
        oldItem.reject(new Error('Request replaced by newer request'));
        this.queue.splice(existingIndex, 1);
      }
      
      this.queue.push({
        id,
        fn: fn as () => Promise<unknown>,
        priority,
        resolve: resolve as (value: unknown) => void,
        reject,
      });
      
      // 按优先级排序
      this.queue.sort((a, b) => b.priority - a.priority);
      
      this.process();
    });
  }
  
  private async process(): Promise<void> {
    if (this.running >= this.maxConcurrent || this.queue.length === 0) {
      return;
    }
    
    this.running++;
    const item = this.queue.shift();
    
    if (item) {
      try {
        const result = await item.fn();
        item.resolve(result);
      } catch (error) {
        item.reject(error);
      } finally {
        this.running--;
        this.process();
      }
    }
  }
  
  clear(): void {
    this.queue.forEach(item => {
      item.reject(new Error('Queue cleared'));
    });
    this.queue = [];
  }
  
  get size(): number {
    return this.queue.length;
  }
  
  get isBusy(): boolean {
    return this.running >= this.maxConcurrent;
  }
}

/**
 * 乐观更新
 */
export function optimisticUpdate<T>(
  currentValue: T,
  updateFn: (value: T) => T,
  serverUpdate: () => Promise<T>,
  onError?: (error: Error, originalValue: T) => void
): Promise<T> {
  return new Promise((resolve, reject) => {
    const originalValue = currentValue;
    const optimisticValue = updateFn(currentValue);
    
    resolve(optimisticValue);
    
    serverUpdate().catch((error) => {
      onError?.(error as Error, originalValue);
      reject(error);
    });
  });
}

/**
 * 创建优化的 API 客户端
 */
export function createOptimizedClient(baseConfig: RequestConfig = {}) {
  const queue = new RequestQueue();
  
  return {
    request: async <T>(
      key: string,
      requestFn: () => Promise<T>,
      config: RequestConfig = {}
    ): Promise<T> => {
      const mergedConfig = { ...baseConfig, ...config };
      
      let operation = requestFn;
      
      // 应用缓存
      if (mergedConfig.cache) {
        const cachedOperation = operation;
        operation = () => cachedRequest(
          key,
          cachedOperation,
          mergedConfig.cacheTtl
        );
      }
      
      // 应用去重
      if (mergedConfig.dedupe !== false) {
        const dedupedOperation = operation;
        operation = () => dedupeRequest(key, dedupedOperation);
      }
      
      // 应用队列
      return queue.add(key, operation, 0) as Promise<T>;
    },
    
    destroy: () => {
      queue.clear();
    },
  };
}

// 全局优化客户端实例
export const optimizedClient = createOptimizedClient({
  dedupe: true,
  cache: true,
  cacheTtl: 5 * 60 * 1000,
});

export default {
  dedupeRequest,
  cachedRequest,
  smartRetry,
  debounceRequest,
  RequestBatcher,
  RequestQueue,
  createOptimizedClient,
  optimizedClient,
};
