// 性能优化工具导出
export {
  performanceMonitor,
  initPerformanceMonitoring,
  measureRenderTime,
  preloadResource,
  dnsPrefetch,
} from './performanceMonitor';

export { default as cache, createCache } from './cache';
export { 
  lazyLoad, 
  prefetchComponent, 
  preloadComponent,
  setupRoutePrefetch,
  useImageLazyLoad,
  dynamicImport,
  preloadResources,
} from './lazyLoad';

export {
  dedupeRequest,
  cachedRequest,
  smartRetry,
  debounceRequest,
  RequestBatcher,
  RequestQueue,
  optimisticUpdate,
  createOptimizedClient,
  optimizedClient,
} from './apiOptimizer';

// 节流函数
export function throttle<T extends (...args: unknown[]) => unknown>(
  fn: T,
  limit: number
): (...args: Parameters<T>) => ReturnType<T> {
  let inThrottle: boolean;
  return function (this: unknown, ...args: Parameters<T>): ReturnType<T> {
    if (!inThrottle) {
      inThrottle = true;
      setTimeout(() => (inThrottle = false), limit);
      return fn.apply(this, args) as ReturnType<T>;
    }
    return undefined as ReturnType<T>;
  };
}

// 防抖函数
export function debounce<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number,
  immediate = false
): (...args: Parameters<T>) => void {
  let timeoutId: ReturnType<typeof setTimeout> | null = null;
  
  return function (this: unknown, ...args: Parameters<T>): void {
    const callNow = immediate && !timeoutId;
    
    if (timeoutId) {
      clearTimeout(timeoutId);
    }
    
    timeoutId = setTimeout(() => {
      timeoutId = null;
      if (!immediate) {
        fn.apply(this, args);
      }
    }, delay);
    
    if (callNow) {
      fn.apply(this, args);
    }
  };
}

// RAF 节流
export function rafThrottle<T extends (...args: unknown[]) => unknown>(
  fn: T
): (...args: Parameters<T>) => void {
  let rafId: number | null = null;
  
  return function (this: unknown, ...args: Parameters<T>): void {
    if (rafId) {
      cancelAnimationFrame(rafId);
    }
    
    rafId = requestAnimationFrame(() => {
      rafId = null;
      fn.apply(this, args);
    });
  };
}

// 空闲回调调度
export function scheduleIdleCallback(
  callback: () => void,
  timeout = 2000
): void {
  if ('requestIdleCallback' in window) {
    window.requestIdleCallback(callback, { timeout });
  } else {
    setTimeout(callback, 1);
  }
}

// 批量处理
export function batchProcess<T>(
  items: T[],
  processor: (item: T) => void,
  batchSize = 10,
  delay = 0
): Promise<void> {
  return new Promise((resolve) => {
    let index = 0;
    
    function processBatch(): void {
      const batch = items.slice(index, index + batchSize);
      
      if (batch.length === 0) {
        resolve();
        return;
      }
      
      batch.forEach(processor);
      index += batchSize;
      
      if (delay > 0) {
        setTimeout(processBatch, delay);
      } else {
        requestAnimationFrame(processBatch);
      }
    }
    
    processBatch();
  });
}

// 虚拟列表计算
export interface VirtualListOptions {
  itemHeight: number;
  overscan?: number;
  containerHeight: number;
}

export interface VirtualListResult {
  startIndex: number;
  endIndex: number;
  offset: number;
}

export function calculateVirtualList(
  scrollTop: number,
  totalItems: number,
  options: VirtualListOptions
): VirtualListResult {
  const { itemHeight, overscan = 5, containerHeight } = options;
  
  const startIndex = Math.max(0, Math.floor(scrollTop / itemHeight) - overscan);
  const visibleCount = Math.ceil(containerHeight / itemHeight);
  const endIndex = Math.min(totalItems - 1, startIndex + visibleCount + overscan * 2);
  const offset = startIndex * itemHeight;
  
  return { startIndex, endIndex, offset };
}

// 内存使用监控
export function getMemoryUsage(): { used: number; total: number } | null {
  if ('memory' in performance) {
    const memory = (performance as any).memory;
    return {
      used: memory.usedJSHeapSize,
      total: memory.totalJSHeapSize,
    };
  }
  return null;
}

// 长任务监控
export function observeLongTasks(callback: (duration: number) => void): () => void {
  if (!('PerformanceObserver' in window)) {
    return () => {};
  }
  
  try {
    const observer = new PerformanceObserver((entries) => {
      for (const entry of entries.getEntries()) {
        if (entry.duration > 50) { // 超过50ms视为长任务
          callback(entry.duration);
        }
      }
    });
    
    observer.observe({ entryTypes: ['longtask'] });
    
    return () => observer.disconnect();
  } catch (e) {
    return () => {};
  }
}

// Web Worker 包装器
export class WorkerPool {
  private workers: Worker[] = [];
  private queue: Array<{
    id: string;
    data: unknown;
    resolve: (value: unknown) => void;
    reject: (reason: unknown) => void;
  }> = [];
  private taskMap = new Map<string, {
    resolve: (value: unknown) => void;
    reject: (reason: unknown) => void;
  }>();
  
  constructor(
    private workerScript: string,
    private poolSize = navigator.hardwareConcurrency || 4
  ) {
    this.init();
  }
  
  private init(): void {
    for (let i = 0; i < this.poolSize; i++) {
      const worker = new Worker(this.workerScript);
      worker.onmessage = (e) => this.handleMessage(e);
      worker.onerror = (e) => this.handleError(e);
      this.workers.push(worker);
    }
  }
  
  private handleMessage(e: MessageEvent): void {
    const { id, result, error } = e.data;
    const handlers = this.taskMap.get(id);
    
    if (handlers) {
      if (error) {
        handlers.reject(new Error(error));
      } else {
        handlers.resolve(result);
      }
      this.taskMap.delete(id);
    }
    
    this.processQueue();
  }
  
  private handleError(e: ErrorEvent): void {
    console.error('Worker error:', e);
  }
  
  private processQueue(): void {
    if (this.queue.length === 0) return;
    
    const availableWorker = this.workers.find(w => !this.isWorkerBusy(w));
    if (!availableWorker) return;
    
    const task = this.queue.shift();
    if (task) {
      this.taskMap.set(task.id, {
        resolve: task.resolve,
        reject: task.reject,
      });
      availableWorker.postMessage({ id: task.id, data: task.data });
    }
  }
  
  private isWorkerBusy(worker: Worker): boolean {
    // 简化实现，实际应该跟踪worker状态
    return false;
  }
  
  execute<T>(data: unknown): Promise<T> {
    return new Promise((resolve, reject) => {
      const id = Math.random().toString(36).substring(7);
      this.queue.push({
        id,
        data,
        resolve: resolve as (value: unknown) => void,
        reject,
      });
      this.processQueue();
    });
  }
  
  terminate(): void {
    this.workers.forEach(w => w.terminate());
    this.workers = [];
    this.queue = [];
    this.taskMap.forEach((handlers) => {
      handlers.reject(new Error('Worker pool terminated'));
    });
    this.taskMap.clear();
  }
}

// 资源加载优先级管理
export function setResourcePriority(
  element: HTMLImageElement | HTMLScriptElement | HTMLLinkElement,
  priority: 'high' | 'low' | 'auto'
): void {
  if ('fetchPriority' in element) {
    (element as any).fetchPriority = priority;
  }
}

// 首屏加载优化
export function optimizeFirstPaint(): void {
  // 延迟非关键资源
  const deferNonCritical = () => {
    // 延迟加载非关键图片
    document.querySelectorAll('img[data-src]').forEach((img) => {
      const image = img as HTMLImageElement;
      scheduleIdleCallback(() => {
        image.src = image.dataset.src!;
        image.removeAttribute('data-src');
      });
    });
    
    // 延迟加载非关键脚本
    document.querySelectorAll('script[data-src]').forEach((script) => {
      scheduleIdleCallback(() => {
        const newScript = document.createElement('script');
        newScript.src = script.getAttribute('data-src')!;
        document.body.appendChild(newScript);
        script.remove();
      });
    });
  };
  
  if (document.readyState === 'complete') {
    deferNonCritical();
  } else {
    window.addEventListener('load', deferNonCritical);
  }
}

// 性能标记
export function markPerformance(name: string): void {
  if ('performance' in window && 'mark' in performance) {
    performance.mark(name);
  }
}

export function measurePerformance(
  name: string,
  startMark: string,
  endMark: string
): void {
  if ('performance' in window && 'measure' in performance) {
    try {
      performance.measure(name, startMark, endMark);
    } catch (e) {
      console.warn(`Failed to measure ${name}:`, e);
    }
  }
}

// 导出所有性能工具
export default {
  throttle,
  debounce,
  rafThrottle,
  scheduleIdleCallback,
  batchProcess,
  calculateVirtualList,
  getMemoryUsage,
  observeLongTasks,
  setResourcePriority,
  optimizeFirstPaint,
  markPerformance,
  measurePerformance,
};
