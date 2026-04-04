// 性能优化工具导出
export {
  performanceMonitor,
  initPerformanceMonitoring,
  measureRenderTime,
  preloadResource,
  dnsPrefetch,
} from './performanceMonitor';

export { default as cache, createCache } from './cache';
export { lazyLoad, prefetchComponent, preloadComponent } from './lazyLoad';

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
