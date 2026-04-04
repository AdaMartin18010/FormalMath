/**
 * 性能优化 Hook
 * 提供渲染优化、内存管理和性能监控功能
 */

import { useCallback, useEffect, useMemo, useRef, useState } from 'react';

// ============================================
// 类型定义
// ============================================

interface PerformanceMetrics {
  fps: number;
  memory: number;
  renderTime: number;
  nodeCount: number;
}

interface ThrottleOptions {
  leading?: boolean;
  trailing?: boolean;
}

interface DebounceOptions {
  leading?: boolean;
  maxWait?: number;
}

// ============================================
// FPS 监控
// ============================================

export function useFPSMonitor(enabled: boolean = true): number {
  const [fps, setFps] = useState(60);
  const frameCount = useRef(0);
  const lastTime = useRef(performance.now());
  const rafId = useRef<number>();

  useEffect(() => {
    if (!enabled) return;

    const measureFPS = () => {
      frameCount.current++;
      const currentTime = performance.now();
      const delta = currentTime - lastTime.current;

      if (delta >= 1000) {
        setFps(Math.round((frameCount.current * 1000) / delta));
        frameCount.current = 0;
        lastTime.current = currentTime;
      }

      rafId.current = requestAnimationFrame(measureFPS);
    };

    rafId.current = requestAnimationFrame(measureFPS);

    return () => {
      if (rafId.current) {
        cancelAnimationFrame(rafId.current);
      }
    };
  }, [enabled]);

  return fps;
}

// ============================================
// 渲染节流
// ============================================

export function useThrottle<T extends (...args: any[]) => any>(
  callback: T,
  delay: number,
  options: ThrottleOptions = {}
): T {
  const { leading = true, trailing = true } = options;
  const timeoutRef = useRef<NodeJS.Timeout | null>(null);
  const lastArgsRef = useRef<Parameters<T> | null>(null);
  const lastCallTimeRef = useRef<number>(0);

  const throttled = useCallback(
    (...args: Parameters<T>) => {
      const now = Date.now();
      const remaining = delay - (now - lastCallTimeRef.current);

      lastArgsRef.current = args;

      if (remaining <= 0) {
        if (timeoutRef.current) {
          clearTimeout(timeoutRef.current);
          timeoutRef.current = null;
        }
        if (leading) {
          lastCallTimeRef.current = now;
          callback(...args);
        }
      } else if (!timeoutRef.current && trailing) {
        timeoutRef.current = setTimeout(() => {
          lastCallTimeRef.current = leading ? Date.now() : 0;
          timeoutRef.current = null;
          if (lastArgsRef.current) {
            callback(...lastArgsRef.current);
          }
        }, remaining);
      }
    },
    [callback, delay, leading, trailing]
  );

  useEffect(() => {
    return () => {
      if (timeoutRef.current) {
        clearTimeout(timeoutRef.current);
      }
    };
  }, []);

  return throttled as T;
}

// ============================================
// 防抖
// ============================================

export function useDebounce<T extends (...args: any[]) => any>(
  callback: T,
  delay: number,
  options: DebounceOptions = {}
): T {
  const { leading = false, maxWait } = options;
  const timeoutRef = useRef<NodeJS.Timeout | null>(null);
  const maxTimeoutRef = useRef<NodeJS.Timeout | null>(null);
  const lastCallTimeRef = useRef<number>(0);

  const debounced = useCallback(
    (...args: Parameters<T>) => {
      const now = Date.now();

      const invoke = () => {
        lastCallTimeRef.current = now;
        callback(...args);
      };

      if (timeoutRef.current) {
        clearTimeout(timeoutRef.current);
      }

      if (leading && !lastCallTimeRef.current) {
        invoke();
      } else {
        timeoutRef.current = setTimeout(invoke, delay);
      }

      if (maxWait && !maxTimeoutRef.current) {
        maxTimeoutRef.current = setTimeout(() => {
          if (timeoutRef.current) {
            clearTimeout(timeoutRef.current);
            timeoutRef.current = null;
          }
          maxTimeoutRef.current = null;
          invoke();
        }, maxWait);
      }
    },
    [callback, delay, leading, maxWait]
  );

  useEffect(() => {
    return () => {
      if (timeoutRef.current) clearTimeout(timeoutRef.current);
      if (maxTimeoutRef.current) clearTimeout(maxTimeoutRef.current);
    };
  }, []);

  return debounced as T;
}

// ============================================
// RAF 节流 (用于动画)
// ============================================

export function useRAFThrottle<T extends (...args: any[]) => any>(callback: T): T {
  const rafId = useRef<number | null>(null);
  const pendingArgs = useRef<Parameters<T> | null>(null);

  const throttled = useCallback(
    (...args: Parameters<T>) => {
      pendingArgs.current = args;

      if (rafId.current === null) {
        rafId.current = requestAnimationFrame(() => {
          if (pendingArgs.current) {
            callback(...pendingArgs.current);
          }
          rafId.current = null;
          pendingArgs.current = null;
        });
      }
    },
    [callback]
  );

  useEffect(() => {
    return () => {
      if (rafId.current !== null) {
        cancelAnimationFrame(rafId.current);
      }
    };
  }, []);

  return throttled as T;
}

// ============================================
// 内存管理
// ============================================

export function useMemoryOptimizer<T>(
  data: T[],
  maxItems: number = 1000
): T[] {
  const cacheRef = useRef<Map<string, T>>(new Map());

  return useMemo(() => {
    // 如果数据量超过限制，清理旧数据
    if (data.length > maxItems) {
      const keysToKeep = new Set(
        data.slice(-maxItems).map((item: any) => item.id || JSON.stringify(item))
      );

      // 清理缓存
      for (const key of cacheRef.current.keys()) {
        if (!keysToKeep.has(key)) {
          cacheRef.current.delete(key);
        }
      }

      return data.slice(-maxItems);
    }
    return data;
  }, [data, maxItems]);
}

// ============================================
// 性能监控
// ============================================

export function usePerformanceMonitor(
  componentName: string,
  enabled: boolean = false
): PerformanceMetrics | null {
  const [metrics, setMetrics] = useState<PerformanceMetrics | null>(null);
  const renderStartTime = useRef<number>(0);

  useEffect(() => {
    if (!enabled) return;

    renderStartTime.current = performance.now();

    return () => {
      const renderTime = performance.now() - renderStartTime.current;
      
      // 获取内存信息（如果可用）
      const memory = (performance as any).memory?.usedJSHeapSize || 0;

      setMetrics({
        fps: 60, // 简化处理
        memory,
        renderTime,
        nodeCount: document.querySelectorAll('*').length,
      });

      if (process.env.NODE_ENV === 'development') {
        console.log(`[Performance] ${componentName}:`, {
          renderTime: `${renderTime.toFixed(2)}ms`,
          memory: `${(memory / 1024 / 1024).toFixed(2)}MB`,
        });
      }
    };
  }, [componentName, enabled]);

  return metrics;
}

// ============================================
// 批量更新
// ============================================

export function useBatchedUpdates<T>(
  items: T[],
  batchSize: number = 50,
  delay: number = 16
): T[] {
  const [displayedItems, setDisplayedItems] = useState<T[]>([]);
  const indexRef = useRef(0);

  useEffect(() => {
    indexRef.current = 0;
    setDisplayedItems([]);

    const loadBatch = () => {
      const nextIndex = Math.min(indexRef.current + batchSize, items.length);
      const batch = items.slice(indexRef.current, nextIndex);
      
      setDisplayedItems(prev => [...prev, ...batch]);
      indexRef.current = nextIndex;

      if (nextIndex < items.length) {
        setTimeout(loadBatch, delay);
      }
    };

    loadBatch();
  }, [items, batchSize, delay]);

  return displayedItems;
}

// ============================================
// 惰性计算
// ============================================

export function useLazyCalculation<T, R>(
  input: T,
  calculator: (input: T) => R,
  deps: React.DependencyList = []
): R {
  const resultRef = useRef<R>();
  const inputRef = useRef<T>();

  return useMemo(() => {
    // 检查输入是否变化
    if (JSON.stringify(input) !== JSON.stringify(inputRef.current)) {
      inputRef.current = input;
      resultRef.current = calculator(input);
    }
    return resultRef.current!;
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [input, calculator, ...deps]);
}

// ============================================
// 虚拟化支持
// ============================================

interface VirtualizationConfig {
  itemHeight: number;
  containerHeight: number;
  overscan?: number;
  totalItems: number;
}

interface VirtualizationResult {
  startIndex: number;
  endIndex: number;
  startOffset: number;
  totalHeight: number;
  visibleRange: [number, number];
}

export function useVirtualization(
  config: VirtualizationConfig,
  scrollTop: number
): VirtualizationResult {
  const { itemHeight, containerHeight, overscan = 3, totalItems } = config;

  return useMemo(() => {
    const startIndex = Math.max(0, Math.floor(scrollTop / itemHeight) - overscan);
    const visibleCount = Math.ceil(containerHeight / itemHeight);
    const endIndex = Math.min(totalItems - 1, startIndex + visibleCount + overscan * 2);

    return {
      startIndex,
      endIndex,
      startOffset: startIndex * itemHeight,
      totalHeight: totalItems * itemHeight,
      visibleRange: [startIndex, endIndex] as [number, number],
    };
  }, [itemHeight, containerHeight, overscan, totalItems, scrollTop]);
}

// ============================================
// 离屏渲染检测
// ============================================

export function useVisibilityObserver(
  elementRef: React.RefObject<Element>,
  options: IntersectionObserverInit = {}
): boolean {
  const [isVisible, setIsVisible] = useState(false);

  useEffect(() => {
    const element = elementRef.current;
    if (!element) return;

    const observer = new IntersectionObserver(
      ([entry]) => {
        setIsVisible(entry.isIntersecting);
      },
      {
        threshold: 0,
        rootMargin: '50px',
        ...options,
      }
    );

    observer.observe(element);

    return () => {
      observer.disconnect();
    };
  }, [elementRef, options]);

  return isVisible;
}

// ============================================
// 内存泄漏检测 (开发模式)
// ============================================

export function useMemoryLeakDetector(componentName: string) {
  useEffect(() => {
    if (process.env.NODE_ENV !== 'development') return;

    const startMemory = (performance as any).memory?.usedJSHeapSize || 0;

    return () => {
      const endMemory = (performance as any).memory?.usedJSHeapSize || 0;
      const diff = endMemory - startMemory;

      if (diff > 10 * 1024 * 1024) { // 10MB
        console.warn(
          `[Memory Leak Warning] ${componentName} may have leaked ${(diff / 1024 / 1024).toFixed(2)}MB`
        );
      }
    };
  }, [componentName]);
}

export default {
  useFPSMonitor,
  useThrottle,
  useDebounce,
  useRAFThrottle,
  useMemoryOptimizer,
  usePerformanceMonitor,
  useBatchedUpdates,
  useLazyCalculation,
  useVirtualization,
  useVisibilityObserver,
  useMemoryLeakDetector,
};
