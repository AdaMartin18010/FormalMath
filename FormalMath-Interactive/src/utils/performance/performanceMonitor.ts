// @ts-nocheck
/**
 * 性能监控工具
 * 用于监控和分析应用性能
 */

interface PerformanceMetrics {
  // 页面加载时间
  fcp?: number; // First Contentful Paint
  lcp?: number; // Largest Contentful Paint
  fid?: number; // First Input Delay
  cls?: number; // Cumulative Layout Shift
  ttfb?: number; // Time to First Byte
  loadTime?: number; // 总加载时间
}

interface PerformanceEntryHandler {
  (entry: PerformanceEntry): void;
}

class PerformanceMonitor {
  private metrics: PerformanceMetrics = {};
  private observers: PerformanceObserver[] = [];
  private listeners: Map<string, Set<(data: unknown) => void>> = new Map();

  /**
   * 初始化性能监控
   */
  init(): void {
    if (typeof window === 'undefined' || !('performance' in window)) {
      console.warn('Performance API not supported');
      return;
    }

    this.observeFCP();
    this.observeLCP();
    this.observeFID();
    this.observeCLS();
    this.measureLoadTime();
    this.measureTTFB();
  }

  /**
   * 观察 First Contentful Paint
   */
  private observeFCP(): void {
    this.observeEntry('paint', (entry) => {
      if (entry.name === 'first-contentful-paint') {
        this.metrics.fcp = entry.startTime;
        this.emit('fcp', { value: entry.startTime });
      }
    });
  }

  /**
   * 观察 Largest Contentful Paint
   */
  private observeLCP(): void {
    let lcpValue = 0;
    const observer = new PerformanceObserver((entries) => {
      for (const entry of entries.getEntries()) {
        if (entry.startTime > lcpValue) {
          lcpValue = entry.startTime;
          this.metrics.lcp = lcpValue;
          this.emit('lcp', { value: lcpValue });
        }
      }
    });
    
    try {
      observer.observe({ entryTypes: ['largest-contentful-paint'] });
      this.observers.push(observer);
    } catch (e) {
      console.warn('LCP observation not supported');
    }
  }

  /**
   * 观察 First Input Delay
   */
  private observeFID(): void {
    this.observeEntry('first-input', (entry) => {
      const fidEntry = entry as PerformanceEventTiming;
      this.metrics.fid = fidEntry.processingStart - fidEntry.startTime;
      this.emit('fid', { value: this.metrics.fid });
    });
  }

  /**
   * 观察 Cumulative Layout Shift
   */
  private observeCLS(): void {
    let clsValue = 0;
    const observer = new PerformanceObserver((entries) => {
      for (const entry of entries.getEntries()) {
        const layoutShiftEntry = entry as LayoutShift;
        if (!layoutShiftEntry.hadRecentInput) {
          clsValue += layoutShiftEntry.value;
          this.metrics.cls = clsValue;
          this.emit('cls', { value: clsValue });
        }
      }
    });
    
    try {
      observer.observe({ entryTypes: ['layout-shift'] });
      this.observers.push(observer);
    } catch (e) {
      console.warn('CLS observation not supported');
    }
  }

  /**
   * 测量页面加载时间
   */
  private measureLoadTime(): void {
    window.addEventListener('load', () => {
      setTimeout(() => {
        const navigation = performance.getEntriesByType('navigation')[0] as PerformanceNavigationTiming;
        if (navigation) {
          this.metrics.loadTime = navigation.loadEventEnd - navigation.startTime;
          this.emit('loadTime', { value: this.metrics.loadTime });
        }
      }, 0);
    });
  }

  /**
   * 测量 Time to First Byte
   */
  private measureTTFB(): void {
    const navigation = performance.getEntriesByType('navigation')[0] as PerformanceNavigationTiming;
    if (navigation) {
      this.metrics.ttfb = navigation.responseStart - navigation.startTime;
      this.emit('ttfb', { value: this.metrics.ttfb });
    }
  }

  /**
   * 通用性能条目观察
   */
  private observeEntry(type: string, handler: PerformanceEntryHandler): void {
    const observer = new PerformanceObserver((entries) => {
      for (const entry of entries.getEntries()) {
        handler(entry);
      }
    });

    try {
      observer.observe({ entryTypes: [type as any] });
      this.observers.push(observer);
    } catch (e) {
      console.warn(`Performance observation for ${type} not supported`);
    }
  }

  /**
   * 订阅性能指标
   */
  on(event: string, callback: (data: unknown) => void): () => void {
    if (!this.listeners.has(event)) {
      this.listeners.set(event, new Set());
    }
    this.listeners.get(event)!.add(callback);
    
    return () => {
      this.listeners.get(event)?.delete(callback);
    };
  }

  /**
   * 触发事件
   */
  private emit(event: string, data: unknown): void {
    this.listeners.get(event)?.forEach(callback => {
      try {
        callback(data);
      } catch (e) {
        console.error('Error in performance listener:', e);
      }
    });
  }

  /**
   * 获取当前性能指标
   */
  getMetrics(): PerformanceMetrics {
    return { ...this.metrics };
  }

  /**
   * 报告性能指标（可用于发送到分析服务）
   */
  report(): void {
    const metrics = this.getMetrics();
    console.log('Performance Metrics:', metrics);
    
    // 可以在这里发送到 Google Analytics 或其他分析服务
    if ('gtag' in window) {
      (window as any).gtag('event', 'performance_metrics', {
        event_category: 'Performance',
        ...metrics,
      });
    }
  }

  /**
   * 销毁监控器
   */
  destroy(): void {
    this.observers.forEach(observer => observer.disconnect());
    this.observers = [];
    this.listeners.clear();
  }
}

// 全局性能监控实例
export const performanceMonitor = new PerformanceMonitor();

// 初始化性能监控
export function initPerformanceMonitoring(): void {
  performanceMonitor.init();
}

// 测量组件渲染时间
export function measureRenderTime(componentName: string): () => void {
  const startTime = performance.now();
  
  return () => {
    const endTime = performance.now();
    const renderTime = endTime - startTime;
    
    if (renderTime > 16.67) { // 超过一帧的时间（60fps）
      console.warn(`Slow render detected: ${componentName} took ${renderTime.toFixed(2)}ms`);
    }
    
    performanceMonitor.emit('componentRender', {
      component: componentName,
      duration: renderTime,
    });
  };
}

// 资源预加载
export function preloadResource(href: string, as: string): void {
  const link = document.createElement('link');
  link.rel = 'preload';
  link.href = href;
  link.as = as;
  
  if (as === 'font') {
    link.crossOrigin = 'anonymous';
  }
  
  document.head.appendChild(link);
}

// DNS预解析
export function dnsPrefetch(url: string): void {
  const link = document.createElement('link');
  link.rel = 'dns-prefetch';
  link.href = url;
  document.head.appendChild(link);
}

export default performanceMonitor;
