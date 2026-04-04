/**
 * 懒加载工具函数
 * 性能优化：延迟加载非关键资源
 */

import { lazy, ComponentType, LazyExoticComponent } from 'react';

interface LazyLoadOptions {
  /** 加载超时时间（毫秒） */
  timeout?: number;
  /** 重试次数 */
  retries?: number;
  /** 重试延迟（毫秒） */
  retryDelay?: number;
  /** 加载失败时的回退组件 */
  fallback?: ComponentType;
  /** 预加载优先级 */
  priority?: 'auto' | 'high' | 'low';
}

/**
 * 智能懒加载组件
 * 支持超时、重试和预加载
 */
export function lazyLoad<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>,
  options: LazyLoadOptions = {}
): LazyExoticComponent<T> {
  const {
    timeout = 10000,
    retries = 2,
    retryDelay = 1000,
  } = options;

  let attempts = 0;

  const loadComponent = async (): Promise<{ default: T }> => {
    try {
      // 创建超时Promise
      const timeoutPromise = new Promise<never>((_, reject) => {
        setTimeout(() => reject(new Error('Component load timeout')), timeout);
      });

      // 竞争加载
      const result = await Promise.race([factory(), timeoutPromise]);
      return result;
    } catch (error) {
      attempts++;
      
      if (attempts <= retries) {
        // 延迟后重试
        await new Promise(resolve => setTimeout(resolve, retryDelay));
        return loadComponent();
      }
      
      throw error;
    }
  };

  return lazy(loadComponent);
}

/**
 * 预加载组件
 * 在需要前提前加载组件
 */
export function preloadComponent<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>
): Promise<{ default: T }> {
  return factory();
}

/**
 * 创建可预加载的懒加载组件
 */
export function createLazyComponent<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>,
  options: LazyLoadOptions = {}
) {
  const LazyComponent = lazyLoad(factory, options);
  let preloadPromise: Promise<void> | null = null;

  const preload = () => {
    if (!preloadPromise) {
      preloadPromise = factory().then(() => undefined);
    }
    return preloadPromise;
  };

  return {
    Component: LazyComponent,
    preload,
  };
}

/**
 * 图片懒加载
 * 使用 Intersection Observer API
 */
export function createLazyImageLoader(options: IntersectionObserverInit = {}) {
  const imageMap = new Map<HTMLImageElement, string>();
  
  const observer = new IntersectionObserver((entries) => {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        const img = entry.target as HTMLImageElement;
        const src = imageMap.get(img);
        
        if (src) {
          img.src = src;
          imageMap.delete(img);
          observer.unobserve(img);
        }
      }
    });
  }, {
    rootMargin: '50px',
    ...options,
  });

  return {
    observe: (img: HTMLImageElement, src: string) => {
      imageMap.set(img, src);
      observer.observe(img);
    },
    disconnect: () => observer.disconnect(),
  };
}

/**
 * 动态导入Polyfill
 */
export async function loadPolyfill(feature: string, url: string): Promise<void> {
  if ((window as any)[feature]) {
    return;
  }

  return new Promise((resolve, reject) => {
    const script = document.createElement('script');
    script.src = url;
    script.async = true;
    
    script.onload = () => resolve();
    script.onerror = () => reject(new Error(`Failed to load polyfill: ${feature}`));
    
    document.head.appendChild(script);
  });
}

/**
 * 分块加载数据
 * 用于大量数据的渐进加载
 */
export async function* chunkedLoad<T>(
  fetcher: (offset: number, limit: number) => Promise<T[]>,
  chunkSize: number = 20
): AsyncGenerator<T[], void, unknown> {
  let offset = 0;
  let hasMore = true;

  while (hasMore) {
    const chunk = await fetcher(offset, chunkSize);
    
    if (chunk.length === 0) {
      hasMore = false;
    } else {
      yield chunk;
      offset += chunk.length;
      hasMore = chunk.length === chunkSize;
    }
  }
}

/**
 * 虚拟列表计算
 */
export interface VirtualListConfig {
  itemHeight: number;
  overscan?: number;
  containerHeight: number;
}

export interface VirtualListRange {
  startIndex: number;
  endIndex: number;
  startOffset: number;
  totalHeight: number;
}

export function calculateVirtualRange(
  scrollTop: number,
  itemCount: number,
  config: VirtualListConfig
): VirtualListRange {
  const { itemHeight, overscan = 3, containerHeight } = config;
  
  const startIndex = Math.max(0, Math.floor(scrollTop / itemHeight) - overscan);
  const visibleCount = Math.ceil(containerHeight / itemHeight);
  const endIndex = Math.min(itemCount - 1, startIndex + visibleCount + overscan * 2);
  
  return {
    startIndex,
    endIndex,
    startOffset: startIndex * itemHeight,
    totalHeight: itemCount * itemHeight,
  };
}

export default lazyLoad;
