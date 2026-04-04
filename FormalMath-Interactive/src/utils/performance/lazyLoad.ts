/**
 * 懒加载与预加载工具
 * 优化组件加载性能
 */

import { lazy, ComponentType, Suspense } from 'react';

interface LazyOptions {
  preload?: boolean;
  delay?: number;
  retry?: number;
  fallback?: ComponentType;
}

/**
 * 智能懒加载组件
 * 支持预加载、重试和延迟加载
 */
export function lazyLoad<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>,
  options: LazyOptions = {}
) {
  const { preload = false, retry = 3 } = options;
  
  let componentPromise: Promise<{ default: T }> | null = null;
  
  const loadComponent = async (): Promise<{ default: T }> => {
    let lastError: Error | null = null;
    
    for (let i = 0; i < retry; i++) {
      try {
        return await factory();
      } catch (error) {
        lastError = error as Error;
        if (i < retry - 1) {
          // 指数退避重试
          await new Promise(resolve => setTimeout(resolve, Math.pow(2, i) * 1000));
        }
      }
    }
    
    throw lastError;
  };
  
  const LazyComponent = lazy(() => {
    if (!componentPromise) {
      componentPromise = loadComponent();
    }
    return componentPromise;
  });
  
  // 预加载方法
  const preloadComponent = () => {
    if (!componentPromise) {
      componentPromise = loadComponent();
    }
    return componentPromise;
  };
  
  if (preload) {
    // 使用 requestIdleCallback 在浏览器空闲时预加载
    if ('requestIdleCallback' in window) {
      window.requestIdleCallback(() => preloadComponent(), { timeout: 2000 });
    } else {
      setTimeout(preloadComponent, 1000);
    }
  }
  
  return Object.assign(LazyComponent, { preload: preloadComponent });
}

/**
 * 预加载组件
 */
export function prefetchComponent<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>
): Promise<{ default: T }> {
  return factory();
}

/**
 * 预加载组件（延迟执行）
 */
export function preloadComponent<T extends ComponentType<any>>(
  factory: () => Promise<{ default: T }>,
  delay = 2000
): () => Promise<{ default: T }> {
  let promise: Promise<{ default: T }> | null = null;
  let timeoutId: ReturnType<typeof setTimeout> | null = null;
  
  const startPreload = () => {
    if (!promise) {
      promise = factory();
    }
    return promise;
  };
  
  // 延迟预加载
  timeoutId = setTimeout(() => {
    if ('requestIdleCallback' in window) {
      window.requestIdleCallback(startPreload, { timeout: 2000 });
    } else {
      startPreload();
    }
  }, delay);
  
  // 返回取消函数
  return () => {
    if (timeoutId) {
      clearTimeout(timeoutId);
    }
    return startPreload();
  };
}

/**
 * 路由级别的组件预加载
 * 基于用户行为预测预加载
 */
export function setupRoutePrefetch() {
  const prefetchMap = new Map<string, () => void>();
  
  // 监听鼠标悬停事件进行预加载
  const handleMouseEnter = (e: MouseEvent) => {
    const target = e.target as HTMLElement;
    const link = target.closest('a[href]');
    
    if (link) {
      const href = link.getAttribute('href');
      if (href && prefetchMap.has(href)) {
        const prefetch = prefetchMap.get(href);
        prefetch?.();
      }
    }
  };
  
  document.addEventListener('mouseenter', handleMouseEnter, true);
  
  return {
    register: (path: string, prefetcher: () => void) => {
      prefetchMap.set(path, prefetcher);
    },
    unregister: (path: string) => {
      prefetchMap.delete(path);
    },
    destroy: () => {
      document.removeEventListener('mouseenter', handleMouseEnter, true);
      prefetchMap.clear();
    },
  };
}

/**
 * 图片懒加载 hook
 */
export function useImageLazyLoad(src: string, options?: IntersectionObserverInit) {
  const [shouldLoad, setShouldLoad] = useState(false);
  const [isLoaded, setIsLoaded] = useState(false);
  const imageRef = useRef<HTMLImageElement>(null);
  
  useEffect(() => {
    const element = imageRef.current;
    if (!element) return;
    
    const observer = new IntersectionObserver((entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          setShouldLoad(true);
          observer.disconnect();
        }
      });
    }, {
      rootMargin: '50px',
      ...options,
    });
    
    observer.observe(element);
    
    return () => observer.disconnect();
  }, [options]);
  
  const handleLoad = () => setIsLoaded(true);
  
  return {
    ref: imageRef,
    src: shouldLoad ? src : undefined,
    isLoaded,
    handleLoad,
  };
}

/**
 * 动态导入 with 超时和重试
 */
export async function dynamicImport<T>(
  importer: () => Promise<T>,
  options: { timeout?: number; retries?: number } = {}
): Promise<T> {
  const { timeout = 10000, retries = 3 } = options;
  
  const attempt = async (remainingRetries: number): Promise<T> => {
    try {
      const timeoutPromise = new Promise<never>((_, reject) => {
        setTimeout(() => reject(new Error('Import timeout')), timeout);
      });
      
      return await Promise.race([importer(), timeoutPromise]);
    } catch (error) {
      if (remainingRetries > 0) {
        await new Promise(resolve => setTimeout(resolve, 1000));
        return attempt(remainingRetries - 1);
      }
      throw error;
    }
  };
  
  return attempt(retries);
}

/**
 * 批量预加载资源
 */
export function preloadResources(
  resources: Array<{ href: string; as: string; type?: string }>
): void {
  const isVisible = document.visibilityState === 'visible';
  
  // 如果页面不可见，延迟加载
  if (!isVisible) {
    const handleVisibility = () => {
      if (document.visibilityState === 'visible') {
        doPreload(resources);
        document.removeEventListener('visibilitychange', handleVisibility);
      }
    };
    document.addEventListener('visibilitychange', handleVisibility);
    return;
  }
  
  // 使用 requestIdleCallback 在空闲时预加载
  if ('requestIdleCallback' in window) {
    window.requestIdleCallback(() => doPreload(resources), { timeout: 2000 });
  } else {
    setTimeout(() => doPreload(resources), 100);
  }
}

function doPreload(
  resources: Array<{ href: string; as: string; type?: string }>
): void {
  resources.forEach((resource, index) => {
    // 使用指数退避错开加载时间
    setTimeout(() => {
      const link = document.createElement('link');
      link.rel = 'preload';
      link.href = resource.href;
      link.as = resource.as;
      
      if (resource.type) {
        link.type = resource.type;
      }
      
      if (resource.as === 'font') {
        link.crossOrigin = 'anonymous';
      }
      
      document.head.appendChild(link);
    }, index * 100);
  });
}

// React hook
import { useState, useEffect, useRef } from 'react';

export default lazyLoad;
