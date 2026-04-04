import React, { lazy, Suspense, ComponentType } from 'react';

/**
 * 懒加载工具
 * 提供组件懒加载和预加载功能
 */

// 预加载标记
const preloadedComponents = new Set<string>();

/**
 * 带重试的懒加载
 */
export function lazyLoad<T extends ComponentType<unknown>>(
  factory: () => Promise<{ default: T }>,
  retries = 3,
  retryDelay = 1000
): React.LazyExoticComponent<T> {
  return lazy(() => retryLoad(factory, retries, retryDelay));
}

/**
 * 重试加载
 */
async function retryLoad<T extends ComponentType<unknown>>(
  factory: () => Promise<{ default: T }>,
  retries: number,
  delay: number
): Promise<{ default: T }> {
  try {
    return await factory();
  } catch (error) {
    if (retries === 0) {
      throw error;
    }
    
    await sleep(delay);
    return retryLoad(factory, retries - 1, delay * 1.5);
  }
}

/**
 * 延迟工具
 */
function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

/**
 * 预加载组件
 */
export function prefetchComponent<T extends ComponentType<unknown>>(
  factory: () => Promise<{ default: T }>
): void {
  const key = factory.toString();
  
  if (preloadedComponents.has(key)) {
    return;
  }

  preloadedComponents.add(key);

  // 使用 requestIdleCallback 在空闲时预加载
  if ('requestIdleCallback' in window) {
    requestIdleCallback(() => {
      factory().catch(() => {}); // 忽略预加载错误
    });
  } else {
    setTimeout(() => {
      factory().catch(() => {});
    }, 100);
  }
}

/**
 * 预加载并缓存组件
 */
export function preloadComponent<T extends ComponentType<unknown>>(
  factory: () => Promise<{ default: T }>
): Promise<{ default: T }> {
  const key = factory.toString();
  
  if (preloadedComponents.has(key)) {
    return factory();
  }

  preloadedComponents.add(key);
  return factory();
}

/**
 * 图片懒加载 Hook
 */
export function useLazyImage(src: string): {
  src: string | undefined;
  isLoaded: boolean;
  error: Error | null;
} {
  const [imageSrc, setImageSrc] = React.useState<string | undefined>(undefined);
  const [isLoaded, setIsLoaded] = React.useState(false);
  const [error, setError] = React.useState<Error | null>(null);

  React.useEffect(() => {
    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            setImageSrc(src);
            observer.disconnect();
          }
        });
      },
      { rootMargin: '50px' }
    );

    const img = new Image();
    observer.observe(img);

    return () => observer.disconnect();
  }, [src]);

  React.useEffect(() => {
    if (!imageSrc) return;

    const img = new Image();
    
    img.onload = () => {
      setIsLoaded(true);
    };
    
    img.onerror = () => {
      setError(new Error(`Failed to load image: ${src}`));
    };

    img.src = imageSrc;
  }, [imageSrc, src]);

  return { src: imageSrc, isLoaded, error };
}

/**
 * 图片预加载
 */
export function preloadImage(src: string): Promise<void> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve();
    img.onerror = reject;
    img.src = src;
  });
}

/**
 * 批量预加载图片
 */
export function preloadImages(srcs: string[]): Promise<void> {
  return Promise.all(srcs.map(preloadImage)).then(() => undefined);
}

/**
 * 观察元素可见性
 */
export function useIntersectionObserver(
  callback: (isIntersecting: boolean) => void,
  options?: IntersectionObserverInit
): (node: Element | null) => void {
  const observerRef = React.useRef<IntersectionObserver | null>(null);

  return React.useCallback(
    (node: Element | null) => {
      if (observerRef.current) {
        observerRef.current.disconnect();
      }

      if (node) {
        observerRef.current = new IntersectionObserver(([entry]) => {
          callback(entry.isIntersecting);
        }, options);

        observerRef.current.observe(node);
      }
    },
    [callback, options]
  );
}

/**
 * 动态导入组件
 */
export function dynamicImport<T extends ComponentType<unknown>>(
  importer: () => Promise<{ default: T }>,
  fallback?: React.ReactNode
): React.FC {
  const LazyComponent = lazy(importer);

  return function DynamicComponent(props: React.ComponentProps<T>) {
    return React.createElement(
      Suspense,
      { fallback: fallback || React.createElement('div', null, 'Loading...') },
      React.createElement(LazyComponent, props)
    );
  };
}

/**
 * 优先级加载队列
 */
class LoadQueue {
  private queue: Array<() => Promise<void>> = [];
  private running = false;
  private concurrency: number;

  constructor(concurrency = 3) {
    this.concurrency = concurrency;
  }

  add<T>(loader: () => Promise<T>): Promise<T> {
    return new Promise((resolve, reject) => {
      this.queue.push(async () => {
        try {
          const result = await loader();
          resolve(result);
        } catch (error) {
          reject(error);
        }
      });

      this.process();
    });
  }

  private async process(): Promise<void> {
    if (this.running || this.queue.length === 0) {
      return;
    }

    this.running = true;
    const batch = this.queue.splice(0, this.concurrency);
    
    await Promise.all(batch.map(loader => loader()));
    
    this.running = false;
    this.process();
  }
}

// 全局加载队列
export const loadQueue = new LoadQueue();

export default lazyLoad;
