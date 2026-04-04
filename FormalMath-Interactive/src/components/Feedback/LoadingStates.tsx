import React from 'react';
import { Loader2, BookOpen, Circle, Sparkles } from 'lucide-react';
import { cn } from '@utils/classNames';

interface SkeletonProps {
  className?: string;
  lines?: number;
  width?: string | string[];
}

/**
 * 文本骨架屏
 */
export const TextSkeleton: React.FC<SkeletonProps> = ({ 
  className, 
  lines = 1,
  width,
}) => {
  return (
    <div className="space-y-2 animate-pulse">
      {Array.from({ length: lines }).map((_, i) => {
        const lineWidth = Array.isArray(width) 
          ? width[i] 
          : i === lines - 1 && width 
            ? width 
            : '100%';
        
        return (
          <div
            key={i}
            className={cn('h-4 bg-gray-200 dark:bg-slate-700 rounded', className)}
            style={{ width: lineWidth !== '100%' ? lineWidth : undefined }}
          />
        );
      })}
    </div>
  );
};

/**
 * 卡片骨架屏
 */
export const CardSkeleton: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <div className={cn('bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-4 animate-pulse', className)}>
      <div className="flex items-center gap-3 mb-4">
        <div className="w-10 h-10 bg-gray-200 dark:bg-slate-700 rounded-full" />
        <div className="flex-1">
          <div className="h-4 bg-gray-200 dark:bg-slate-700 rounded w-3/4 mb-2" />
          <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded w-1/2" />
        </div>
      </div>
      <div className="space-y-2">
        <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded" />
        <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded w-5/6" />
        <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded w-4/6" />
      </div>
    </div>
  );
};

/**
 * 列表骨架屏
 */
interface ListSkeletonProps {
  count?: number;
  className?: string;
}

export const ListSkeleton: React.FC<ListSkeletonProps> = ({ count = 3, className }) => {
  return (
    <div className={cn('space-y-3', className)}>
      {Array.from({ length: count }).map((_, i) => (
        <div
          key={i}
          className="flex items-center gap-3 p-3 bg-white dark:bg-slate-800 rounded-lg border border-gray-200 dark:border-slate-700 animate-pulse"
        >
          <div className="w-10 h-10 bg-gray-200 dark:bg-slate-700 rounded-lg" />
          <div className="flex-1">
            <div className="h-4 bg-gray-200 dark:bg-slate-700 rounded w-1/3 mb-2" />
            <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded w-1/2" />
          </div>
        </div>
      ))}
    </div>
  );
};

/**
 * 图片骨架屏
 */
interface ImageSkeletonProps {
  aspectRatio?: string;
  className?: string;
}

export const ImageSkeleton: React.FC<ImageSkeletonProps> = ({ 
  aspectRatio = '16/9',
  className 
}) => {
  return (
    <div 
      className={cn(
        'bg-gray-200 dark:bg-slate-700 rounded-lg animate-pulse flex items-center justify-center',
        className
      )}
      style={{ aspectRatio }}
    >
      <Circle className="w-8 h-8 text-gray-300 dark:text-slate-600" />
    </div>
  );
};

/**
 * 页面加载器
 */
interface PageLoaderProps {
  title?: string;
  description?: string;
  progress?: number;
}

export const PageLoader: React.FC<PageLoaderProps> = ({
  title = '正在加载',
  description = '请稍候...',
  progress,
}) => {
  return (
    <div className="min-h-[400px] flex flex-col items-center justify-center p-8">
      {/* Logo动画 */}
      <div className="relative mb-6">
        <div className="absolute inset-0 bg-blue-100 rounded-full animate-ping opacity-20" />
        <div className="relative w-16 h-16 bg-white dark:bg-slate-800 rounded-full shadow-lg flex items-center justify-center">
          <BookOpen className="w-8 h-8 text-blue-600 animate-pulse" />
        </div>
      </div>
      
      {/* 标题 */}
      <h2 className="text-xl font-semibold text-gray-900 dark:text-white mb-2">
        {title}
      </h2>
      <p className="text-sm text-gray-500 dark:text-gray-400 mb-6">
        {description}
      </p>
      
      {/* 进度条 */}
      {progress !== undefined ? (
        <div className="w-48 h-1.5 bg-gray-200 dark:bg-slate-700 rounded-full overflow-hidden">
          <div 
            className="h-full bg-blue-600 rounded-full transition-all duration-300"
            style={{ width: `${Math.min(100, Math.max(0, progress))}%` }}
          />
        </div>
      ) : (
        /* 加载动画 */
        <div className="flex gap-1">
          <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '0ms' }} />
          <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '150ms' }} />
          <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '300ms' }} />
        </div>
      )}
    </div>
  );
};

/**
 * 渐进式加载组件
 */
interface ProgressiveLoadProps {
  children: React.ReactNode;
  fallback?: React.ReactNode;
  delay?: number;
}

export const ProgressiveLoad: React.FC<ProgressiveLoadProps> = ({
  children,
  fallback,
  delay = 0,
}) => {
  const [isVisible, setIsVisible] = React.useState(delay === 0);

  React.useEffect(() => {
    if (delay > 0) {
      const timer = setTimeout(() => setIsVisible(true), delay);
      return () => clearTimeout(timer);
    }
  }, [delay]);

  if (!isVisible) {
    return fallback ? <>{fallback}</> : <CardSkeleton />;
  }

  return <>{children}</>;
};

/**
 * 渐进式图片加载
 */
interface ProgressiveImageProps {
  src: string;
  alt: string;
  className?: string;
  placeholderColor?: string;
}

export const ProgressiveImage: React.FC<ProgressiveImageProps> = ({
  src,
  alt,
  className,
  placeholderColor = '#e5e7eb',
}) => {
  const [isLoaded, setIsLoaded] = React.useState(false);

  return (
    <div 
      className={cn('relative overflow-hidden', className)}
      style={{ backgroundColor: placeholderColor }}
    >
      {!isLoaded && (
        <div className="absolute inset-0 animate-pulse bg-gray-200 dark:bg-slate-700" />
      )}
      <img
        src={src}
        alt={alt}
        className={cn(
          'w-full h-full object-cover transition-opacity duration-300',
          isLoaded ? 'opacity-100' : 'opacity-0'
        )}
        onLoad={() => setIsLoaded(true)}
      />
    </div>
  );
};

/**
 * 智能加载更多
 */
interface SmartLoadMoreProps {
  hasMore: boolean;
  loading: boolean;
  onLoadMore: () => void;
  threshold?: number;
}

export const SmartLoadMore: React.FC<SmartLoadMoreProps> = ({
  hasMore,
  loading,
  onLoadMore,
  threshold = 100,
}) => {
  const observerRef = React.useRef<IntersectionObserver | null>(null);
  const triggerRef = React.useRef<HTMLDivElement>(null);

  React.useEffect(() => {
    if (loading || !hasMore) return;

    observerRef.current = new IntersectionObserver(
      (entries) => {
        if (entries[0].isIntersecting) {
          onLoadMore();
        }
      },
      { rootMargin: `${threshold}px` }
    );

    if (triggerRef.current) {
      observerRef.current.observe(triggerRef.current);
    }

    return () => observerRef.current?.disconnect();
  }, [loading, hasMore, onLoadMore, threshold]);

  if (!hasMore) return null;

  return (
    <div ref={triggerRef} className="py-4 text-center">
      {loading ? (
        <div className="flex items-center justify-center gap-2 text-gray-500">
          <Loader2 className="w-4 h-4 animate-spin" />
          <span className="text-sm">加载中...</span>
        </div>
      ) : (
        <div className="h-4" /> // 触发观察器的占位元素
      )}
    </div>
  );
};

/**
 * 内容加载优化包装器
 */
interface ContentLoaderProps {
  children: React.ReactNode;
  isLoading: boolean;
  skeleton?: React.ReactNode;
  minHeight?: string;
}

export const ContentLoader: React.FC<ContentLoaderProps> = ({
  children,
  isLoading,
  skeleton,
  minHeight = '200px',
}) => {
  if (isLoading) {
    return (
      <div style={{ minHeight }}>
        {skeleton || <CardSkeleton />}
      </div>
    );
  }

  return <>{children}</>;
};

export default PageLoader;
