import React from 'react';
import { Loader2, BookOpen } from 'lucide-react';
import { cn } from '@utils/classNames';

interface LoadingProps {
  message?: string;
  size?: 'sm' | 'md' | 'lg';
  fullScreen?: boolean;
  className?: string;
}

export const Loading: React.FC<LoadingProps> = ({
  message = '加载中...',
  size = 'md',
  fullScreen = false,
  className,
}) => {
  const sizeClasses = {
    sm: 'w-4 h-4',
    md: 'w-8 h-8',
    lg: 'w-12 h-12',
  };

  const textSizes = {
    sm: 'text-xs',
    md: 'text-sm',
    lg: 'text-base',
  };

  const content = (
    <div className={cn('flex flex-col items-center justify-center gap-3', className)}>
      <Loader2 className={cn('animate-spin text-blue-600', sizeClasses[size])} />
      {message && (
        <p className={cn('text-gray-600 font-medium', textSizes[size])}>
          {message}
        </p>
      )}
    </div>
  );

  if (fullScreen) {
    return (
      <div className="fixed inset-0 bg-white/80 backdrop-blur-sm flex items-center justify-center z-50">
        {content}
      </div>
    );
  }

  return content;
};

interface PageLoadingProps {
  title?: string;
  description?: string;
}

export const PageLoading: React.FC<PageLoadingProps> = ({
  title = '正在加载页面',
  description = '请稍候，正在准备内容...',
}) => {
  return (
    <div className="min-h-[400px] flex flex-col items-center justify-center">
      <div className="relative">
        <div className="absolute inset-0 bg-blue-100 rounded-full animate-ping opacity-20" />
        <div className="relative bg-white p-4 rounded-full shadow-lg">
          <BookOpen className="w-8 h-8 text-blue-600 animate-pulse" />
        </div>
      </div>
      <h2 className="mt-6 text-xl font-semibold text-gray-900">{title}</h2>
      <p className="mt-2 text-sm text-gray-500">{description}</p>
      <div className="mt-4 flex gap-1">
        <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '0ms' }} />
        <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '150ms' }} />
        <div className="w-2 h-2 bg-blue-600 rounded-full animate-bounce" style={{ animationDelay: '300ms' }} />
      </div>
    </div>
  );
};

interface SkeletonProps {
  className?: string;
  lines?: number;
}

export const Skeleton: React.FC<SkeletonProps> = ({ className, lines = 1 }) => {
  return (
    <div className="space-y-2 animate-pulse">
      {Array.from({ length: lines }).map((_, i) => (
        <div
          key={i}
          className={cn('bg-gray-200 rounded', className)}
        />
      ))}
    </div>
  );
};

export const CardSkeleton: React.FC = () => {
  return (
    <div className="bg-white rounded-lg border border-gray-200 p-4 animate-pulse">
      <div className="flex items-center gap-3 mb-4">
        <div className="w-10 h-10 bg-gray-200 rounded-full" />
        <div className="flex-1">
          <div className="h-4 bg-gray-200 rounded w-3/4 mb-2" />
          <div className="h-3 bg-gray-200 rounded w-1/2" />
        </div>
      </div>
      <div className="space-y-2">
        <div className="h-3 bg-gray-200 rounded" />
        <div className="h-3 bg-gray-200 rounded w-5/6" />
        <div className="h-3 bg-gray-200 rounded w-4/6" />
      </div>
    </div>
  );
};

export default Loading;
