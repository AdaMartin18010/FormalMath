import React from 'react';
import { cn } from '@utils/classNames';

interface SkeletonProps {
  className?: string;
  width?: string | number;
  height?: string | number;
  circle?: boolean;
  animate?: boolean;
}

/**
 * 基础骨架屏组件
 */
export const Skeleton: React.FC<SkeletonProps> = ({
  className,
  width,
  height,
  circle = false,
  animate = true,
}) => {
  return (
    <div
      className={cn(
        'bg-gray-200 dark:bg-slate-700',
        animate && 'animate-pulse',
        circle ? 'rounded-full' : 'rounded-md',
        className
      )}
      style={{
        width: width,
        height: height,
      }}
    />
  );
};

/**
 * 卡片骨架屏
 */
export const CardSkeleton: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <div className={cn(
      'bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700',
      className
    )}>
      <div className="flex items-start gap-4">
        <Skeleton width={48} height={48} circle />
        <div className="flex-1 space-y-2">
          <Skeleton width="60%" height={20} />
          <Skeleton width="100%" height={16} />
          <Skeleton width="80%" height={16} />
        </div>
      </div>
    </div>
  );
};

/**
 * 图表骨架屏
 */
export const GraphSkeleton: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <div className={cn(
      'bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden',
      className
    )}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between p-4 border-b border-gray-200 dark:border-slate-700">
        <div className="flex items-center gap-3">
          <Skeleton width={24} height={24} />
          <Skeleton width={120} height={20} />
        </div>
        <div className="flex items-center gap-2">
          <Skeleton width={32} height={32} circle />
          <Skeleton width={32} height={32} circle />
          <Skeleton width={32} height={32} circle />
        </div>
      </div>

      {/* 图表区域 */}
      <div className="relative h-[400px] p-4">
        <Skeleton width="100%" height="100%" className="rounded-lg" animate={false} />
        
        {/* 模拟节点 */}
        <div className="absolute inset-0 flex items-center justify-center">
          <div className="relative w-full h-full">
            <div className="absolute top-1/4 left-1/4">
              <Skeleton width={48} height={48} circle />
            </div>
            <div className="absolute top-1/3 right-1/4">
              <Skeleton width={40} height={40} circle />
            </div>
            <div className="absolute bottom-1/3 left-1/3">
              <Skeleton width={36} height={36} circle />
            </div>
            <div className="absolute bottom-1/4 right-1/3">
              <Skeleton width={44} height={44} circle />
            </div>
            <div className="absolute top-1/2 left-1/2 -translate-x-1/2 -translate-y-1/2">
              <Skeleton width={56} height={56} circle />
            </div>
          </div>
        </div>
      </div>

      {/* 底部状态栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-t border-gray-200 dark:border-slate-700">
        <div className="flex items-center gap-4">
          <Skeleton width={60} height={16} />
          <Skeleton width={60} height={16} />
        </div>
        <Skeleton width={80} height={16} />
      </div>
    </div>
  );
};

/**
 * 列表骨架屏
 */
export const ListSkeleton: React.FC<{ 
  className?: string; 
  count?: number;
  itemHeight?: number;
}> = ({ className, count = 5, itemHeight = 64 }) => {
  return (
    <div className={cn('space-y-3', className)}>
      {Array.from({ length: count }).map((_, i) => (
        <div 
          key={i}
          className="flex items-center gap-3 p-3 bg-white dark:bg-slate-800 rounded-lg border border-gray-200 dark:border-slate-700"
        >
          <Skeleton width={itemHeight - 16} height={itemHeight - 16} circle />
          <div className="flex-1 space-y-2">
            <Skeleton width="70%" height={18} />
            <Skeleton width="40%" height={14} />
          </div>
          <Skeleton width={24} height={24} />
        </div>
      ))}
    </div>
  );
};

/**
 * 页面骨架屏
 */
export const PageSkeleton: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <div className={cn('space-y-6 p-4', className)}>
      {/* 标题区域 */}
      <div className="space-y-3">
        <Skeleton width="60%" height={32} />
        <Skeleton width="40%" height={20} />
      </div>

      {/* 统计卡片 */}
      <div className="grid grid-cols-2 lg:grid-cols-4 gap-4">
        {Array.from({ length: 4 }).map((_, i) => (
          <div 
            key={i}
            className="bg-white dark:bg-slate-800 p-4 rounded-xl border border-gray-200 dark:border-slate-700"
          >
            <Skeleton width={32} height={32} circle className="mb-3" />
            <Skeleton width="60%" height={28} className="mb-1" />
            <Skeleton width="40%" height={16} />
          </div>
        ))}
      </div>

      {/* 功能卡片 */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
        {Array.from({ length: 6 }).map((_, i) => (
          <CardSkeleton key={i} />
        ))}
      </div>
    </div>
  );
};

/**
 * 知识图谱页面骨架屏
 */
export const KnowledgeGraphSkeleton: React.FC<{ className?: string }> = ({ className }) => {
  return (
    <div className={cn('flex h-[calc(100vh-64px)]', className)}>
      {/* 侧边栏 */}
      <div className="hidden lg:block w-64 bg-gray-50 dark:bg-slate-900 border-r border-gray-200 dark:border-slate-800 p-4">
        <Skeleton width="80%" height={24} className="mb-6" />
        <div className="space-y-4">
          {Array.from({ length: 4 }).map((_, i) => (
            <div key={i}>
              <Skeleton width="60%" height={18} className="mb-2" />
              <div className="space-y-2 pl-4">
                <Skeleton width="100%" height={16} />
                <Skeleton width="80%" height={16} />
                <Skeleton width="90%" height={16} />
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* 主内容 */}
      <div className="flex-1 flex flex-col">
        {/* 工具栏 */}
        <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200 dark:border-slate-800 bg-white dark:bg-slate-900">
          <div className="flex items-center gap-3">
            <Skeleton width={24} height={24} />
            <Skeleton width={100} height={20} />
          </div>
          <div className="flex items-center gap-2">
            <Skeleton width={80} height={32} />
            <Skeleton width={32} height={32} circle />
            <Skeleton width={32} height={32} circle />
          </div>
        </div>

        {/* 图表区域 */}
        <GraphSkeleton className="flex-1 m-4" />
      </div>
    </div>
  );
};

export default Skeleton;
