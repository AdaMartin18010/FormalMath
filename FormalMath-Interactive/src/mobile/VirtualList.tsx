import React, { useRef, useState, useCallback, useEffect, useMemo } from 'react';
import { cn } from '@utils/classNames';

interface VirtualListProps<T> {
  items: T[];
  renderItem: (item: T, index: number) => React.ReactNode;
  itemHeight: number;
  className?: string;
  overscan?: number;
  onEndReached?: () => void;
  endReachedThreshold?: number;
  header?: React.ReactNode;
  footer?: React.ReactNode;
  emptyComponent?: React.ReactNode;
  loadingComponent?: React.ReactNode;
  isLoading?: boolean;
}

/**
 * 虚拟列表组件
 * 支持：大数据量渲染、无限滚动、性能优化
 */
export function VirtualList<T>({
  items,
  renderItem,
  itemHeight,
  className,
  overscan = 5,
  onEndReached,
  endReachedThreshold = 200,
  header,
  footer,
  emptyComponent,
  loadingComponent,
  isLoading,
}: VirtualListProps<T>) {
  const containerRef = useRef<HTMLDivElement>(null);
  const [scrollTop, setScrollTop] = useState(0);
  const [containerHeight, setContainerHeight] = useState(0);
  const endReachedCalled = useRef(false);

  // 计算总高度
  const totalHeight = useMemo(() => items.length * itemHeight, [items.length, itemHeight]);

  // 计算可见范围
  const visibleRange = useMemo(() => {
    const start = Math.max(0, Math.floor(scrollTop / itemHeight) - overscan);
    const end = Math.min(
      items.length,
      Math.ceil((scrollTop + containerHeight) / itemHeight) + overscan
    );
    return { start, end };
  }, [scrollTop, containerHeight, itemHeight, overscan, items.length]);

  // 计算偏移量
  const offsetY = visibleRange.start * itemHeight;

  // 可见项目
  const visibleItems = useMemo(() => {
    return items.slice(visibleRange.start, visibleRange.end).map((item, index) => ({
      item,
      index: visibleRange.start + index,
    }));
  }, [items, visibleRange]);

  // 处理滚动
  const handleScroll = useCallback((e: React.UIEvent<HTMLDivElement>) => {
    const newScrollTop = e.currentTarget.scrollTop;
    setScrollTop(newScrollTop);

    // 检测是否接近底部
    if (onEndReached && !isLoading && !endReachedCalled.current) {
      const scrollHeight = e.currentTarget.scrollHeight;
      const clientHeight = e.currentTarget.clientHeight;
      const remaining = scrollHeight - newScrollTop - clientHeight;

      if (remaining < endReachedThreshold) {
        endReachedCalled.current = true;
        onEndReached();
      }
    }
  }, [onEndReached, endReachedThreshold, isLoading]);

  // 重置 endReached 标记
  useEffect(() => {
    endReachedCalled.current = false;
  }, [items.length]);

  // 初始化容器高度
  useEffect(() => {
    if (containerRef.current) {
      setContainerHeight(containerRef.current.clientHeight);
    }

    const handleResize = () => {
      if (containerRef.current) {
        setContainerHeight(containerRef.current.clientHeight);
      }
    };

    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  if (items.length === 0 && !isLoading) {
    return (
      <div ref={containerRef} className={cn('overflow-auto', className)}>
        {header}
        {emptyComponent || (
          <div className="flex flex-col items-center justify-center py-12 text-gray-500">
            <svg className="w-12 h-12 mb-3 text-gray-300" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2" />
            </svg>
            <p>暂无数据</p>
          </div>
        )}
        {footer}
      </div>
    );
  }

  return (
    <div
      ref={containerRef}
      className={cn('overflow-auto', className)}
      onScroll={handleScroll}
      style={{ WebkitOverflowScrolling: 'touch' }}
    >
      {header}
      
      <div style={{ height: totalHeight, position: 'relative' }}>
        <div
          style={{
            transform: `translateY(${offsetY}px)`,
            willChange: 'transform',
          }}
        >
          {visibleItems.map(({ item, index }) => (
            <div key={index} style={{ height: itemHeight }}>
              {renderItem(item, index)}
            </div>
          ))}
        </div>
      </div>

      {isLoading && loadingComponent}
      {footer}
    </div>
  );
}

export default VirtualList;
