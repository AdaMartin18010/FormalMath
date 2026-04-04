import React, { useState, useCallback, useRef, useEffect } from 'react';
import { RefreshCw, CheckCircle } from 'lucide-react';
import { cn } from '@utils/classNames';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';

export interface PullToRefreshProps {
  onRefresh: () => Promise<void>;
  children: React.ReactNode;
  className?: string;
  pullThreshold?: number;
  maxPullDistance?: number;
  disabled?: boolean;
}

/**
 * 下拉刷新组件
 * 支持：弹性下拉、加载动画、触觉反馈
 */
export const PullToRefresh: React.FC<PullToRefreshProps> = ({
  onRefresh,
  children,
  className,
  pullThreshold = 80,
  maxPullDistance = 120,
  disabled = false,
}) => {
  const { isMobile } = useMobileDetect();
  const containerRef = useRef<HTMLDivElement>(null);
  const [pullDistance, setPullDistance] = useState(0);
  const [isRefreshing, setIsRefreshing] = useState(false);
  const [isComplete, setIsComplete] = useState(false);
  const touchStartY = useRef(0);
  const isPulling = useRef(false);

  // 检测是否在顶部
  const isAtTop = useCallback(() => {
    if (!containerRef.current) return false;
    return containerRef.current.scrollTop <= 0;
  }, []);

  // 处理触摸开始
  const handleTouchStart = useCallback((e: React.TouchEvent) => {
    if (disabled || !isMobile) return;
    
    if (isAtTop()) {
      touchStartY.current = e.touches[0].clientY;
      isPulling.current = true;
    }
  }, [disabled, isMobile, isAtTop]);

  // 处理触摸移动
  const handleTouchMove = useCallback((e: React.TouchEvent) => {
    if (disabled || !isMobile || !isPulling.current || isRefreshing) return;

    const touchY = e.touches[0].clientY;
    const delta = touchY - touchStartY.current;

    // 只有在向下拉动时才触发
    if (delta > 0 && isAtTop()) {
      e.preventDefault();
      
      // 使用阻尼效果
      const dampedDistance = Math.min(delta * 0.5, maxPullDistance);
      setPullDistance(dampedDistance);
    }
  }, [disabled, isMobile, isRefreshing, maxPullDistance, isAtTop]);

  // 处理触摸结束
  const handleTouchEnd = useCallback(async () => {
    if (disabled || !isMobile || !isPulling.current) return;

    isPulling.current = false;

    if (pullDistance >= pullThreshold && !isRefreshing) {
      // 触发刷新
      setIsRefreshing(true);
      setPullDistance(pullThreshold);

      // 触觉反馈
      if (navigator.vibrate) {
        navigator.vibrate(50);
      }

      try {
        await onRefresh();
        setIsComplete(true);
        
        // 显示完成状态后恢复
        setTimeout(() => {
          setIsRefreshing(false);
          setIsComplete(false);
          setPullDistance(0);
        }, 800);
      } catch (error) {
        console.error('Refresh failed:', error);
        setIsRefreshing(false);
        setPullDistance(0);
      }
    } else {
      // 未达到阈值，恢复
      setPullDistance(0);
    }
  }, [disabled, isMobile, pullDistance, pullThreshold, isRefreshing, onRefresh]);

  // 计算旋转角度
  const rotation = Math.min((pullDistance / pullThreshold) * 360, 360);
  const isReady = pullDistance >= pullThreshold;

  if (!isMobile) {
    return <div className={className}>{children}</div>;
  }

  return (
    <div
      ref={containerRef}
      className={cn('relative overflow-hidden', className)}
      onTouchStart={handleTouchStart}
      onTouchMove={handleTouchMove}
      onTouchEnd={handleTouchEnd}
    >
      {/* 下拉指示器 */}
      <div
        className="absolute left-0 right-0 flex items-center justify-center transition-transform"
        style={{
          top: -60,
          transform: `translateY(${pullDistance}px)`,
        }}
      >
        <div className={cn(
          'flex items-center gap-2 px-4 py-2 rounded-full transition-colors',
          isReady ? 'bg-blue-100 dark:bg-blue-900/30 text-blue-600' : 'bg-gray-100 dark:bg-slate-800 text-gray-500'
        )}>
          {isRefreshing ? (
            <RefreshCw className="w-5 h-5 animate-spin" />
          ) : isComplete ? (
            <CheckCircle className="w-5 h-5 text-green-500" />
          ) : (
            <RefreshCw 
              className="w-5 h-5 transition-transform"
              style={{ transform: `rotate(${rotation}deg)` }}
            />
          )}
          <span className="text-sm font-medium">
            {isRefreshing ? '刷新中...' : isComplete ? '刷新完成' : isReady ? '释放刷新' : '下拉刷新'}
          </span>
        </div>
      </div>

      {/* 内容区域 */}
      <div
        className="transition-transform duration-200"
        style={{
          transform: `translateY(${isRefreshing ? pullThreshold : pullDistance}px)`,
        }}
      >
        {children}
      </div>
    </div>
  );
};

export default PullToRefresh;
