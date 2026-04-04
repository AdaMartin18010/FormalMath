/**
 * 响应式图表容器组件
 * 自动适配移动端和桌面端，优化触摸交互
 */

import React, { useRef, useState, useEffect } from 'react';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';
import { ZoomIn, ZoomOut, Maximize, RotateCcw, Move } from 'lucide-react';

interface ResponsiveChartContainerProps {
  children: React.ReactNode;
  title?: string;
  description?: string;
  onZoomIn?: () => void;
  onZoomOut?: () => void;
  onReset?: () => void;
  allowFullscreen?: boolean;
  className?: string;
  minHeight?: string;
}

export const ResponsiveChartContainer: React.FC<ResponsiveChartContainerProps> = ({
  children,
  title,
  description,
  onZoomIn,
  onZoomOut,
  onReset,
  allowFullscreen = true,
  className = '',
  minHeight = '300px',
}) => {
  const { isMobile, isTablet } = useMobileDetect();
  const containerRef = useRef<HTMLDivElement>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [touchStart, setTouchStart] = useState<{ x: number; y: number } | null>(null);
  const [isPinching, setIsPinching] = useState(false);

  const isSmallScreen = isMobile || isTablet;

  // 全屏切换
  const toggleFullscreen = () => {
    if (!containerRef.current) return;

    if (!isFullscreen) {
      containerRef.current.requestFullscreen?.().catch(() => {});
    } else {
      document.exitFullscreen?.().catch(() => {});
    }
  };

  // 监听全屏变化
  useEffect(() => {
    const handleFullscreenChange = () => {
      setIsFullscreen(!!document.fullscreenElement);
    };

    document.addEventListener('fullscreenchange', handleFullscreenChange);
    return () => document.removeEventListener('fullscreenchange', handleFullscreenChange);
  }, []);

  // 触摸手势处理
  const handleTouchStart = (e: React.TouchEvent) => {
    if (e.touches.length === 1) {
      setTouchStart({ x: e.touches[0].clientX, y: e.touches[0].clientY });
    } else if (e.touches.length === 2) {
      setIsPinching(true);
    }
  };

  const handleTouchMove = (e: React.TouchEvent) => {
    if (!touchStart || e.touches.length !== 1) return;
    
    // 处理单指滑动（用于平移）
    const deltaX = e.touches[0].clientX - touchStart.x;
    const deltaY = e.touches[0].clientY - touchStart.y;
    
    // 这里可以触发父组件的平移回调
  };

  const handleTouchEnd = (e: React.TouchEvent) => {
    if (e.touches.length === 0) {
      setTouchStart(null);
      setIsPinching(false);
    }
  };

  // 双击缩放
  const handleDoubleClick = () => {
    if (isFullscreen) {
      document.exitFullscreen?.().catch(() => {});
    } else {
      toggleFullscreen();
    }
  };

  return (
    <div
      ref={containerRef}
      className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg overflow-hidden 
                 transition-all duration-300 ${isFullscreen ? 'fixed inset-0 z-50' : ''} ${className}`}
      style={{ minHeight: isFullscreen ? '100vh' : minHeight }}
      onTouchStart={handleTouchStart}
      onTouchMove={handleTouchMove}
      onTouchEnd={handleTouchEnd}
      onDoubleClick={handleDoubleClick}
    >
      {/* 头部工具栏 */}
      {(title || !isSmallScreen) && (
        <div className="flex items-center justify-between p-3 border-b border-gray-200 dark:border-slate-700">
          <div className="flex-1 min-w-0">
            {title && (
              <h3 className="font-semibold text-gray-900 dark:text-white truncate">
                {title}
              </h3>
            )}
            {description && (
              <p className="text-xs text-gray-500 dark:text-gray-400 truncate">
                {description}
              </p>
            )}
          </div>

          {/* 工具按钮 */}
          <div className="flex items-center gap-1">
            {isMobile && (
              <span className="text-xs text-gray-400 mr-2 flex items-center gap-1">
                <Move className="w-3 h-3" />
                双击全屏
              </span>
            )}

            {onZoomIn && (
              <button
                onClick={onZoomIn}
                className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg 
                         transition-colors"
                title="放大"
              >
                <ZoomIn className="w-4 h-4 text-gray-600 dark:text-gray-400" />
              </button>
            )}

            {onZoomOut && (
              <button
                onClick={onZoomOut}
                className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg 
                         transition-colors"
                title="缩小"
              >
                <ZoomOut className="w-4 h-4 text-gray-600 dark:text-gray-400" />
              </button>
            )}

            {onReset && (
              <button
                onClick={onReset}
                className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg 
                         transition-colors"
                title="重置视图"
              >
                <RotateCcw className="w-4 h-4 text-gray-600 dark:text-gray-400" />
              </button>
            )}

            {allowFullscreen && (
              <button
                onClick={toggleFullscreen}
                className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg 
                         transition-colors"
                title={isFullscreen ? '退出全屏' : '全屏'}
              >
                <Maximize className="w-4 h-4 text-gray-600 dark:text-gray-400" />
              </button>
            )}
          </div>
        </div>
      )}

      {/* 图表内容 */}
      <div className={`relative ${isFullscreen ? 'h-[calc(100vh-60px)]' : ''}`}>
        {children}

        {/* 移动端手势提示 */}
        {isMobile && !isPinching && (
          <div className="absolute bottom-4 right-4 pointer-events-none">
            <div className="bg-black/50 text-white text-xs px-3 py-1.5 rounded-full 
                          backdrop-blur-sm flex items-center gap-1">
              <Move className="w-3 h-3" />
              拖动平移 · 双击全屏
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default ResponsiveChartContainer;
