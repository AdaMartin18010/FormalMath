import React, { useRef, useEffect, useState, useCallback } from 'react';
import { ZoomIn, ZoomOut, Maximize, Target, Hand, Move } from 'lucide-react';
import { cn } from '@utils/classNames';

interface TouchOptimizedGraphProps {
  children: React.ReactNode;
  className?: string;
  onZoomIn?: () => void;
  onZoomOut?: () => void;
  onReset?: () => void;
  onPanStart?: () => void;
  onPanEnd?: () => void;
  minZoom?: number;
  maxZoom?: number;
  enableGestures?: boolean;
}

/**
 * 触摸优化的图表容器
 * 支持双指缩放、单指拖动、双击缩放等手势
 */
export const TouchOptimizedGraph: React.FC<TouchOptimizedGraphProps> = ({
  children,
  className,
  onZoomIn,
  onZoomOut,
  onReset,
  onPanStart,
  onPanEnd,
  minZoom = 0.1,
  maxZoom = 4,
  enableGestures = true,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const [scale, setScale] = useState(1);
  const [translate, setTranslate] = useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = useState(false);
  const [touchMode, setTouchMode] = useState<'pan' | 'select'>('pan');
  
  // 触摸状态
  const touchState = useRef({
    startDistance: 0,
    startScale: 1,
    startX: 0,
    startY: 0,
    lastX: 0,
    lastY: 0,
    isPinching: false,
  });

  // 获取两点间距离
  const getDistance = useCallback((touches: React.TouchList) => {
    if (touches.length < 2) return 0;
    const dx = touches[0].clientX - touches[1].clientX;
    const dy = touches[0].clientY - touches[1].clientY;
    return Math.sqrt(dx * dx + dy * dy);
  }, []);

  // 处理触摸开始
  const handleTouchStart = useCallback((e: React.TouchEvent) => {
    if (!enableGestures) return;

    const { touches } = e;
    
    if (touches.length === 2) {
      // 双指缩放
      touchState.current.isPinching = true;
      touchState.current.startDistance = getDistance(touches);
      touchState.current.startScale = scale;
    } else if (touches.length === 1) {
      // 单指拖动
      touchState.current.isPinching = false;
      touchState.current.startX = touches[0].clientX - translate.x;
      touchState.current.startY = touches[0].clientY - translate.y;
      touchState.current.lastX = touches[0].clientX;
      touchState.current.lastY = touches[0].clientY;
      
      if (touchMode === 'pan') {
        setIsDragging(true);
        onPanStart?.();
      }
    }
  }, [enableGestures, scale, translate, touchMode, getDistance, onPanStart]);

  // 处理触摸移动
  const handleTouchMove = useCallback((e: React.TouchEvent) => {
    if (!enableGestures) return;

    const { touches } = e;

    if (touches.length === 2 && touchState.current.isPinching) {
      // 双指缩放
      e.preventDefault();
      const currentDistance = getDistance(touches);
      const newScale = Math.min(
        maxZoom,
        Math.max(minZoom, touchState.current.startScale * (currentDistance / touchState.current.startDistance))
      );
      setScale(newScale);
    } else if (touches.length === 1 && isDragging && touchMode === 'pan') {
      // 单指拖动
      e.preventDefault();
      const newX = touches[0].clientX - touchState.current.startX;
      const newY = touches[0].clientY - touchState.current.startY;
      setTranslate({ x: newX, y: newY });
    }
  }, [enableGestures, isDragging, touchMode, maxZoom, minZoom, getDistance]);

  // 处理触摸结束
  const handleTouchEnd = useCallback(() => {
    touchState.current.isPinching = false;
    setIsDragging(false);
    onPanEnd?.();
  }, [onPanEnd]);

  // 处理双击缩放
  const handleDoubleClick = useCallback((e: React.MouseEvent) => {
    if (!enableGestures) return;
    
    const rect = containerRef.current?.getBoundingClientRect();
    if (!rect) return;

    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (scale > 1.5) {
      // 缩小
      setScale(1);
      setTranslate({ x: 0, y: 0 });
    } else {
      // 放大到点击位置
      const newScale = Math.min(maxZoom, scale * 1.5);
      const newX = (rect.width / 2 - x) * (newScale / scale - 1) + translate.x;
      const newY = (rect.height / 2 - y) * (newScale / scale - 1) + translate.y;
      setScale(newScale);
      setTranslate({ x: newX, y: newY });
    }
  }, [enableGestures, scale, translate, maxZoom]);

  // 滚轮缩放
  const handleWheel = useCallback((e: React.WheelEvent) => {
    if (!enableGestures) return;
    e.preventDefault();

    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    const newScale = Math.min(maxZoom, Math.max(minZoom, scale * delta));
    setScale(newScale);
  }, [enableGestures, scale, maxZoom, minZoom]);

  // 控制函数
  const handleZoomIn = useCallback(() => {
    const newScale = Math.min(maxZoom, scale * 1.3);
    setScale(newScale);
    onZoomIn?.();
  }, [scale, maxZoom, onZoomIn]);

  const handleZoomOut = useCallback(() => {
    const newScale = Math.max(minZoom, scale * 0.7);
    setScale(newScale);
    onZoomOut?.();
  }, [scale, minZoom, onZoomOut]);

  const handleReset = useCallback(() => {
    setScale(1);
    setTranslate({ x: 0, y: 0 });
    onReset?.();
  }, [onReset]);

  return (
    <div
      ref={containerRef}
      className={cn(
        'relative overflow-hidden touch-none select-none',
        isDragging && 'cursor-grabbing',
        touchMode === 'pan' && !isDragging && 'cursor-grab',
        className
      )}
      onTouchStart={handleTouchStart}
      onTouchMove={handleTouchMove}
      onTouchEnd={handleTouchEnd}
      onDoubleClick={handleDoubleClick}
      onWheel={handleWheel}
    >
      {/* 变换容器 */}
      <div
        className="w-full h-full transition-transform duration-75 ease-out"
        style={{
          transform: `translate(${translate.x}px, ${translate.y}px) scale(${scale})`,
          transformOrigin: 'center center',
        }}
      >
        {children}
      </div>

      {/* 缩放控制 */}
      <div className="absolute bottom-4 right-4 flex flex-col gap-2 z-10">
        {/* 模式切换 */}
        <div className="flex bg-white dark:bg-slate-800 rounded-lg shadow-lg overflow-hidden mb-2">
          <button
            onClick={() => setTouchMode('pan')}
            className={cn(
              'p-2 transition-colors',
              touchMode === 'pan' 
                ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400' 
                : 'text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700'
            )}
            title="拖动模式"
          >
            <Hand className="w-4 h-4" />
          </button>
          <button
            onClick={() => setTouchMode('select')}
            className={cn(
              'p-2 transition-colors',
              touchMode === 'select' 
                ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400' 
                : 'text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700'
            )}
            title="选择模式"
          >
            <Move className="w-4 h-4" />
          </button>
        </div>

        {/* 缩放按钮 */}
        <button
          onClick={handleZoomIn}
          className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400"
          title="放大"
        >
          <ZoomIn className="w-5 h-5" />
        </button>
        <button
          onClick={handleZoomOut}
          className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400"
          title="缩小"
        >
          <ZoomOut className="w-5 h-5" />
        </button>
        <button
          onClick={handleReset}
          className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400"
          title="重置视图"
        >
          <Target className="w-5 h-5" />
        </button>
      </div>

      {/* 缩放比例显示 */}
      <div className="absolute bottom-4 left-4 px-2 py-1 bg-white/90 dark:bg-slate-800/90 backdrop-blur rounded text-xs font-medium text-gray-600 dark:text-gray-400 shadow-lg">
        {Math.round(scale * 100)}%
      </div>

      {/* 手势提示（仅在移动端显示） */}
      {enableGestures && (
        <div className="absolute top-4 left-1/2 -translate-x-1/2 px-3 py-1.5 bg-black/70 text-white text-xs rounded-full pointer-events-none opacity-0 animate-fade-out">
          双指缩放，双击定位
        </div>
      )}
    </div>
  );
};

export default TouchOptimizedGraph;
