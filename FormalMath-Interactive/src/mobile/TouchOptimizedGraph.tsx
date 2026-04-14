// @ts-nocheck
import React, { useRef, useEffect, useState, useCallback, useMemo } from 'react';
import { ZoomIn, ZoomOut, Maximize, Target, Hand, Move, RotateCcw, MoreHorizontal } from 'lucide-react';
import { cn } from '@utils/classNames';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';
import { useGesture, type GestureState } from '@hooks/mobile/useGesture';

export interface TouchOptimizedGraphProps {
  children: React.ReactNode;
  className?: string;
  onZoomIn?: () => void;
  onZoomOut?: () => void;
  onReset?: () => void;
  onPanStart?: () => void;
  onPanEnd?: () => void;
  onTap?: (x: number, y: number) => void;
  onDoubleTap?: (x: number, y: number) => void;
  onSwipe?: (direction: 'left' | 'right' | 'up' | 'down') => void;
  minZoom?: number;
  maxZoom?: number;
  enableGestures?: boolean;
  enableDoubleTapZoom?: boolean;
  showControls?: boolean;
  showGestureHints?: boolean;
}

export type { TouchOptimizedGraphProps };

/**
 * 增强版触摸优化的图表容器
 * 支持：双指缩放、单指拖动、双击缩放、惯性滑动、手势提示
 */
export const TouchOptimizedGraph: React.FC<TouchOptimizedGraphProps> = ({
  children,
  className,
  onZoomIn,
  onZoomOut,
  onReset,
  onPanStart,
  onPanEnd,
  onTap,
  onDoubleTap,
  onSwipe,
  minZoom = 0.1,
  maxZoom = 4,
  enableGestures = true,
  enableDoubleTapZoom = true,
  showControls = true,
  showGestureHints = true,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const contentRef = useRef<HTMLDivElement>(null);
  const [scale, setScale] = useState(1);
  const [translate, setTranslate] = useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = useState(false);
  const [touchMode, setTouchMode] = useState<'pan' | 'select'>('pan');
  const [showHint, setShowHint] = useState(false);
  const [showMenu, setShowMenu] = useState(false);
  const { isMobile, isTablet, touchSupported } = useMobileDetect();

  // 物理动画状态
  const velocityRef = useRef({ x: 0, y: 0 });
  const lastPositionRef = useRef({ x: 0, y: 0, time: 0 });
  const animationRef = useRef<number>();

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

  // 显示手势提示
  useEffect(() => {
    if (showGestureHints && isMobile && touchSupported) {
      const timer = setTimeout(() => setShowHint(true), 500);
      const hideTimer = setTimeout(() => setShowHint(false), 4500);
      return () => {
        clearTimeout(timer);
        clearTimeout(hideTimer);
      };
    }
  }, [showGestureHints, isMobile, touchSupported]);

  // 获取两点间距离
  const getDistance = useCallback((touches: React.TouchList) => {
    if (touches.length < 2) return 0;
    const dx = touches[0].clientX - touches[1].clientX;
    const dy = touches[0].clientY - touches[1].clientY;
    return Math.sqrt(dx * dx + dy * dy);
  }, []);

  // 惯性滑动动画
  const startInertia = useCallback(() => {
    const decay = 0.95;
    const minVelocity = 0.5;

    const animate = () => {
      if (Math.abs(velocityRef.current.x) < minVelocity && Math.abs(velocityRef.current.y) < minVelocity) {
        cancelAnimationFrame(animationRef.current!);
        return;
      }

      setTranslate(prev => ({
        x: prev.x + velocityRef.current.x,
        y: prev.y + velocityRef.current.y,
      }));

      velocityRef.current.x *= decay;
      velocityRef.current.y *= decay;

      animationRef.current = requestAnimationFrame(animate);
    };

    animationRef.current = requestAnimationFrame(animate);
  }, []);

  // 清理惯性动画
  useEffect(() => {
    return () => {
      if (animationRef.current) {
        cancelAnimationFrame(animationRef.current);
      }
    };
  }, []);

  // 处理触摸开始
  const handleTouchStart = useCallback((e: React.TouchEvent) => {
    if (!enableGestures) return;

    // 取消惯性动画
    if (animationRef.current) {
      cancelAnimationFrame(animationRef.current);
    }

    const { touches } = e;

    if (touches.length === 2) {
      // 双指缩放
      e.preventDefault();
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
      lastPositionRef.current = {
        x: touches[0].clientX,
        y: touches[0].clientY,
        time: Date.now(),
      };

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

      // 计算速度用于惯性
      const now = Date.now();
      const dt = now - lastPositionRef.current.time;
      if (dt > 0) {
        velocityRef.current = {
          x: (touches[0].clientX - lastPositionRef.current.x) / dt * 16,
          y: (touches[0].clientY - lastPositionRef.current.y) / dt * 16,
        };
      }

      lastPositionRef.current = {
        x: touches[0].clientX,
        y: touches[0].clientY,
        time: now,
      };

      setTranslate({ x: newX, y: newY });
    }
  }, [enableGestures, isDragging, touchMode, maxZoom, minZoom, getDistance]);

  // 处理触摸结束
  const handleTouchEnd = useCallback((e: React.TouchEvent) => {
    touchState.current.isPinching = false;
    setIsDragging(false);
    onPanEnd?.();

    // 启动惯性滑动
    if (Math.abs(velocityRef.current.x) > 1 || Math.abs(velocityRef.current.y) > 1) {
      startInertia();
    }
  }, [onPanEnd, startInertia]);

  // 处理双击缩放
  const handleDoubleClick = useCallback((e: React.MouseEvent) => {
    if (!enableGestures || !enableDoubleTapZoom) return;

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

    onDoubleTap?.(x, y);
  }, [enableGestures, enableDoubleTapZoom, scale, translate, maxZoom, onDoubleTap]);

  // 滚轮缩放
  const handleWheel = useCallback((e: React.WheelEvent) => {
    if (!enableGestures) return;
    e.preventDefault();

    const rect = containerRef.current?.getBoundingClientRect();
    if (!rect) return;

    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    const newScale = Math.min(maxZoom, Math.max(minZoom, scale * delta));

    // 以鼠标位置为中心缩放
    const scaleRatio = newScale / scale;
    const newX = x - (x - translate.x) * scaleRatio;
    const newY = y - (y - translate.y) * scaleRatio;

    setScale(newScale);
    setTranslate({ x: newX, y: newY });
  }, [enableGestures, scale, translate, maxZoom, minZoom]);

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
    velocityRef.current = { x: 0, y: 0 };
    onReset?.();
  }, [onReset]);

  // 手势识别
  const { bind: gestureBind } = useGesture({
    onSwipe: (gesture) => {
      if (gesture.direction) {
        onSwipe?.(gesture.direction);
      }
    },
    onTap: (gesture) => {
      onTap?.(gesture.centerX, gesture.centerY);
    },
    onDoubleTap: (gesture) => {
      if (enableDoubleTapZoom) {
        handleDoubleClick({ clientX: gesture.centerX, clientY: gesture.centerY } as React.MouseEvent);
      }
    },
  });

  // 合并手势绑定
  const mergedTouchStart = useCallback((e: React.TouchEvent) => {
    handleTouchStart(e);
    gestureBind.onTouchStart(e);
  }, [handleTouchStart, gestureBind]);

  const mergedTouchMove = useCallback((e: React.TouchEvent) => {
    handleTouchMove(e);
    gestureBind.onTouchMove(e);
  }, [handleTouchMove, gestureBind]);

  const mergedTouchEnd = useCallback((e: React.TouchEvent) => {
    handleTouchEnd(e);
    gestureBind.onTouchEnd(e);
  }, [handleTouchEnd, gestureBind]);

  return (
    <div
      ref={containerRef}
      className={cn(
        'relative overflow-hidden touch-none select-none',
        isDragging && 'cursor-grabbing',
        touchMode === 'pan' && !isDragging && 'cursor-grab',
        className
      )}
      onTouchStart={mergedTouchStart}
      onTouchMove={mergedTouchMove}
      onTouchEnd={mergedTouchEnd}
      onTouchCancel={mergedTouchEnd}
      onDoubleClick={handleDoubleClick}
      onWheel={handleWheel}
    >
      {/* 变换容器 */}
      <div
        ref={contentRef}
        className="w-full h-full"
        style={{
          transform: `translate(${translate.x}px, ${translate.y}px) scale(${scale})`,
          transformOrigin: 'center center',
          transition: isDragging ? 'none' : 'transform 0.1s ease-out',
          willChange: isDragging ? 'transform' : 'auto',
        }}
      >
        {children}
      </div>

      {/* 手势提示 */}
      {showGestureHints && showHint && (
        <div className="absolute top-4 left-1/2 -translate-x-1/2 px-4 py-2 bg-black/70 text-white text-xs rounded-full pointer-events-none animate-fade-out z-20">
          <span className="flex items-center gap-2">
            <span>👆</span> 拖动
            <span>🤏</span> 缩放
            <span>👆👆</span> 双击
          </span>
        </div>
      )}

      {/* 缩放控制 */}
      {showControls && (
        <>
          {/* 主控制按钮 */}
          <div className="absolute bottom-4 right-4 flex flex-col gap-2 z-10">
            {/* 更多菜单按钮 */}
            {(isMobile || isTablet) && (
              <button
                onClick={() => setShowMenu(!showMenu)}
                className={cn(
                  'p-2 rounded-lg shadow-lg transition-colors touch-target',
                  showMenu
                    ? 'bg-blue-600 text-white'
                    : 'bg-white dark:bg-slate-800 text-gray-600 dark:text-gray-400 hover:bg-gray-50 dark:hover:bg-slate-700'
                )}
                title="更多选项"
              >
                <MoreHorizontal className="w-5 h-5" />
              </button>
            )}

            {/* 模式切换 */}
            {showMenu && (
              <div className="flex bg-white dark:bg-slate-800 rounded-lg shadow-lg overflow-hidden mb-2 animate-fadeIn">
                <button
                  onClick={() => setTouchMode('pan')}
                  className={cn(
                    'p-2 transition-colors touch-target',
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
                    'p-2 transition-colors touch-target',
                    touchMode === 'select'
                      ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400'
                      : 'text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700'
                  )}
                  title="选择模式"
                >
                  <Move className="w-4 h-4" />
                </button>
              </div>
            )}

            {/* 缩放按钮 */}
            <button
              onClick={handleZoomIn}
              className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400 touch-target"
              title="放大"
            >
              <ZoomIn className="w-5 h-5" />
            </button>
            <button
              onClick={handleZoomOut}
              className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400 touch-target"
              title="缩小"
            >
              <ZoomOut className="w-5 h-5" />
            </button>
            <button
              onClick={handleReset}
              className="p-2 bg-white dark:bg-slate-800 rounded-lg shadow-lg hover:bg-gray-50 dark:hover:bg-slate-700 transition-colors text-gray-600 dark:text-gray-400 touch-target"
              title="重置视图"
            >
              <RotateCcw className="w-5 h-5" />
            </button>
          </div>

          {/* 缩放比例显示 */}
          <div className="absolute bottom-4 left-4 px-2 py-1 bg-white/90 dark:bg-slate-800/90 backdrop-blur rounded text-xs font-medium text-gray-600 dark:text-gray-400 shadow-lg z-10">
            {Math.round(scale * 100)}%
          </div>
        </>
      )}

      {/* 模式指示器 */}
      <div className="absolute top-4 right-4 px-2 py-1 bg-white/90 dark:bg-slate-800/90 backdrop-blur rounded text-xs font-medium text-gray-600 dark:text-gray-400 shadow-lg z-10">
        {touchMode === 'pan' ? '拖动模式' : '选择模式'}
      </div>
    </div>
  );
};

export default TouchOptimizedGraph;
