// @ts-nocheck
import React, { useState, useCallback, useRef } from 'react';
import { cn } from '@utils/classNames';

interface TouchFeedbackProps {
  children: React.ReactNode;
  className?: string;
  feedbackClassName?: string;
  onClick?: (e: React.MouseEvent | React.TouchEvent) => void;
  disabled?: boolean;
  feedbackColor?: 'default' | 'primary' | 'danger' | 'success';
}

/**
 * 触摸反馈组件
 * 为移动端按钮和可点击元素提供视觉反馈
 */
export const TouchFeedback: React.FC<TouchFeedbackProps> = ({
  children,
  className,
  feedbackClassName,
  onClick,
  disabled = false,
  feedbackColor = 'default',
}) => {
  const [isPressed, setIsPressed] = useState(false);
  const touchStartTime = useRef<number>(0);
  const touchMoved = useRef(false);

  const handleTouchStart = useCallback(() => {
    if (disabled) return;
    touchStartTime.current = Date.now();
    touchMoved.current = false;
    setIsPressed(true);
  }, [disabled]);

  const handleTouchMove = useCallback(() => {
    touchMoved.current = true;
    setIsPressed(false);
  }, []);

  const handleTouchEnd = useCallback((e: React.TouchEvent) => {
    setIsPressed(false);
    
    // 如果触摸时间很短且没有移动，视为点击
    const touchDuration = Date.now() - touchStartTime.current;
    if (!touchMoved.current && touchDuration < 500) {
      onClick?.(e);
    }
  }, [onClick]);

  const handleMouseDown = useCallback(() => {
    if (disabled) return;
    setIsPressed(true);
  }, [disabled]);

  const handleMouseUp = useCallback((e: React.MouseEvent) => {
    setIsPressed(false);
    onClick?.(e);
  }, [onClick]);

  const handleMouseLeave = useCallback(() => {
    setIsPressed(false);
  }, []);

  const feedbackColors = {
    default: 'bg-black/10 dark:bg-white/10',
    primary: 'bg-blue-500/20',
    danger: 'bg-red-500/20',
    success: 'bg-green-500/20',
  };

  return (
    <div
      className={cn(
        'relative overflow-hidden cursor-pointer select-none',
        'transition-transform duration-75',
        isPressed && 'scale-95',
        disabled && 'opacity-50 cursor-not-allowed',
        className
      )}
      onTouchStart={handleTouchStart}
      onTouchMove={handleTouchMove}
      onTouchEnd={handleTouchEnd}
      onMouseDown={handleMouseDown}
      onMouseUp={handleMouseUp}
      onMouseLeave={handleMouseLeave}
    >
      {children}
      
      {/* 涟漪效果 */}
      {isPressed && (
        <div
          className={cn(
            'absolute inset-0 pointer-events-none',
            'animate-pulse',
            feedbackColors[feedbackColor],
            feedbackClassName
          )}
        />
      )}
    </div>
  );
};

/**
 * 涟漪效果组件
 */
interface RippleProps {
  color?: string;
  duration?: number;
}

export const Ripple: React.FC<RippleProps> = ({ 
  color = 'rgba(255, 255, 255, 0.3)',
  duration = 600 
}) => {
  const [ripples, setRipples] = useState<Array<{ x: number; y: number; id: number }>>([]);
  const counter = useRef(0);

  const triggerRipple = useCallback((e: React.MouseEvent | React.TouchEvent) => {
    const rect = (e.currentTarget as HTMLElement).getBoundingClientRect();
    let clientX, clientY;

    if ('touches' in e) {
      clientX = e.touches[0].clientX;
      clientY = e.touches[0].clientY;
    } else {
      clientX = (e as React.MouseEvent).clientX;
      clientY = (e as React.MouseEvent).clientY;
    }

    const x = clientX - rect.left;
    const y = clientY - rect.top;
    const id = counter.current++;

    setRipples((prev) => [...prev, { x, y, id }]);

    setTimeout(() => {
      setRipples((prev) => prev.filter((r) => r.id !== id));
    }, duration);
  }, [duration]);

  return { ripples, triggerRipple, RippleContainer: (
    <>
      {ripples.map((ripple) => (
        <span
          key={ripple.id}
          className="absolute rounded-full pointer-events-none animate-ripple"
          style={{
            left: ripple.x,
            top: ripple.y,
            backgroundColor: color,
            transform: 'translate(-50%, -50%)',
          }}
        />
      ))}
    </>
  )};
};

/**
 * 可滑动卡片组件
 */
interface SwipeableCardProps {
  children: React.ReactNode;
  className?: string;
  onSwipeLeft?: () => void;
  onSwipeRight?: () => void;
  onSwipeUp?: () => void;
  onSwipeDown?: () => void;
  threshold?: number;
}

export const SwipeableCard: React.FC<SwipeableCardProps> = ({
  children,
  className,
  onSwipeLeft,
  onSwipeRight,
  onSwipeUp,
  onSwipeDown,
  threshold = 50,
}) => {
  const [translateX, setTranslateX] = useState(0);
  const [translateY, setTranslateY] = useState(0);
  const [isDragging, setIsDragging] = useState(false);
  const startX = useRef(0);
  const startY = useRef(0);

  const handleTouchStart = useCallback((e: React.TouchEvent) => {
    startX.current = e.touches[0].clientX;
    startY.current = e.touches[0].clientY;
    setIsDragging(true);
  }, []);

  const handleTouchMove = useCallback((e: React.TouchEvent) => {
    if (!isDragging) return;
    
    const deltaX = e.touches[0].clientX - startX.current;
    const deltaY = e.touches[0].clientY - startY.current;
    
    setTranslateX(deltaX * 0.5); // 添加阻力效果
    setTranslateY(deltaY * 0.5);
  }, [isDragging]);

  const handleTouchEnd = useCallback(() => {
    setIsDragging(false);
    
    if (translateX > threshold) {
      onSwipeRight?.();
    } else if (translateX < -threshold) {
      onSwipeLeft?.();
    } else if (translateY > threshold) {
      onSwipeDown?.();
    } else if (translateY < -threshold) {
      onSwipeUp?.();
    }
    
    // 回弹动画
    setTranslateX(0);
    setTranslateY(0);
  }, [translateX, translateY, threshold, onSwipeLeft, onSwipeRight, onSwipeUp, onSwipeDown]);

  return (
    <div
      className={cn(
        'transition-transform duration-200 ease-out',
        isDragging && 'duration-0',
        className
      )}
      style={{
        transform: `translate(${translateX}px, ${translateY}px)`,
      }}
      onTouchStart={handleTouchStart}
      onTouchMove={handleTouchMove}
      onTouchEnd={handleTouchEnd}
    >
      {children}
    </div>
  );
};

/**
 * 长按检测Hook
 */
export function useLongPress(
  onLongPress: () => void,
  onClick: () => void,
  delay = 500
) {
  const [startLongPress, setStartLongPress] = useState(false);
  const timerRef = useRef<NodeJS.Timeout>();
  const isLongPress = useRef(false);

  const start = useCallback(() => {
    isLongPress.current = false;
    setStartLongPress(true);
    timerRef.current = setTimeout(() => {
      isLongPress.current = true;
      onLongPress();
    }, delay);
  }, [onLongPress, delay]);

  const stop = useCallback(() => {
    setStartLongPress(false);
    if (timerRef.current) {
      clearTimeout(timerRef.current);
      if (!isLongPress.current) {
        onClick();
      }
    }
  }, [onClick]);

  return {
    onMouseDown: start,
    onMouseUp: stop,
    onMouseLeave: stop,
    onTouchStart: start,
    onTouchEnd: stop,
    isLongPress: startLongPress,
  };
}

export default TouchFeedback;
