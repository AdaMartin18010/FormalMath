/**
 * 键盘导航辅助组件
 * 增强键盘导航体验
 */

import React, { useCallback, useRef } from 'react';
import { cn } from '@utils/classNames';

interface KeyboardNavProps {
  children: React.ReactNode;
  className?: string;
  orientation?: 'horizontal' | 'vertical';
  loop?: boolean;
  onNavigate?: (index: number) => void;
}

/**
 * 键盘导航容器
 * 支持方向键导航
 */
export const KeyboardNavContainer: React.FC<KeyboardNavProps> = ({
  children,
  className,
  orientation = 'vertical',
  loop = true,
  onNavigate,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);

  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    const container = containerRef.current;
    if (!container) return;

    const items = Array.from(
      container.querySelectorAll('[data-nav-item]:not([disabled])')
    ) as HTMLElement[];

    const currentIndex = items.findIndex(item => item === document.activeElement);
    let nextIndex = currentIndex;

    const isHorizontal = orientation === 'horizontal';
    const isVertical = orientation === 'vertical';

    switch (e.key) {
      case 'ArrowDown':
        if (isVertical) {
          e.preventDefault();
          nextIndex = currentIndex + 1;
        }
        break;
      case 'ArrowUp':
        if (isVertical) {
          e.preventDefault();
          nextIndex = currentIndex - 1;
        }
        break;
      case 'ArrowRight':
        if (isHorizontal) {
          e.preventDefault();
          nextIndex = currentIndex + 1;
        }
        break;
      case 'ArrowLeft':
        if (isHorizontal) {
          e.preventDefault();
          nextIndex = currentIndex - 1;
        }
        break;
      case 'Home':
        e.preventDefault();
        nextIndex = 0;
        break;
      case 'End':
        e.preventDefault();
        nextIndex = items.length - 1;
        break;
      default:
        return;
    }

    // 循环导航
    if (loop) {
      if (nextIndex < 0) nextIndex = items.length - 1;
      if (nextIndex >= items.length) nextIndex = 0;
    } else {
      nextIndex = Math.max(0, Math.min(nextIndex, items.length - 1));
    }

    if (nextIndex !== currentIndex && items[nextIndex]) {
      items[nextIndex].focus();
      onNavigate?.(nextIndex);
    }
  }, [orientation, loop, onNavigate]);

  return (
    <div
      ref={containerRef}
      onKeyDown={handleKeyDown}
      className={cn(className)}
      role={orientation === 'horizontal' ? 'menubar' : 'menu'}
    >
      {children}
    </div>
  );
};

/**
 * 导航项
 */
export const KeyboardNavItem: React.FC<{
  children: React.ReactNode;
  className?: string;
  disabled?: boolean;
  onSelect?: () => void;
}> = ({ children, className, disabled, onSelect, ...props }) => {
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    if (e.key === 'Enter' || e.key === ' ') {
      e.preventDefault();
      onSelect?.();
    }
  }, [onSelect]);

  return (
    <button
      data-nav-item
      disabled={disabled}
      onKeyDown={handleKeyDown}
      onClick={onSelect}
      className={cn(
        'focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500',
        disabled && 'opacity-50 cursor-not-allowed',
        className
      )}
      {...props}
    >
      {children}
    </button>
  );
};

export default KeyboardNavContainer;
