/**
 * 焦点指示器组件
 * 自定义焦点样式，符合WCAG 2.1焦点可见性要求
 */

import React from 'react';
import { cn } from '@utils/classNames';

interface FocusIndicatorProps {
  children: React.ReactNode;
  className?: string;
  ringColor?: string;
  ringWidth?: number;
  ringOffset?: number;
  rounded?: string;
}

export const FocusIndicator: React.FC<FocusIndicatorProps> = ({
  children,
  className,
  ringColor = 'ring-blue-500',
  ringWidth = 2,
  ringOffset = 2,
  rounded = 'rounded-md',
}) => {
  return (
    <div
      className={cn(
        // 焦点时显示环形
        'focus-within:ring-2',
        ringColor,
        rounded,
        // 确保子元素可以获得焦点
        '[&>*]:focus:outline-none',
        className
      )}
      style={{
        '--tw-ring-width': `${ringWidth}px`,
        '--tw-ring-offset-width': `${ringOffset}px`,
      } as React.CSSProperties}
    >
      {children}
    </div>
  );
};

/**
 * 焦点可见包装器
 * 仅在键盘导航时显示焦点样式
 */
export const FocusVisibleWrapper: React.FC<{
  children: React.ReactNode;
  className?: string;
}> = ({ children, className }) => {
  return (
    <div
      className={cn(
        // 默认隐藏焦点
        '[&>*]:focus:outline-none',
        // 焦点可见时显示（由父组件或全局CSS控制）
        '[&>*]:focus-visible:outline',
        '[&>*]:focus-visible:outline-2',
        '[&>*]:focus-visible:outline-blue-500',
        '[&>*]:focus-visible:outline-offset-2',
        className
      )}
    >
      {children}
    </div>
  );
};

export default FocusIndicator;
