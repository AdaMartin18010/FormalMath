// @ts-nocheck
/**
 * 屏幕阅读器专用组件
 * 仅对辅助技术可见的内容
 */

import React from 'react';
import { cn } from '@utils/classNames';

interface ScreenReaderOnlyProps {
  children: React.ReactNode;
  as?: keyof JSX.IntrinsicElements;
  className?: string;
}

/**
 * 屏幕阅读器专用文本
 * 视觉隐藏但对屏幕阅读器可见
 */
export const ScreenReaderOnly: React.FC<ScreenReaderOnlyProps> = ({
  children,
  as: Component = 'span',
  className,
}) => {
  return (
    <Component
      className={cn(
        'absolute w-px h-px p-0 -m-px',
        'overflow-hidden whitespace-nowrap',
        'border-0',
        'clip-rect-0',
        className
      )}
      style={{
        clip: 'rect(0, 0, 0, 0)',
        clipPath: 'inset(50%)',
      }}
    >
      {children}
    </Component>
  );
};

/**
 * 装饰性元素
 * 对屏幕阅读器隐藏
 */
export const Decorative: React.FC<{
  children: React.ReactNode;
  as?: keyof JSX.IntrinsicElements;
  className?: string;
}> = ({ children, as: Component = 'span', className }) => {
  return (
    <Component aria-hidden="true" className={className}>
      {children}
    </Component>
  );
};

/**
 * 图标标签
 * 为图标提供屏幕阅读器文本
 */
export const IconLabel: React.FC<{
  icon: React.ReactNode;
  label: string;
  className?: string;
}> = ({ icon, label, className }) => {
  return (
    <span className={cn('inline-flex items-center', className)}>
      <span aria-hidden="true">{icon}</span>
      <ScreenReaderOnly>{label}</ScreenReaderOnly>
    </span>
  );
};

/**
 * 带描述的图标
 */
export const IconWithDescription: React.FC<{
  icon: React.ReactNode;
  title: string;
  description: string;
  className?: string;
}> = ({ icon, title, description, className }) => {
  const id = React.useId();
  const descId = `${id}-desc`;

  return (
    <span 
      className={cn('inline-flex items-center', className)}
      role="img"
      aria-labelledby={`${id} ${descId}`}
    >
      <span aria-hidden="true">{icon}</span>
      <ScreenReaderOnly as="span" id={id}>{title}</ScreenReaderOnly>
      <ScreenReaderOnly as="span" id={descId}>{description}</ScreenReaderOnly>
    </span>
  );
};

/**
 * 状态指示器（视觉+屏幕阅读器）
 */
export const StatusIndicator: React.FC<{
  status: 'success' | 'warning' | 'error' | 'info' | 'loading';
  message?: string;
  size?: 'sm' | 'md' | 'lg';
  className?: string;
}> = ({ status, message, size = 'md', className }) => {
  const statusConfig = {
    success: { color: 'bg-green-500', label: '成功' },
    warning: { color: 'bg-yellow-500', label: '警告' },
    error: { color: 'bg-red-500', label: '错误' },
    info: { color: 'bg-blue-500', label: '信息' },
    loading: { color: 'bg-gray-400', label: '加载中' },
  };

  const config = statusConfig[status];
  const displayMessage = message || config.label;

  const sizeClasses = {
    sm: 'w-2 h-2',
    md: 'w-3 h-3',
    lg: 'w-4 h-4',
  };

  return (
    <span className={cn('inline-flex items-center gap-1.5', className)} role="status">
      <span
        className={cn('rounded-full', config.color, sizeClasses[size])}
        aria-hidden="true"
      />
      <span className="sr-only">{config.label}:</span>
      <span>{displayMessage}</span>
    </span>
  );
};

/**
 * 进度指示器
 */
export const ProgressIndicator: React.FC<{
  current: number;
  total: number;
  label?: string;
  className?: string;
}> = ({ current, total, label, className }) => {
  const percentage = Math.round((current / total) * 100);
  const displayLabel = label || `进度 ${current}/${total}`;

  return (
    <div 
      className={cn('w-full', className)}
      role="progressbar"
      aria-valuenow={current}
      aria-valuemin={0}
      aria-valuemax={total}
      aria-label={displayLabel}
    >
      <div className="h-2 bg-gray-200 rounded-full overflow-hidden">
        <div 
          className="h-full bg-blue-500 transition-all duration-300"
          style={{ width: `${percentage}%` }}
        />
      </div>
      <ScreenReaderOnly>
        {displayLabel}，已完成 {percentage}%
      </ScreenReaderOnly>
    </div>
  );
};

export default ScreenReaderOnly;
