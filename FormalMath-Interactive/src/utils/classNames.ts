// ==================== CSS类名工具 ====================

import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';

/**
 * 合并Tailwind CSS类名
 * 使用clsx处理条件类名，再用tailwind-merge解决冲突
 */
export function cn(...inputs: ClassValue[]): string {
  return twMerge(clsx(inputs));
}

/**
 * 条件类名组合
 */
export function classNames(
  ...classes: (string | undefined | null | false | Record<string, boolean>)[]
): string {
  const result: string[] = [];
  
  classes.forEach(item => {
    if (!item) return;
    
    if (typeof item === 'string') {
      result.push(item);
    } else if (typeof item === 'object') {
      Object.entries(item).forEach(([key, value]) => {
        if (value) result.push(key);
      });
    }
  });
  
  return result.join(' ');
}

/**
 * 尺寸变体类名
 */
export const sizeVariants = {
  sm: 'text-sm px-2 py-1',
  md: 'text-base px-4 py-2',
  lg: 'text-lg px-6 py-3',
  xl: 'text-xl px-8 py-4',
} as const;

/**
 * 颜色变体类名
 */
export const colorVariants = {
  primary: 'bg-blue-500 text-white hover:bg-blue-600',
  secondary: 'bg-gray-500 text-white hover:bg-gray-600',
  success: 'bg-green-500 text-white hover:bg-green-600',
  warning: 'bg-yellow-500 text-white hover:bg-yellow-600',
  danger: 'bg-red-500 text-white hover:bg-red-600',
  info: 'bg-cyan-500 text-white hover:bg-cyan-600',
  outline: 'border-2 border-current bg-transparent',
  ghost: 'bg-transparent hover:bg-gray-100',
} as const;

/**
 * 状态类名
 */
export const stateClasses = {
  disabled: 'opacity-50 cursor-not-allowed',
  loading: 'opacity-70 cursor-wait',
  active: 'ring-2 ring-offset-2 ring-blue-500',
  focus: 'outline-none ring-2 ring-blue-500 ring-offset-2',
  hover: 'hover:shadow-md transition-shadow',
} as const;
