/**
 * 跳过链接组件
 * WCAG 2.1要求：提供绕过重复内容块的方法
 */

import React from 'react';
import { cn } from '@utils/classNames';

interface SkipLinkProps {
  targetId: string;
  children?: React.ReactNode;
  className?: string;
}

export const SkipLink: React.FC<SkipLinkProps> = ({
  targetId,
  children = '跳转到主内容',
  className,
}) => {
  const handleClick = (e: React.MouseEvent<HTMLAnchorElement>) => {
    e.preventDefault();
    const target = document.getElementById(targetId);
    if (target) {
      // 设置tabindex确保可以接收焦点
      if (!target.hasAttribute('tabindex')) {
        target.setAttribute('tabindex', '-1');
      }
      target.focus();
      target.scrollIntoView({ behavior: 'smooth' });
    }
  };

  return (
    <a
      href={`#${targetId}`}
      onClick={handleClick}
      className={cn(
        // 基础样式
        'fixed top-4 left-4 z-[100]',
        // 焦点前隐藏
        '-translate-y-full opacity-0',
        // 焦点时显示
        'focus:translate-y-0 focus:opacity-100',
        // 过渡动画
        'transition-all duration-200 ease-out',
        // 视觉样式
        'px-4 py-2 bg-blue-600 text-white font-medium',
        'rounded-lg shadow-lg',
        'focus:outline-none focus:ring-2 focus:ring-blue-500 focus:ring-offset-2',
        className
      )}
    >
      {children}
    </a>
  );
};

export default SkipLink;
