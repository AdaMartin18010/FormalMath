/**
 * ARIA实时区域组件
 * 用于向屏幕阅读器动态发送通知
 */

import React from 'react';

interface LiveRegionProps {
  id?: string;
  priority?: 'polite' | 'assertive';
  atomic?: boolean;
  relevant?: 'additions' | 'removals' | 'text' | 'all';
  className?: string;
  children?: React.ReactNode;
}

export const LiveRegion: React.FC<LiveRegionProps> = ({
  id = 'live-region',
  priority = 'polite',
  atomic = true,
  relevant,
  className,
  children,
}) => {
  return (
    <div
      id={id}
      role="status"
      aria-live={priority}
      aria-atomic={atomic}
      aria-relevant={relevant}
      className={className || 'sr-only'}
    >
      {children}
    </div>
  );
};

/**
 * 屏幕阅读器专用文本
 * 视觉隐藏但对屏幕阅读器可见
 */
export const VisuallyHidden: React.FC<{ children: React.ReactNode; className?: string }> = ({
  children,
  className,
}) => {
  return (
    <span
      className={className}
      style={{
        position: 'absolute',
        width: '1px',
        height: '1px',
        padding: '0',
        margin: '-1px',
        overflow: 'hidden',
        clip: 'rect(0, 0, 0, 0)',
        whiteSpace: 'nowrap',
        border: '0',
      }}
    >
      {children}
    </span>
  );
};

export default LiveRegion;
