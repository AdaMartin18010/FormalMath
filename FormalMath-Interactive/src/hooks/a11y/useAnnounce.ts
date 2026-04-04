/**
 * 屏幕阅读器通知 Hook
 * 实现ARIA实时区域通知
 */

import { useCallback, useRef, useEffect } from 'react';

type AnnouncePriority = 'polite' | 'assertive';
type AnnounceLevel = 'info' | 'success' | 'warning' | 'error';

interface AnnounceOptions {
  priority?: AnnouncePriority;
  level?: AnnounceLevel;
  clearAfter?: number;
}

/**
 * 屏幕阅读器通知 Hook
 * 用于向辅助技术发送通知
 */
export const useAnnounce = () => {
  const politeRef = useRef<HTMLDivElement | null>(null);
  const assertiveRef = useRef<HTMLDivElement | null>(null);

  // 创建ARIA实时区域（如果不存在）
  useEffect(() => {
    const createLiveRegion = (id: string, priority: AnnouncePriority) => {
      let region = document.getElementById(id) as HTMLDivElement;
      if (!region) {
        region = document.createElement('div');
        region.id = id;
        region.setAttribute('aria-live', priority);
        region.setAttribute('aria-atomic', 'true');
        region.setAttribute('class', 'sr-only');
        region.style.cssText = `
          position: absolute;
          width: 1px;
          height: 1px;
          padding: 0;
          margin: -1px;
          overflow: hidden;
          clip: rect(0, 0, 0, 0);
          white-space: nowrap;
          border: 0;
        `;
        document.body.appendChild(region);
      }
      return region;
    };

    politeRef.current = createLiveRegion('aria-live-polite', 'polite');
    assertiveRef.current = createLiveRegion('aria-live-assertive', 'assertive');

    return () => {
      // 不清理，因为其他组件可能在使用
    };
  }, []);

  const announce = useCallback((
    message: string, 
    options: AnnounceOptions = {}
  ) => {
    const { 
      priority = 'polite', 
      level = 'info',
      clearAfter = 0 
    } = options;

    const region = priority === 'assertive' ? assertiveRef.current : politeRef.current;
    if (!region) return;

    // 添加级别前缀
    const levelPrefix = {
      info: '',
      success: '成功：',
      warning: '警告：',
      error: '错误：',
    };

    const fullMessage = levelPrefix[level] + message;

    // 清空后设置新消息（确保屏幕阅读器会读取）
    region.textContent = '';
    
    requestAnimationFrame(() => {
      region.textContent = fullMessage;
    });

    // 自动清理
    if (clearAfter > 0) {
      setTimeout(() => {
        region.textContent = '';
      }, clearAfter);
    }
  }, []);

  const announcePolite = useCallback((message: string, options?: Omit<AnnounceOptions, 'priority'>) => {
    announce(message, { ...options, priority: 'polite' });
  }, [announce]);

  const announceAssertive = useCallback((message: string, options?: Omit<AnnounceOptions, 'priority'>) => {
    announce(message, { ...options, priority: 'assertive' });
  }, [announce]);

  const announceLoading = useCallback((message: string = '加载中...') => {
    announce(message, { priority: 'polite' });
  }, [announce]);

  const announceSuccess = useCallback((message: string) => {
    announce(message, { priority: 'polite', level: 'success' });
  }, [announce]);

  const announceError = useCallback((message: string) => {
    announce(message, { priority: 'assertive', level: 'error' });
  }, [announce]);

  const clearAnnouncements = useCallback(() => {
    if (politeRef.current) politeRef.current.textContent = '';
    if (assertiveRef.current) assertiveRef.current.textContent = '';
  }, []);

  return {
    announce,
    announcePolite,
    announceAssertive,
    announceLoading,
    announceSuccess,
    announceError,
    clearAnnouncements,
  };
};

/**
 * 路由变化通知 Hook
 * 页面切换时通知屏幕阅读器
 */
export const useRouteAnnounce = () => {
  const { announcePolite } = useAnnounce();

  const announcePageChange = useCallback((pageTitle: string) => {
    announcePolite(`已导航到 ${pageTitle}`);
  }, [announcePolite]);

  return {
    announcePageChange,
  };
};

/**
 * 进度通知 Hook
 */
export const useProgressAnnounce = () => {
  const { announcePolite, announceAssertive } = useAnnounce();
  const lastProgressRef = useRef<number>(0);

  const announceProgress = useCallback((
    current: number, 
    total: number, 
    label: string = ''
  ) => {
    const percentage = Math.round((current / total) * 100);
    
    // 每10%或完成时通知
    if (percentage % 10 === 0 && percentage !== lastProgressRef.current) {
      const message = label 
        ? `${label}: ${percentage}%`
        : `进度: ${percentage}%`;
      
      announcePolite(message);
      lastProgressRef.current = percentage;
    }

    // 完成时强制通知
    if (current === total && lastProgressRef.current !== 100) {
      announceAssertive(label ? `${label} 完成` : '完成');
      lastProgressRef.current = 100;
    }
  }, [announcePolite, announceAssertive]);

  const resetProgress = useCallback(() => {
    lastProgressRef.current = 0;
  }, []);

  return {
    announceProgress,
    resetProgress,
  };
};

export default useAnnounce;
