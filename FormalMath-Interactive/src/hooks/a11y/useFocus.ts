/**
 * 焦点管理 Hook - 无障碍优化
 * 实现WCAG 2.1焦点管理要求
 */

import { useCallback, useRef, useEffect, useState } from 'react';

interface FocusTrapOptions {
  enabled?: boolean;
  onEscape?: () => void;
  initialFocus?: boolean;
  returnFocus?: boolean;
}

/**
 * 焦点陷阱 Hook - 用于模态框、对话框等
 * 确保键盘焦点不会逃出组件
 */
export const useFocusTrap = <T extends HTMLElement>(options: FocusTrapOptions = {}) => {
  const { 
    enabled = true, 
    onEscape, 
    initialFocus = true,
    returnFocus = true 
  } = options;
  
  const containerRef = useRef<T>(null);
  const previousFocusRef = useRef<HTMLElement | null>(null);

  useEffect(() => {
    if (!enabled) return;

    // 保存之前的焦点
    if (returnFocus) {
      previousFocusRef.current = document.activeElement as HTMLElement;
    }

    const container = containerRef.current;
    if (!container) return;

    // 获取所有可聚焦元素
    const getFocusableElements = () => {
      const selectors = [
        'button:not([disabled])',
        'a[href]',
        'input:not([disabled])',
        'select:not([disabled])',
        'textarea:not([disabled])',
        '[tabindex]:not([tabindex="-1"])',
        '[contenteditable]',
      ].join(', ');

      return Array.from(container.querySelectorAll(selectors)) as HTMLElement[];
    };

    // 初始焦点
    if (initialFocus) {
      const focusableElements = getFocusableElements();
      if (focusableElements.length > 0) {
        focusableElements[0].focus();
      }
    }

    // 处理Tab键
    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.key !== 'Tab') return;

      const focusableElements = getFocusableElements();
      if (focusableElements.length === 0) return;

      const firstElement = focusableElements[0];
      const lastElement = focusableElements[focusableElements.length - 1];

      // Shift + Tab
      if (e.shiftKey) {
        if (document.activeElement === firstElement) {
          e.preventDefault();
          lastElement.focus();
        }
      } else {
        // Tab
        if (document.activeElement === lastElement) {
          e.preventDefault();
          firstElement.focus();
        }
      }
    };

    // 处理Escape键
    const handleEscape = (e: KeyboardEvent) => {
      if (e.key === 'Escape' && onEscape) {
        e.preventDefault();
        onEscape();
      }
    };

    container.addEventListener('keydown', handleKeyDown);
    container.addEventListener('keydown', handleEscape);

    return () => {
      container.removeEventListener('keydown', handleKeyDown);
      container.removeEventListener('keydown', handleEscape);
      
      // 恢复之前的焦点
      if (returnFocus && previousFocusRef.current) {
        previousFocusRef.current.focus();
      }
    };
  }, [enabled, onEscape, initialFocus, returnFocus]);

  return containerRef;
};

/**
 * 焦点可见性 Hook
 * 检测焦点是否由键盘触发（而非鼠标点击）
 */
export const useFocusVisible = () => {
  const [isFocusVisible, setIsFocusVisible] = useState(false);

  useEffect(() => {
    const handleKeyDown = () => {
      setIsFocusVisible(true);
    };

    const handlePointerDown = () => {
      setIsFocusVisible(false);
    };

    document.addEventListener('keydown', handleKeyDown);
    document.addEventListener('mousedown', handlePointerDown);
    document.addEventListener('touchstart', handlePointerDown);

    return () => {
      document.removeEventListener('keydown', handleKeyDown);
      document.removeEventListener('mousedown', handlePointerDown);
      document.removeEventListener('touchstart', handlePointerDown);
    };
  }, []);

  return isFocusVisible;
};

/**
 * 焦点管理器 Hook
 * 用于程序化焦点管理
 */
export const useFocusManager = () => {
  const focusHistoryRef = useRef<HTMLElement[]>([]);

  const saveFocus = useCallback(() => {
    const currentElement = document.activeElement as HTMLElement;
    if (currentElement) {
      focusHistoryRef.current.push(currentElement);
    }
  }, []);

  const restoreFocus = useCallback(() => {
    const lastElement = focusHistoryRef.current.pop();
    if (lastElement && document.contains(lastElement)) {
      lastElement.focus();
    }
  }, []);

  const focusFirst = useCallback((container: HTMLElement) => {
    const focusableElements = container.querySelectorAll(
      'button:not([disabled]), a[href], input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])'
    );
    
    if (focusableElements.length > 0) {
      (focusableElements[0] as HTMLElement).focus();
    }
  }, []);

  const focusLast = useCallback((container: HTMLElement) => {
    const focusableElements = container.querySelectorAll(
      'button:not([disabled]), a[href], input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])'
    );
    
    if (focusableElements.length > 0) {
      (focusableElements[focusableElements.length - 1] as HTMLElement).focus();
    }
  }, []);

  const clearHistory = useCallback(() => {
    focusHistoryRef.current = [];
  }, []);

  return {
    saveFocus,
    restoreFocus,
    focusFirst,
    focusLast,
    clearHistory,
    focusHistory: focusHistoryRef.current,
  };
};

/**
 * 跳过链接 Hook
 * 实现"跳到主内容"功能
 */
export const useSkipLink = (mainContentId: string) => {
  const skipLinkRef = useRef<HTMLAnchorElement>(null);

  const handleSkip = useCallback((e: React.MouseEvent) => {
    e.preventDefault();
    const mainContent = document.getElementById(mainContentId);
    if (mainContent) {
      mainContent.focus();
      mainContent.scrollIntoView({ behavior: 'smooth' });
    }
  }, [mainContentId]);

  return {
    skipLinkRef,
    handleSkip,
    skipLinkProps: {
      ref: skipLinkRef,
      href: `#${mainContentId}`,
      onClick: handleSkip,
    },
  };
};

export default useFocusTrap;
