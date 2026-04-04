/**
 * 高对比度模式组件
 * WCAG 2.1要求支持高对比度显示
 */

import React, { useEffect, useState, createContext, useContext } from 'react';
import { cn } from '@utils/classNames';

interface HighContrastContextType {
  isHighContrast: boolean;
  toggleHighContrast: () => void;
  setHighContrast: (value: boolean) => void;
}

const HighContrastContext = createContext<HighContrastContextType>({
  isHighContrast: false,
  toggleHighContrast: () => {},
  setHighContrast: () => {},
});

export const useHighContrast = () => useContext(HighContrastContext);

/**
 * 高对比度模式Provider
 */
export const HighContrastProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [isHighContrast, setIsHighContrast] = useState(() => {
    if (typeof window === 'undefined') return false;
    return (
      localStorage.getItem('high-contrast') === 'true' ||
      window.matchMedia('(prefers-contrast: high)').matches
    );
  });

  useEffect(() => {
    // 监听系统高对比度变化
    const mediaQuery = window.matchMedia('(prefers-contrast: high)');
    const handleChange = (e: MediaQueryListEvent) => {
      setIsHighContrast(e.matches);
    };

    mediaQuery.addEventListener('change', handleChange);
    return () => mediaQuery.removeEventListener('change', handleChange);
  }, []);

  useEffect(() => {
    localStorage.setItem('high-contrast', String(isHighContrast));
    
    if (isHighContrast) {
      document.documentElement.classList.add('high-contrast');
    } else {
      document.documentElement.classList.remove('high-contrast');
    }
  }, [isHighContrast]);

  const toggleHighContrast = () => setIsHighContrast(prev => !prev);

  return (
    <HighContrastContext.Provider
      value={{
        isHighContrast,
        toggleHighContrast,
        setHighContrast,
      }}
    >
      {children}
    </HighContrastContext.Provider>
  );
};

/**
 * 高对比度切换按钮
 */
export const HighContrastToggle: React.FC<{ className?: string }> = ({ className }) => {
  const { isHighContrast, toggleHighContrast } = useHighContrast();

  return (
    <button
      onClick={toggleHighContrast}
      className={cn(
        'p-2 rounded-lg transition-colors',
        'focus:outline-none focus-visible:ring-2 focus-visible:ring-blue-500',
        isHighContrast
          ? 'bg-yellow-400 text-black'
          : 'bg-gray-100 dark:bg-slate-800 text-gray-700 dark:text-gray-300',
        className
      )}
      aria-pressed={isHighContrast}
      aria-label="切换高对比度模式"
      title="高对比度模式"
    >
      <svg
        className="w-5 h-5"
        fill="none"
        viewBox="0 0 24 24"
        stroke="currentColor"
        aria-hidden="true"
      >
        <circle cx="12" cy="12" r="10" strokeWidth="2" />
        <path
          d="M12 2a10 10 0 0 1 0 20V2z"
          fill="currentColor"
          stroke="none"
        />
      </svg>
    </button>
  );
};

/**
 * 高对比度包装器
 * 为子组件应用高对比度样式
 */
export const HighContrastWrapper: React.FC<{
  children: React.ReactNode;
  className?: string;
}> = ({ children, className }) => {
  const { isHighContrast } = useHighContrast();

  return (
    <div
      className={cn(
        isHighContrast && 'high-contrast-mode',
        className
      )}
    >
      {children}
    </div>
  );
};

export default HighContrastProvider;
