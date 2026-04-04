import { useState, useEffect, useCallback } from 'react';

type Theme = 'light' | 'dark' | 'system';

interface DarkModeState {
  theme: Theme;
  isDark: boolean;
  systemPreference: 'light' | 'dark';
}

const STORAGE_KEY = 'formalmath-theme';

/**
 * 深色模式 Hook
 */
export const useDarkMode = () => {
  const [state, setState] = useState<DarkModeState>({
    theme: 'system',
    isDark: false,
    systemPreference: 'light',
  });

  // 初始化
  useEffect(() => {
    // 读取保存的主题
    const savedTheme = localStorage.getItem(STORAGE_KEY) as Theme | null;
    
    // 检测系统偏好
    const mediaQuery = window.matchMedia('(prefers-color-scheme: dark)');
    const systemPreference = mediaQuery.matches ? 'dark' : 'light';

    const theme = savedTheme || 'system';
    const isDark = theme === 'system' ? systemPreference === 'dark' : theme === 'dark';

    setState({
      theme,
      isDark,
      systemPreference,
    });

    // 应用主题
    applyTheme(isDark);

    // 监听系统主题变化
    const handleChange = (e: MediaQueryListEvent) => {
      const newSystemPreference = e.matches ? 'dark' : 'light';
      setState(prev => {
        if (prev.theme === 'system') {
          const newIsDark = newSystemPreference === 'dark';
          applyTheme(newIsDark);
          return { ...prev, systemPreference: newSystemPreference, isDark: newIsDark };
        }
        return { ...prev, systemPreference: newSystemPreference };
      });
    };

    mediaQuery.addEventListener('change', handleChange);
    return () => mediaQuery.removeEventListener('change', handleChange);
  }, []);

  /**
   * 应用主题到 DOM
   */
  const applyTheme = (isDark: boolean) => {
    const root = document.documentElement;
    if (isDark) {
      root.classList.add('dark');
      root.style.backgroundColor = '#0f172a';
      root.style.colorScheme = 'dark';
    } else {
      root.classList.remove('dark');
      root.style.backgroundColor = '#ffffff';
      root.style.colorScheme = 'light';
    }

    // 更新 meta theme-color
    const metaThemeColor = document.querySelector('meta[name="theme-color"]');
    if (metaThemeColor) {
      metaThemeColor.setAttribute('content', isDark ? '#0f172a' : '#2563eb');
    }

    // 更新 meta apple-mobile-web-app-status-bar-style
    const metaStatusBar = document.querySelector('meta[name="apple-mobile-web-app-status-bar-style"]');
    if (metaStatusBar) {
      metaStatusBar.setAttribute('content', isDark ? 'black-translucent' : 'default');
    }
  };

  /**
   * 设置主题
   */
  const setTheme = useCallback((theme: Theme) => {
    localStorage.setItem(STORAGE_KEY, theme);
    
    setState(prev => {
      const isDark = theme === 'system' 
        ? prev.systemPreference === 'dark' 
        : theme === 'dark';
      
      applyTheme(isDark);
      
      return {
        ...prev,
        theme,
        isDark,
      };
    });
  }, []);

  /**
   * 切换主题
   */
  const toggle = useCallback(() => {
    setState(prev => {
      const newTheme = prev.isDark ? 'light' : 'dark';
      localStorage.setItem(STORAGE_KEY, newTheme);
      applyTheme(!prev.isDark);
      return {
        ...prev,
        theme: newTheme,
        isDark: !prev.isDark,
      };
    });
  }, []);

  /**
   * 切换到深色模式
   */
  const enableDark = useCallback(() => setTheme('dark'), [setTheme]);

  /**
   * 切换到浅色模式
   */
  const enableLight = useCallback(() => setTheme('light'), [setTheme]);

  /**
   * 跟随系统
   */
  const enableSystem = useCallback(() => setTheme('system'), [setTheme]);

  return {
    ...state,
    setTheme,
    toggle,
    enableDark,
    enableLight,
    enableSystem,
  };
};

/**
 * 自动深色模式 Hook（根据时间自动切换）
 */
export const useAutoDarkMode = (options: {
  darkStartHour?: number;
  darkEndHour?: number;
  enabled?: boolean;
} = {}) => {
  const { darkStartHour = 18, darkEndHour = 6, enabled = false } = options;
  const { setTheme, theme } = useDarkMode();

  useEffect(() => {
    if (!enabled || theme !== 'system') return;

    const checkTime = () => {
      const hour = new Date().getHours();
      const isDarkTime = hour >= darkStartHour || hour < darkEndHour;
      setTheme(isDarkTime ? 'dark' : 'light');
    };

    checkTime();
    const intervalId = setInterval(checkTime, 60 * 60 * 1000); // 每小时检查一次

    return () => clearInterval(intervalId);
  }, [enabled, darkStartHour, darkEndHour, theme, setTheme]);

  return { enabled };
};

export default useDarkMode;
