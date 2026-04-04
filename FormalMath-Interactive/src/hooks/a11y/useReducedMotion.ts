/**
 * 减少动画偏好 Hook
 * 尊重用户的系统动画偏好设置
 */

import { useEffect, useState, useCallback } from 'react';

/**
 * 检测用户是否偏好减少动画
 * WCAG 2.1要求尊重用户的动画偏好
 */
export const useReducedMotion = (): boolean => {
  const [prefersReducedMotion, setPrefersReducedMotion] = useState(() => {
    if (typeof window === 'undefined') return false;
    return window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  });

  useEffect(() => {
    const mediaQuery = window.matchMedia('(prefers-reduced-motion: reduce)');
    
    const handleChange = (event: MediaQueryListEvent) => {
      setPrefersReducedMotion(event.matches);
    };

    mediaQuery.addEventListener('change', handleChange);
    
    return () => {
      mediaQuery.removeEventListener('change', handleChange);
    };
  }, []);

  return prefersReducedMotion;
};

/**
 * 动画配置 Hook
 * 根据用户偏好返回适当的动画配置
 */
export const useAnimationConfig = () => {
  const prefersReducedMotion = useReducedMotion();

  const getTransition = useCallback((
    duration: number = 300,
    ease: string = 'ease-out'
  ) => {
    if (prefersReducedMotion) {
      return 'none';
    }
    return `all ${duration}ms ${ease}`;
  }, [prefersReducedMotion]);

  const getTransform = useCallback((
    transform: string,
    fallback?: string
  ) => {
    if (prefersReducedMotion) {
      return fallback || 'none';
    }
    return transform;
  }, [prefersReducedMotion]);

  const getAnimation = useCallback((
    animation: string,
    fallback?: string
  ) => {
    if (prefersReducedMotion) {
      return fallback || 'none';
    }
    return animation;
  }, [prefersReducedMotion]);

  const getSpringConfig = useCallback((
    config: { stiffness?: number; damping?: number; mass?: number } = {}
  ) => {
    if (prefersReducedMotion) {
      return { stiffness: 1000, damping: 1000, mass: 0.1 };
    }
    return {
      stiffness: config.stiffness ?? 100,
      damping: config.damping ?? 10,
      mass: config.mass ?? 1,
    };
  }, [prefersReducedMotion]);

  return {
    prefersReducedMotion,
    getTransition,
    getTransform,
    getAnimation,
    getSpringConfig,
  };
};

/**
 * 高对比度偏好 Hook
 */
export const useHighContrast = (): boolean => {
  const [prefersHighContrast, setPrefersHighContrast] = useState(() => {
    if (typeof window === 'undefined') return false;
    return window.matchMedia('(prefers-contrast: high)').matches;
  });

  useEffect(() => {
    const mediaQuery = window.matchMedia('(prefers-contrast: high)');
    
    const handleChange = (event: MediaQueryListEvent) => {
      setPrefersHighContrast(event.matches);
    };

    mediaQuery.addEventListener('change', handleChange);
    
    return () => {
      mediaQuery.removeEventListener('change', handleChange);
    };
  }, []);

  return prefersHighContrast;
};

/**
 * 颜色方案偏好 Hook
 */
export const useColorScheme = (): 'light' | 'dark' | 'no-preference' => {
  const [colorScheme, setColorScheme] = useState<'light' | 'dark' | 'no-preference'>(() => {
    if (typeof window === 'undefined') return 'no-preference';
    
    const prefersDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
    const prefersLight = window.matchMedia('(prefers-color-scheme: light)').matches;
    
    if (prefersDark) return 'dark';
    if (prefersLight) return 'light';
    return 'no-preference';
  });

  useEffect(() => {
    const darkQuery = window.matchMedia('(prefers-color-scheme: dark)');
    const lightQuery = window.matchMedia('(prefers-color-scheme: light)');
    
    const handleChange = () => {
      if (darkQuery.matches) {
        setColorScheme('dark');
      } else if (lightQuery.matches) {
        setColorScheme('light');
      } else {
        setColorScheme('no-preference');
      }
    };

    darkQuery.addEventListener('change', handleChange);
    lightQuery.addEventListener('change', handleChange);
    
    return () => {
      darkQuery.removeEventListener('change', handleChange);
      lightQuery.removeEventListener('change', handleChange);
    };
  }, []);

  return colorScheme;
};

export default useReducedMotion;
