/**
 * 优化的动画 Hook
 * 提供流畅、高性能的动画效果
 */

import { useCallback, useEffect, useRef, useState } from 'react';

// ============================================
// 类型定义
// ============================================

interface AnimationConfig {
  duration: number;
  easing?: (t: number) => number;
  onUpdate?: (value: number) => void;
  onComplete?: () => void;
}

interface SpringConfig {
  stiffness?: number;
  damping?: number;
  mass?: number;
}

interface TransitionConfig {
  type?: 'tween' | 'spring' | 'keyframes';
  duration?: number;
  delay?: number;
  ease?: string | number[];
  spring?: SpringConfig;
}

// ============================================
// 缓动函数
// ============================================

export const easings = {
  linear: (t: number) => t,
  easeInQuad: (t: number) => t * t,
  easeOutQuad: (t: number) => t * (2 - t),
  easeInOutQuad: (t: number) => (t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t),
  easeInCubic: (t: number) => t * t * t,
  easeOutCubic: (t: number) => --t * t * t + 1,
  easeInOutCubic: (t: number) =>
    t < 0.5 ? 4 * t * t * t : (t - 1) * (2 * t - 2) * (2 * t - 2) + 1,
  easeOutBack: (t: number) => {
    const c1 = 1.70158;
    const c3 = c1 + 1;
    return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2);
  },
  easeOutBounce: (t: number) => {
    const n1 = 7.5625;
    const d1 = 2.75;
    if (t < 1 / d1) {
      return n1 * t * t;
    } else if (t < 2 / d1) {
      return n1 * (t -= 1.5 / d1) * t + 0.75;
    } else if (t < 2.5 / d1) {
      return n1 * (t -= 2.25 / d1) * t + 0.9375;
    } else {
      return n1 * (t -= 2.625 / d1) * t + 0.984375;
    }
  },
};

// ============================================
// 基础动画 Hook
// ============================================

export function useAnimation(config: AnimationConfig) {
  const rafRef = useRef<number | null>(null);
  const startTimeRef = useRef<number | null>(null);
  const isRunningRef = useRef(false);

  const start = useCallback(() => {
    if (isRunningRef.current) return;
    
    isRunningRef.current = true;
    startTimeRef.current = null;

    const animate = (timestamp: number) => {
      if (!startTimeRef.current) {
        startTimeRef.current = timestamp;
      }

      const elapsed = timestamp - startTimeRef.current;
      const progress = Math.min(elapsed / config.duration, 1);
      const easedProgress = (config.easing || easings.easeOutQuad)(progress);

      config.onUpdate?.(easedProgress);

      if (progress < 1) {
        rafRef.current = requestAnimationFrame(animate);
      } else {
        isRunningRef.current = false;
        config.onComplete?.();
      }
    };

    rafRef.current = requestAnimationFrame(animate);
  }, [config]);

  const stop = useCallback(() => {
    if (rafRef.current) {
      cancelAnimationFrame(rafRef.current);
      rafRef.current = null;
    }
    isRunningRef.current = false;
  }, []);

  useEffect(() => {
    return () => {
      stop();
    };
  }, [stop]);

  return { start, stop, isRunning: () => isRunningRef.current };
}

// ============================================
// Spring 动画
// ============================================

export function useSpring(
  targetValue: number,
  config: SpringConfig = {}
): number {
  const { stiffness = 100, damping = 10, mass = 1 } = config;
  const [currentValue, setCurrentValue] = useState(targetValue);
  const velocityRef = useRef(0);
  const rafRef = useRef<number | null>(null);
  const lastTimeRef = useRef<number>(0);

  useEffect(() => {
    const animate = (timestamp: number) => {
      if (!lastTimeRef.current) {
        lastTimeRef.current = timestamp;
      }

      const deltaTime = Math.min((timestamp - lastTimeRef.current) / 1000, 0.1);
      lastTimeRef.current = timestamp;

      setCurrentValue(prev => {
        const displacement = targetValue - prev;
        const springForce = displacement * stiffness;
        const dampingForce = velocityRef.current * damping;
        const acceleration = (springForce - dampingForce) / mass;

        velocityRef.current += acceleration * deltaTime;
        const newValue = prev + velocityRef.current * deltaTime;

        // 停止条件
        if (Math.abs(displacement) < 0.001 && Math.abs(velocityRef.current) < 0.001) {
          return targetValue;
        }

        return newValue;
      });

      rafRef.current = requestAnimationFrame(animate);
    };

    rafRef.current = requestAnimationFrame(animate);

    return () => {
      if (rafRef.current) {
        cancelAnimationFrame(rafRef.current);
      }
    };
  }, [targetValue, stiffness, damping, mass]);

  return currentValue;
}

// ============================================
// 数值过渡
// ============================================

export function useAnimatedValue(
  targetValue: number,
  duration: number = 300,
  easing: (t: number) => number = easings.easeOutQuad
): number {
  const [displayValue, setDisplayValue] = useState(targetValue);
  const startValueRef = useRef(targetValue);
  const startTimeRef = useRef<number | null>(null);
  const rafRef = useRef<number | null>(null);

  useEffect(() => {
    if (displayValue === targetValue) return;

    startValueRef.current = displayValue;
    startTimeRef.current = null;

    const animate = (timestamp: number) => {
      if (!startTimeRef.current) {
        startTimeRef.current = timestamp;
      }

      const elapsed = timestamp - startTimeRef.current;
      const progress = Math.min(elapsed / duration, 1);
      const easedProgress = easing(progress);

      const newValue = startValueRef.current + (targetValue - startValueRef.current) * easedProgress;
      setDisplayValue(newValue);

      if (progress < 1) {
        rafRef.current = requestAnimationFrame(animate);
      }
    };

    rafRef.current = requestAnimationFrame(animate);

    return () => {
      if (rafRef.current) {
        cancelAnimationFrame(rafRef.current);
      }
    };
  }, [targetValue, duration, easing, displayValue]);

  return displayValue;
}

// ============================================
// 交错动画
// ============================================

export function useStaggeredAnimation(
  itemCount: number,
  config: {
    staggerDelay?: number;
    initialDelay?: number;
    duration?: number;
  } = {}
): number[] {
  const { staggerDelay = 50, initialDelay = 0, duration = 300 } = config;
  const [progresses, setProgresses] = useState<number[]>(() =>
    Array(itemCount).fill(0)
  );
  const rafRef = useRef<number | null>(null);
  const startTimeRef = useRef<number | null>(null);

  useEffect(() => {
    startTimeRef.current = null;

    const animate = (timestamp: number) => {
      if (!startTimeRef.current) {
        startTimeRef.current = timestamp;
      }

      const elapsed = timestamp - startTimeRef.current;

      setProgresses(prev =>
        prev.map((_, index) => {
          const itemStartTime = initialDelay + index * staggerDelay;
          const itemElapsed = Math.max(0, elapsed - itemStartTime);
          return Math.min(itemElapsed / duration, 1);
        })
      );

      const allComplete = progresses.every(p => p >= 1);
      if (!allComplete) {
        rafRef.current = requestAnimationFrame(animate);
      }
    };

    rafRef.current = requestAnimationFrame(animate);

    return () => {
      if (rafRef.current) {
        cancelAnimationFrame(rafRef.current);
      }
    };
  }, [itemCount, staggerDelay, initialDelay, duration, progresses]);

  return progresses;
}

// ============================================
// 脉冲动画
// ============================================

export function usePulse(
  config: {
    min?: number;
    max?: number;
    duration?: number;
    enabled?: boolean;
  } = {}
): number {
  const { min = 0.8, max = 1.2, duration = 1000, enabled = true } = config;
  const [value, setValue] = useState(min);
  const rafRef = useRef<number | null>(null);

  useEffect(() => {
    if (!enabled) {
      setValue(1);
      return;
    }

    let startTime: number | null = null;

    const animate = (timestamp: number) => {
      if (!startTime) {
        startTime = timestamp;
      }

      const elapsed = timestamp - startTime;
      const progress = (elapsed % duration) / duration;
      const sineValue = Math.sin(progress * Math.PI * 2);
      const normalizedValue = min + (max - min) * (0.5 + sineValue * 0.5);

      setValue(normalizedValue);
      rafRef.current = requestAnimationFrame(animate);
    };

    rafRef.current = requestAnimationFrame(animate);

    return () => {
      if (rafRef.current) {
        cancelAnimationFrame(rafRef.current);
      }
    };
  }, [min, max, duration, enabled]);

  return value;
}

// ============================================
// 滚动驱动动画
// ============================================

export function useScrollProgress(
  elementRef: React.RefObject<Element>,
  options: {
    start?: string;
    end?: string;
  } = {}
): number {
  const { start = 'top bottom', end = 'bottom top' } = options;
  const [progress, setProgress] = useState(0);

  useEffect(() => {
    const element = elementRef.current;
    if (!element) return;

    const handleScroll = () => {
      const rect = element.getBoundingClientRect();
      const windowHeight = window.innerHeight;

      // 解析 start 和 end
      const [startEdge, startContainer] = start.split(' ');
      const [endEdge, endContainer] = end.split(' ');

      const getEdgePosition = (edge: string, container: string) => {
        const containerPos = container === 'bottom' ? windowHeight : 0;
        const elementPos =
          edge === 'top' ? rect.top : edge === 'bottom' ? rect.bottom : rect.top + rect.height / 2;
        return elementPos - containerPos;
      };

      const startPos = getEdgePosition(startEdge, startContainer);
      const endPos = getEdgePosition(endEdge, endContainer);

      const scrollProgress = Math.max(0, Math.min(1, 1 - startPos / (startPos - endPos)));
      setProgress(scrollProgress);
    };

    window.addEventListener('scroll', handleScroll, { passive: true });
    handleScroll();

    return () => {
      window.removeEventListener('scroll', handleScroll);
    };
  }, [elementRef, start, end]);

  return progress;
}

// ============================================
// 手势动画
// ============================================

export function useGestureAnimation() {
  const [transform, setTransform] = useState({ x: 0, y: 0, scale: 1, rotate: 0 });
  const gestureState = useRef({
    startX: 0,
    startY: 0,
    startDistance: 0,
    currentX: 0,
    currentY: 0,
    currentScale: 1,
    currentRotate: 0,
  });

  const onTouchStart = useCallback((e: React.TouchEvent) => {
    if (e.touches.length === 1) {
      gestureState.current.startX = e.touches[0].clientX - gestureState.current.currentX;
      gestureState.current.startY = e.touches[0].clientY - gestureState.current.currentY;
    } else if (e.touches.length === 2) {
      const dx = e.touches[0].clientX - e.touches[1].clientX;
      const dy = e.touches[0].clientY - e.touches[1].clientY;
      gestureState.current.startDistance = Math.sqrt(dx * dx + dy * dy);
    }
  }, []);

  const onTouchMove = useCallback((e: React.TouchEvent) => {
    e.preventDefault();

    if (e.touches.length === 1) {
      gestureState.current.currentX = e.touches[0].clientX - gestureState.current.startX;
      gestureState.current.currentY = e.touches[0].clientY - gestureState.current.startY;
    } else if (e.touches.length === 2) {
      const dx = e.touches[0].clientX - e.touches[1].clientX;
      const dy = e.touches[0].clientY - e.touches[1].clientY;
      const distance = Math.sqrt(dx * dx + dy * dy);
      const scale = (distance / gestureState.current.startDistance) * gestureState.current.currentScale;
      gestureState.current.currentScale = Math.max(0.5, Math.min(3, scale));
    }

    setTransform({
      x: gestureState.current.currentX,
      y: gestureState.current.currentY,
      scale: gestureState.current.currentScale,
      rotate: gestureState.current.currentRotate,
    });
  }, []);

  const onTouchEnd = useCallback(() => {
    gestureState.current.currentX = transform.x;
    gestureState.current.currentY = transform.y;
    gestureState.current.currentScale = transform.scale;
  }, [transform]);

  const reset = useCallback(() => {
    gestureState.current = {
      startX: 0,
      startY: 0,
      startDistance: 0,
      currentX: 0,
      currentY: 0,
      currentScale: 1,
      currentRotate: 0,
    };
    setTransform({ x: 0, y: 0, scale: 1, rotate: 0 });
  }, []);

  return {
    transform,
    onTouchStart,
    onTouchMove,
    onTouchEnd,
    reset,
  };
}

// ============================================
// 页面过渡
// ============================================

export function usePageTransition(
  isActive: boolean,
  config: TransitionConfig = {}
): React.CSSProperties {
  const { type = 'tween', duration = 300, delay = 0, ease = 'easeOut' } = config;
  const [style, setStyle] = useState<React.CSSProperties>({
    opacity: 0,
    transform: 'translateY(20px)',
  });

  useEffect(() => {
    const timer = setTimeout(() => {
      if (isActive) {
        setStyle({
          opacity: 1,
          transform: 'translateY(0)',
          transition: `all ${duration}ms ${ease} ${delay}ms`,
        });
      } else {
        setStyle({
          opacity: 0,
          transform: 'translateY(-20px)',
          transition: `all ${duration}ms ${ease}`,
        });
      }
    }, 10);

    return () => clearTimeout(timer);
  }, [isActive, type, duration, delay, ease]);

  return style;
}

// ============================================
// 计数动画
// ============================================

export function useCountUp(
  endValue: number,
  config: {
    duration?: number;
    startValue?: number;
    decimals?: number;
    suffix?: string;
    prefix?: string;
  } = {}
): string {
  const { duration = 1000, startValue = 0, decimals = 0, suffix = '', prefix = '' } = config;
  const [displayValue, setDisplayValue] = useState(startValue);
  const rafRef = useRef<number | null>(null);

  useEffect(() => {
    const startTime = performance.now();
    const diff = endValue - startValue;

    const animate = (timestamp: number) => {
      const elapsed = timestamp - startTime;
      const progress = Math.min(elapsed / duration, 1);
      const easedProgress = easings.easeOutQuart(progress);
      const currentValue = startValue + diff * easedProgress;

      setDisplayValue(currentValue);

      if (progress < 1) {
        rafRef.current = requestAnimationFrame(animate);
      }
    };

    rafRef.current = requestAnimationFrame(animate);

    return () => {
      if (rafRef.current) {
        cancelAnimationFrame(rafRef.current);
      }
    };
  }, [endValue, duration, startValue]);

  return `${prefix}${displayValue.toFixed(decimals)}${suffix}`;
}

export default {
  useAnimation,
  useSpring,
  useAnimatedValue,
  useStaggeredAnimation,
  usePulse,
  useScrollProgress,
  useGestureAnimation,
  usePageTransition,
  useCountUp,
  easings,
};
