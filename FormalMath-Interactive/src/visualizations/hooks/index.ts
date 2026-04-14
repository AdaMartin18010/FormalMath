// @ts-nocheck
/**
 * FormalMath 可视化 Hooks 索引
 * 统一导出所有可视化相关的 Hooks
 */

// 性能优化 Hooks
export {
  useFPSMonitor,
  useThrottle,
  useDebounce,
  useRAFThrottle,
  useMemoryOptimizer,
  usePerformanceMonitor,
  useBatchedUpdates,
  useLazyCalculation,
  useVirtualization,
  useVisibilityObserver,
  useMemoryLeakDetector,
} from './usePerformance';

export type {
  PerformanceMetrics,
  ThrottleOptions,
  DebounceOptions,
  VirtualizationConfig,
  VirtualizationResult,
} from './usePerformance';

// 动画优化 Hooks
export {
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
} from './useOptimizedAnimation';

export type {
  AnimationConfig,
  SpringConfig,
  TransitionConfig,
} from './useOptimizedAnimation';

// 默认导出
export { default } from './usePerformance';
