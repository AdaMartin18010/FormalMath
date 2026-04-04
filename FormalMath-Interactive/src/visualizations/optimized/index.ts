/**
 * FormalMath 优化可视化组件库 v3.0
 * Optimized Visualization Components
 * 
 * @packageDocumentation
 * 
 * 优化特性:
 * - 虚拟滚动支持 (大量节点)
 * - Web Worker 计算
 * - RAF 节流渲染
 * - InstancedMesh 批量渲染
 * - 内存池复用
 * - 主题系统支持
 * - 无障碍优化
 * - 性能监控
 */

// ============================================
// 优化版可视化组件
// ============================================

export { OptimizedD3Graph } from './OptimizedD3Graph';
export { OptimizedGraph3D } from './OptimizedGraph3D';

// ============================================
// 性能优化 Hooks
// ============================================

export {
  // 性能监控
  useFPSMonitor,
  usePerformanceMonitor,
  useMemoryOptimizer,
  useMemoryLeakDetector,
  
  // 渲染优化
  useThrottle,
  useDebounce,
  useRAFThrottle,
  useBatchedUpdates,
  useLazyCalculation,
  
  // 虚拟化
  useVirtualization,
  useVisibilityObserver,
} from '../hooks';

// ============================================
// 动画优化 Hooks
// ============================================

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
} from '../hooks';

// ============================================
// 主题系统
// ============================================

export {
  // 主题
  lightTheme,
  darkTheme,
  highContrastTheme,
  colorBlindTheme,
  themes,
  
  // 工具函数
  getTheme,
  applyTheme,
  getNodeColor,
  getEdgeColor,
  adjustOpacity,
  getContrastColor,
} from '../themes';

export type {
  // 主题类型
  VisualizationTheme,
  ColorPalette,
  NodeTypeColors,
  EdgeTypeColors,
  Typography,
  Spacing,
  Shadow,
  BorderRadius,
  Animation,
  ThemeName,
} from '../themes';

// ============================================
// 类型定义
// ============================================

export type {
  // 性能类型
  PerformanceMetrics,
  ThrottleOptions,
  DebounceOptions,
  VirtualizationConfig,
  VirtualizationResult,
  
  // 动画类型
  AnimationConfig,
  SpringConfig,
  TransitionConfig,
} from '../hooks';

// ============================================
// 默认导出
// ============================================

export { OptimizedD3Graph as default } from './OptimizedD3Graph';
