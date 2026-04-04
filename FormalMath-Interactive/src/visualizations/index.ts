/**
 * FormalMath Interactive - 可视化组件库 v2.0
 * Knowledge Graph Visualization Components
 * 
 * @packageDocumentation
 */

// ============================================
// 类型定义
// ============================================

export type {
  // D3Graph 类型
  GraphNode,
  GraphLink,
  D3GraphProps,
  
  // InteractiveTree 类型
  TreeNode,
  InteractiveTreeProps,
  
  // MatrixTable 类型
  MatrixCell,
  ColorScale,
  MatrixTableProps,
  MatrixSortConfig,
  
  // MermaidChart 类型
  MermaidChartProps,
  
  // ConceptTimeline 类型
  TimelineEvent,
  ConceptStage,
  ConceptTimelineProps,
  
  // GraphComparison 类型
  ComparisonMode,
  NodeMatch,
  ComparisonStats,
  GraphComparisonProps,
  
  // PathAnimation 类型
  PathNode,
  PathConnection,
  PathEvent,
  PathAnimationProps,
  
  // ProofTreeViz 类型
  ProofNodeType,
  ProofStatus,
  ProofNode,
  ProofStep,
  ProofTreeVizProps,
  
  // AssociationHeatmap 类型
  AssociationData,
  ClusterResult,
  HeatmapMode,
  AssociationHeatmapProps,
  
  // 通用类型
  Point,
  Bounds,
  TooltipState,
  VisualizationTheme
} from './types';

// ============================================
// 基础可视化组件
// ============================================

export { D3Graph } from './D3Graph';
export { Graph3D } from './Graph3D';
export { InteractiveTree } from './InteractiveTree';
export { MatrixTable } from './MatrixTable';
export { MermaidChart } from './MermaidChart';

// ============================================
// 高级可视化组件 v2.0
// ============================================

export { ConceptTimeline } from './ConceptTimeline';
export { GraphComparison } from './GraphComparison';
export { PathAnimation } from './PathAnimation';
export { ProofTreeViz } from './ProofTreeViz';
export { AssociationHeatmap } from './AssociationHeatmap';

// ============================================
// 优化版可视化组件 v3.0
// ============================================

export {
  // 优化版组件
  OptimizedD3Graph,
  OptimizedGraph3D,
  
  // 性能优化 Hooks
  useFPSMonitor,
  useThrottle,
  useDebounce,
  useRAFThrottle,
  usePerformanceMonitor,
  useVirtualization,
  useVisibilityObserver,
  
  // 动画优化 Hooks
  useAnimation,
  useSpring,
  useAnimatedValue,
  useStaggeredAnimation,
  usePulse,
  easings,
  
  // 主题系统
  lightTheme,
  darkTheme,
  highContrastTheme,
  colorBlindTheme,
  themes,
  getTheme,
  applyTheme,
  getNodeColor,
  getEdgeColor,
} from './optimized';

export type {
  // 主题类型
  VisualizationTheme,
  ThemeName,
  
  // 性能类型
  PerformanceMetrics,
  VirtualizationConfig,
  VirtualizationResult,
  
  // 动画类型
  AnimationConfig,
  SpringConfig,
} from './optimized';

// ============================================
// 增强版组件 v4.0
// ============================================

export { EnhancedD3Graph } from './EnhancedD3Graph';

// ============================================
// 默认导出
// ============================================

export { default } from './D3Graph';
export { OptimizedD3Graph as OptimizedGraph } from './optimized';
export { EnhancedD3Graph as EnhancedGraph } from './EnhancedD3Graph';
