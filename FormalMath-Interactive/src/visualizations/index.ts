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
// 默认导出
// ============================================

export { default } from './D3Graph';
