/**
 * FormalMath Interactive - 可视化组件库
 * Knowledge Graph Visualization Components
 * 
 * @packageDocumentation
 */

// 类型定义
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
  
  // 通用类型
  Point,
  Bounds,
  TooltipState,
  VisualizationTheme
} from './types';

// 组件
export { D3Graph } from './D3Graph';
export { Graph3D } from './Graph3D';
export { InteractiveTree } from './InteractiveTree';
export { MatrixTable } from './MatrixTable';
export { MermaidChart } from './MermaidChart';

// 默认导出
export { default } from './D3Graph';
