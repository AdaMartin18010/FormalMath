/**
 * 知识图谱可视化组件类型定义
 * FormalMath Interactive - Visualization Types
 */

// ============================================
// D3Graph 力导向图类型
// ============================================

export interface GraphNode {
  id: string;
  label: string;
  type?: 'concept' | 'theorem' | 'proof' | 'example' | 'application' | 'person';
  size?: number;
  color?: string;
  x?: number;
  y?: number;
  fx?: number | null;
  fy?: number | null;
  vx?: number;
  vy?: number;
  index?: number;
  data?: Record<string, unknown>;
}

export interface GraphLink {
  id?: string;
  source: string | GraphNode;
  target: string | GraphNode;
  type?: 'depends' | 'relates' | 'proves' | 'applies' | 'references';
  strength?: number;
  color?: string;
  data?: Record<string, unknown>;
}

export interface D3GraphProps {
  nodes: GraphNode[];
  links: GraphLink[];
  width?: number;
  height?: number;
  className?: string;
  onNodeClick?: (node: GraphNode) => void;
  onNodeHover?: (node: GraphNode | null) => void;
  onLinkClick?: (link: GraphLink) => void;
  nodeRadius?: number;
  linkDistance?: number;
  chargeStrength?: number;
  enableZoom?: boolean;
  enableDrag?: boolean;
  highlightNode?: string | null;
  searchQuery?: string;
}

// ============================================
// InteractiveTree 交互式树类型
// ============================================

export interface TreeNode {
  id: string;
  label: string;
  description?: string;
  expanded?: boolean;
  children?: TreeNode[];
  data?: Record<string, unknown>;
  color?: string;
  icon?: string;
  disabled?: boolean;
}

export interface InteractiveTreeProps {
  data: TreeNode;
  width?: number;
  height?: number;
  orientation?: 'vertical' | 'horizontal';
  collapsible?: boolean;
  className?: string;
  onNodeClick?: (node: TreeNode) => void;
  onNodeToggle?: (node: TreeNode, expanded: boolean) => void;
  onNodeHover?: (node: TreeNode | null) => void;
  nodeSpacing?: { x: number; y: number };
  duration?: number;
  highlightPath?: string[];
  selectedNode?: string | null;
}

// ============================================
// MatrixTable 矩阵对比类型
// ============================================

export interface MatrixCell {
  value: number | string | boolean | null;
  label?: string;
  color?: string;
  tooltip?: string;
  data?: Record<string, unknown>;
  rowSpan?: number;
  colSpan?: number;
}

export interface ColorScale {
  type: 'sequential' | 'diverging' | 'categorical' | 'custom';
  domain?: [number, number] | number[];
  range?: string[];
  interpolate?: string;
  customMap?: Record<string | number, string>;
}

export interface MatrixTableProps {
  headers: string[];
  rowHeaders: string[];
  data: MatrixCell[][];
  colorScale?: ColorScale;
  className?: string;
  sortable?: boolean;
  filterable?: boolean;
  onCellClick?: (cell: MatrixCell, row: number, col: number) => void;
  onCellHover?: (cell: MatrixCell | null, row: number, col: number) => void;
  cellSize?: { width: number; height: number };
  showValues?: boolean;
  emptyValue?: string;
}

export interface MatrixSortConfig {
  column: number | null;
  direction: 'asc' | 'desc';
}

// ============================================
// MermaidChart Mermaid图表类型
// ============================================

export interface MermaidChartProps {
  chart: string;
  interactive?: boolean;
  className?: string;
  width?: number;
  height?: number;
  theme?: 'default' | 'forest' | 'dark' | 'neutral' | 'base';
  onNodeClick?: (nodeId: string, nodeData: Record<string, unknown>) => void;
  onError?: (error: Error) => void;
  enableZoom?: boolean;
  enablePan?: boolean;
}

// ============================================
// 通用类型
// ============================================

export interface Point {
  x: number;
  y: number;
}

export interface Bounds {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface TooltipState {
  visible: boolean;
  x: number;
  y: number;
  content: React.ReactNode;
}

export type VisualizationTheme = {
  colors: {
    primary: string;
    secondary: string;
    accent: string;
    background: string;
    surface: string;
    text: string;
    textMuted: string;
    border: string;
    success: string;
    warning: string;
    error: string;
  };
  nodeColors: Record<string, string>;
  linkColors: Record<string, string>;
  fontFamily: string;
  fontSize: {
    small: number;
    medium: number;
    large: number;
  };
};

// D3 Simulation 类型扩展
declare module 'd3' {
  interface Simulation<NodeDatum extends GraphNode, LinkDatum extends GraphLink> {
    stop(): this;
    restart(): this;
    tick(): void;
    on(type: string, listener: (event: any) => void): this;
  }
}
