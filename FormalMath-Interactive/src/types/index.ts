// @ts-nocheck
// ==================== 核心类型定义 ====================

// 节点类型
export type NodeType = 'concept' | 'theorem' | 'proof' | 'example' | 'application' | 'mathematician';

// 边类型
export type EdgeType = 'depends_on' | 'proves' | 'uses' | 'extends' | 'contradicts' | 'influences';

// 节点状态
export type NodeStatus = 'discovered' | 'verified' | 'contested' | 'deprecated';

// 基础节点接口
export interface GraphNode {
  id: string;
  label: string;
  type: NodeType;
  status: NodeStatus;
  description?: string;
  metadata?: Record<string, unknown>;
  x?: number;
  y?: number;
  radius?: number;
  color?: string;
  importance?: number; // 0-1 重要性分数
}

// 基础边接口
export interface GraphEdge {
  id: string;
  source: string;
  target: string;
  type: EdgeType;
  label?: string;
  weight?: number;
  directed?: boolean;
}

// 图数据接口
export interface GraphData {
  nodes: GraphNode[];
  edges: GraphEdge[];
}

// 知识图谱数据
export interface KnowledgeGraphData extends GraphData {
  domains?: string[];
  timeRange?: { start: number; end: number };
}

// 推理树节点
export interface ReasoningNode extends GraphNode {
  premises: string[];
  conclusion: string;
  proofSteps: ProofStep[];
  confidence: number;
  depth: number;
}

// 证明步骤
export interface ProofStep {
  id: string;
  stepNumber: number;
  statement: string;
  justification: string;
  references: string[];
  substeps?: ProofStep[];
}

// 思维导图节点
export interface MindMapNode {
  id: string;
  text: string;
  children?: MindMapNode[];
  collapsed?: boolean;
  style?: NodeStyle;
}

// 节点样式
export interface NodeStyle {
  backgroundColor?: string;
  borderColor?: string;
  textColor?: string;
  fontSize?: number;
  shape?: 'rectangle' | 'rounded' | 'ellipse' | 'diamond';
}

// 对比数据
export interface ComparisonData {
  id: string;
  title: string;
  items: ComparisonItem[];
  criteria: ComparisonCriteria[];
  matrix: ComparisonMatrix;
}

export interface ComparisonItem {
  id: string;
  name: string;
  description?: string;
  properties: Record<string, string | number | boolean>;
}

export interface ComparisonCriteria {
  id: string;
  name: string;
  weight: number;
  description?: string;
}

export interface ComparisonMatrix {
  rows: string[];
  cols: string[];
  values: (number | string | boolean)[][];
}

// 决策树
export interface DecisionTreeNode {
  id: string;
  question: string;
  condition?: string;
  yesBranch?: DecisionTreeNode;
  noBranch?: DecisionTreeNode;
  result?: string;
  probability?: number;
}

// 演化数据
export interface EvolutionData {
  timeline: EvolutionEvent[];
  snapshots: EvolutionSnapshot[];
}

export interface EvolutionEvent {
  id: string;
  timestamp: number;
  type: 'creation' | 'modification' | 'merger' | 'split' | 'deletion';
  description: string;
  affectedNodes: string[];
  author?: string;
}

export interface EvolutionSnapshot {
  id: string;
  timestamp: number;
  label: string;
  graphData: GraphData;
  metrics: EvolutionMetrics;
}

export interface EvolutionMetrics {
  nodeCount: number;
  edgeCount: number;
  density: number;
  connectedComponents: number;
  averageDegree: number;
}

// API响应类型
export interface ApiResponse<T> {
  success: boolean;
  data?: T;
  error?: ApiError;
  meta?: ApiMeta;
}

export interface ApiError {
  code: string;
  message: string;
  details?: unknown;
}

export interface ApiMeta {
  page?: number;
  pageSize?: number;
  total?: number;
  timestamp: string;
}

// 视图配置
export interface ViewConfig {
  layout: 'force' | 'hierarchical' | 'circular' | 'grid';
  theme: 'light' | 'dark' | 'colorful';
  showLabels: boolean;
  labelSize: number;
  nodeSize: number;
  edgeWidth: number;
  animationEnabled: boolean;
  physicsEnabled: boolean;
}

// 搜索过滤器
export interface SearchFilter {
  query: string;
  nodeTypes?: NodeType[];
  dateRange?: { start: Date; end: Date };
  domains?: string[];
  status?: NodeStatus[];
  authors?: string[];
}

// 导出选项
export interface ExportOptions {
  format: 'png' | 'svg' | 'pdf' | 'json';
  width?: number;
  height?: number;
  background?: string;
  quality?: number;
}

// 用户偏好
export interface UserPreferences {
  language: 'zh' | 'en';
  theme: 'light' | 'dark' | 'system';
  autoSave: boolean;
  defaultView: ViewConfig;
  shortcuts: Record<string, string>;
}

// 组件通用Props
export interface BaseComponentProps {
  className?: string;
  style?: React.CSSProperties;
}

export interface LoadingProps extends BaseComponentProps {
  message?: string;
  size?: 'sm' | 'md' | 'lg';
}

export interface ErrorProps extends BaseComponentProps {
  error: Error | string;
  onRetry?: () => void;
}

// ==================== 协作类型重导出 ====================
export * from './collaboration';

// ==================== 学习类型重导出 ====================
export * from './learning';

// ==================== 游戏化类型重导出 ====================
export * from './gamification';

// ==================== 数据分析类型重导出 ====================
export * from './analytics';

// ==================== 证明助手类型重导出 ====================
export * from './proofAssistant';

// ==================== 练习系统类型重导出 ====================
export * from './exercise';

// ==================== 视频类型重导出 ====================
export * from './video';

// ==================== 社区类型重导出 ====================
export * from './community';
