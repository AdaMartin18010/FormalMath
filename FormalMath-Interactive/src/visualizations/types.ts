/**
 * 知识图谱可视化组件类型定义
 * FormalMath Interactive - Visualization Types v2.0
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
// ConceptTimeline 概念演化时间线类型
// ============================================

export interface TimelineEvent {
  id: string;
  date: Date;
  year: number;
  title: string;
  description: string;
  type: 'discovery' | 'proof' | 'publication' | 'application' | 'extension';
  mathematician?: string;
  conceptId: string;
  impact: number;
  references?: string[];
}

export interface ConceptStage {
  id: string;
  conceptId: string;
  name: string;
  startDate: Date;
  endDate?: Date;
  description: string;
  maturity: 'nascent' | 'developing' | 'mature' | 'refined';
  keyContributors: string[];
}

export interface ConceptTimelineProps {
  events: TimelineEvent[];
  stages?: ConceptStage[];
  width?: number;
  height?: number;
  className?: string;
  autoPlay?: boolean;
  onEventClick?: (event: TimelineEvent) => void;
  onStageClick?: (stage: ConceptStage) => void;
  highlightedConcepts?: string[];
}

// ============================================
// GraphComparison 知识图谱对比类型
// ============================================

export type ComparisonMode = 'side-by-side' | 'overlay' | 'diff' | 'merge';

export interface NodeMatch {
  nodeA?: GraphNode;
  nodeB?: GraphNode;
  similarity: number;
  type: 'match' | 'only-in-a' | 'only-in-b' | 'modified';
}

export interface ComparisonStats {
  commonNodes: number;
  onlyInA: number;
  onlyInB: number;
  modifiedNodes: number;
  commonEdges: number;
  onlyEdgesInA: number;
  onlyEdgesInB: number;
  similarityScore: number;
}

export interface GraphComparisonProps {
  graphA: { nodes: GraphNode[]; edges: GraphLink[] };
  graphB: { nodes: GraphNode[]; edges: GraphLink[] };
  titleA?: string;
  titleB?: string;
  width?: number;
  height?: number;
  className?: string;
  mode?: ComparisonMode;
  onNodeClick?: (match: NodeMatch) => void;
  onModeChange?: (mode: ComparisonMode) => void;
  showStats?: boolean;
  showLegend?: boolean;
}

// ============================================
// PathAnimation 学习路径动画类型
// ============================================

export interface PathNode {
  id: string;
  conceptId: string;
  label: string;
  description?: string;
  x: number;
  y: number;
  status: 'locked' | 'available' | 'in_progress' | 'completed' | 'recommended';
  mastery: number;
  difficulty: number;
  estimatedTime: number;
  prerequisites: string[];
  rewards?: string[];
  isMilestone?: boolean;
  isShortcut?: boolean;
}

export interface PathConnection {
  from: string;
  to: string;
  type: 'required' | 'recommended' | 'shortcut';
  strength?: number;
}

export interface PathEvent {
  timestamp: number;
  type: 'start' | 'complete' | 'unlock' | 'recommend' | 'milestone';
  nodeId: string;
  message: string;
}

export interface PathAnimationProps {
  nodes: PathNode[];
  connections: PathConnection[];
  width?: number;
  height?: number;
  className?: string;
  autoPlay?: boolean;
  playbackSpeed?: number;
  showParticles?: boolean;
  showHeatmap?: boolean;
  onNodeClick?: (node: PathNode) => void;
  onAnimationComplete?: () => void;
}

// ============================================
// ProofTreeViz 定理证明树类型
// ============================================

export type ProofNodeType = 'theorem' | 'lemma' | 'axiom' | 'assumption' | 'conclusion' | 'contradiction';

export type ProofStatus = 'proven' | 'unproven' | 'pending' | 'invalid' | 'axiomatic';

export interface ProofNode {
  id: string;
  label: string;
  type: ProofNodeType;
  status: ProofStatus;
  statement: string;
  proof?: string;
  children?: ProofNode[];
  parentId?: string;
  depth: number;
  confidence?: number;
  usedAxioms?: string[];
  usedLemmas?: string[];
  isExpanded?: boolean;
  metadata?: {
    author?: string;
    date?: string;
    complexity?: number;
  };
}

export interface ProofStep {
  id: string;
  stepNumber: number;
  description: string;
  justification: string;
  dependsOn?: string[];
  produces?: string;
}

export interface ProofTreeVizProps {
  root: ProofNode;
  width?: number;
  height?: number;
  className?: string;
  orientation?: 'vertical' | 'horizontal';
  onNodeClick?: (node: ProofNode) => void;
  onNodeExpand?: (node: ProofNode, expanded: boolean) => void;
  showStepByStep?: boolean;
  interactive?: boolean;
}

// ============================================
// AssociationHeatmap 概念关联热力图类型
// ============================================

export interface AssociationData {
  concepts: string[];
  matrix: number[][];
  metadata?: {
    conceptCategories?: Record<string, string>;
    conceptDescriptions?: Record<string, string>;
  };
}

export interface ClusterResult {
  id: number;
  concepts: string[];
  centroid: number[];
  color: string;
}

export type HeatmapMode = 'matrix' | 'clustered' | 'network' | 'circular';

export interface AssociationHeatmapProps {
  data: AssociationData;
  width?: number;
  height?: number;
  className?: string;
  mode?: HeatmapMode;
  onCellClick?: (conceptA: string, conceptB: string, strength: number) => void;
  onModeChange?: (mode: HeatmapMode) => void;
  showColorScale?: boolean;
  enableClustering?: boolean;
  threshold?: number;
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

export interface GraphData {
  nodes: GraphNode[];
  edges: GraphLink[];
}

export type GraphEdge = GraphLink;
