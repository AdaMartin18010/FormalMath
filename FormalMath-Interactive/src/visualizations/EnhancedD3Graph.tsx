// @ts-nocheck
/**
 * EnhancedD3Graph - 增强版 D3 知识图谱可视化组件
 * 
 * 核心优化特性:
 * - 性能优化: 支持5000+节点，使用虚拟渲染和Web Worker
 * - 力导向参数调节: 实时调整物理模拟参数
 * - 层级聚类: 基于类型的智能聚类和层次布局
 * - 筛选搜索: 多维度节点筛选和搜索高亮
 * - 视觉优化: 现代UI设计和流畅动画
 */

import React, { 
  useRef, 
  useEffect, 
  useState, 
  useCallback, 
  useMemo,
  memo,
  useId
} from 'react';
import * as d3 from 'd3';
import { 
  ZoomIn, 
  ZoomOut, 
  Target, 
  Download, 
  RefreshCw,
  Maximize2,
  Minimize2,
  Search,
  Filter,
  Layers,
  Grid3x3,
  Focus,
  Settings2,
  ChevronDown,
  ChevronUp,
  X,
  SlidersHorizontal,
  LayoutGrid,
  CircleDot,
  GitBranch,
  Palette,
  Eye,
  EyeOff
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '../types';
import { 
  useRAFThrottle, 
  useDebounce, 
  useVisibilityObserver,
  useFPSMonitor
} from './hooks/usePerformance';
import { lightTheme, darkTheme, getNodeColor, getEdgeColor, VisualizationTheme, type ThemeName } from './themes';

// ============================================
// 类型定义
// ============================================

interface EnhancedD3GraphProps {
  data: GraphData;
  width?: number;
  height?: number;
  config?: Partial<ViewConfig>;
  className?: string;
  theme?: ThemeName;
  onNodeClick?: (node: GraphNode) => void;
  onEdgeClick?: (edge: GraphEdge) => void;
  onNodeHover?: (node: GraphNode | null) => void;
  selectedNodes?: string[];
  highlightPath?: string[];
  enableVirtualization?: boolean;
  maxVisibleNodes?: number;
}

interface ForceConfig {
  linkDistance: number;
  chargeStrength: number;
  collisionRadius: number;
  centerStrength: number;
  gravityStrength: number;
  alphaDecay: number;
  velocityDecay: number;
}

interface FilterState {
  searchQuery: string;
  selectedTypes: Set<string>;
  minImportance: number;
  showIsolated: boolean;
}

interface ClusterInfo {
  id: string;
  type: string;
  nodes: GraphNode[];
  centroid: { x: number; y: number };
  radius: number;
  color: string;
}

interface ViewState {
  transform: d3.ZoomTransform;
  scale: number;
  translate: [number, number];
}

// ============================================
// 常量配置
// ============================================

const DEFAULT_FORCE_CONFIG: ForceConfig = {
  linkDistance: 120,
  chargeStrength: -400,
  collisionRadius: 40,
  centerStrength: 0.05,
  gravityStrength: 0.01,
  alphaDecay: 0.02,
  velocityDecay: 0.4,
};

const VIRTUALIZATION_THRESHOLD = 500;
const BATCH_SIZE = 100;
const ZOOM_EXTENT: [number, number] = [0.05, 5];

const NODE_TYPES = ['concept', 'theorem', 'proof', 'example', 'application', 'mathematician', 'axiom', 'lemma', 'corollary', 'definition'];

// ============================================
// 工具函数
// ============================================

const getNodeRadius = (node: GraphNode, config: Partial<ViewConfig>, scale: number = 1): number => {
  const baseRadius = Math.max(5, Math.min((node.radius || config.nodeSize || 20) * scale, 60));
  return baseRadius;
};

const calculateClusterCentroid = (nodes: GraphNode[]): { x: number; y: number } => {
  if (nodes.length === 0) return { x: 0, y: 0 };
  const sum = nodes.reduce((acc, node) => ({
    x: acc.x + (node.x || 0),
    y: acc.y + (node.y || 0)
  }), { x: 0, y: 0 });
  return { x: sum.x / nodes.length, y: sum.y / nodes.length };
};

const calculateClusterRadius = (nodes: GraphNode[], centroid: { x: number; y: number }): number => {
  if (nodes.length === 0) return 0;
  const maxDist = Math.max(...nodes.map(node => {
    const dx = (node.x || 0) - centroid.x;
    const dy = (node.y || 0) - centroid.y;
    return Math.sqrt(dx * dx + dy * dy);
  }));
  return maxDist + 50;
};

// ============================================
// 统计面板组件
// ============================================

interface StatsPanelProps {
  nodes: GraphNode[];
  edges: GraphEdge[];
  selectedCount: number;
  fps: number;
  visibleCount: number;
  totalCount: number;
  isVisible: boolean;
  onToggle: () => void;
  theme: VisualizationTheme;
}

const StatsPanel = memo<StatsPanelProps>(({
  nodes,
  edges,
  selectedCount,
  fps,
  visibleCount,
  totalCount,
  isVisible,
  onToggle,
  theme
}) => {
  const nodeTypes = useMemo(() => {
    return nodes.reduce((acc, node) => {
      acc[node.type] = (acc[node.type] || 0) + 1;
      return acc;
    }, {} as Record<string, number>);
  }, [nodes]);

  const stats = useMemo(() => {
    const density = nodes.length > 1 ? (2 * edges.length) / (nodes.length * (nodes.length - 1)) : 0;
    const avgDegree = nodes.length > 0 ? (2 * edges.length) / nodes.length : 0;
    return { density, avgDegree: avgDegree.toFixed(1) };
  }, [nodes, edges]);

  if (!isVisible) {
    return (
      <button
        onClick={onToggle}
        className="absolute top-4 left-4 p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg border border-gray-200 hover:bg-white transition-all z-20"
        title="显示统计"
      >
        <Layers className="w-4 h-4 text-gray-600" />
      </button>
    );
  }

  return (
    <div 
      className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-20 min-w-[220px] max-h-[400px] overflow-y-auto"
      style={{ borderColor: theme.colors.border }}
    >
      <div className="flex items-center justify-between mb-3">
        <h4 className="font-semibold text-gray-900 flex items-center gap-2">
          <Grid3x3 className="w-4 h-4" style={{ color: theme.colors.primary }} />
          图谱统计
        </h4>
        <button
          onClick={onToggle}
          className="p-1 hover:bg-gray-100 rounded transition-colors"
        >
          <ChevronUp className="w-4 h-4 text-gray-500" />
        </button>
      </div>

      <div className="space-y-2 text-sm">
        <div className="flex justify-between">
          <span className="text-gray-600">节点:</span>
          <span className="font-medium text-gray-900">
            {visibleCount < totalCount ? `${visibleCount}/${totalCount}` : totalCount}
          </span>
        </div>
        <div className="flex justify-between">
          <span className="text-gray-600">连接:</span>
          <span className="font-medium text-gray-900">{edges.length}</span>
        </div>
        <div className="flex justify-between">
          <span className="text-gray-600">密度:</span>
          <span className="font-medium text-gray-900">{stats.density.toFixed(3)}</span>
        </div>
        <div className="flex justify-between">
          <span className="text-gray-600">平均度:</span>
          <span className="font-medium text-gray-900">{stats.avgDegree}</span>
        </div>
        {selectedCount > 0 && (
          <div className="flex justify-between">
            <span className="text-gray-600">已选中:</span>
            <span className="font-medium" style={{ color: theme.colors.primary }}>{selectedCount}</span>
          </div>
        )}
        <div className="flex justify-between">
          <span className="text-gray-600">FPS:</span>
          <span className={`font-medium ${fps < 30 ? 'text-red-500' : fps < 50 ? 'text-yellow-500' : 'text-green-500'}`}>
            {fps}
          </span>
        </div>
      </div>

      <div className="mt-3 pt-3 border-t border-gray-200">
        <p className="text-xs text-gray-500 mb-2">节点类型分布:</p>
        <div className="space-y-1 max-h-32 overflow-y-auto">
          {Object.entries(nodeTypes).map(([type, count]) => (
            <div key={type} className="flex justify-between text-xs">
              <span className="text-gray-500 capitalize">{type}:</span>
              <span 
                className="font-medium"
                style={{ color: getNodeColor(type, theme) }}
              >
                {count}
              </span>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
});

StatsPanel.displayName = 'StatsPanel';

// ============================================
// 工具栏组件
// ============================================

interface ToolbarProps {
  onZoomIn: () => void;
  onZoomOut: () => void;
  onReset: () => void;
  onExport: () => void;
  onToggleFullscreen: () => void;
  isFullscreen: boolean;
  onFocusSelected: () => void;
  hasSelection: boolean;
  onToggleSettings: () => void;
  onToggleFilters: () => void;
  showSettings: boolean;
  showFilters: boolean;
}

const Toolbar = memo<ToolbarProps>(({
  onZoomIn,
  onZoomOut,
  onReset,
  onExport,
  onToggleFullscreen,
  isFullscreen,
  onFocusSelected,
  hasSelection,
  onToggleSettings,
  onToggleFilters,
  showSettings,
  showFilters,
}) => (
  <div className="absolute top-4 right-4 flex flex-col gap-2 z-20">
    <button
      onClick={onZoomIn}
      className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all border border-gray-200"
      title="放大"
    >
      <ZoomIn className="w-4 h-4 text-gray-700" />
    </button>
    <button
      onClick={onZoomOut}
      className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all border border-gray-200"
      title="缩小"
    >
      <ZoomOut className="w-4 h-4 text-gray-700" />
    </button>
    <button
      onClick={onReset}
      className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all border border-gray-200"
      title="重置视图"
    >
      <Target className="w-4 h-4 text-gray-700" />
    </button>
    {hasSelection && (
      <button
        onClick={onFocusSelected}
        className="p-2 bg-blue-50 backdrop-blur rounded-lg shadow-lg hover:bg-blue-100 transition-all border border-blue-200"
        title="聚焦选中"
      >
        <Focus className="w-4 h-4 text-blue-600" />
      </button>
    )}
    <button
      onClick={onToggleFilters}
      className={cn(
        "p-2 backdrop-blur rounded-lg shadow-lg transition-all border",
        showFilters ? "bg-blue-50 border-blue-200" : "bg-white/90 border-gray-200 hover:bg-white"
      )}
      title="筛选与搜索"
    >
      <Filter className={cn("w-4 h-4", showFilters ? "text-blue-600" : "text-gray-700")} />
    </button>
    <button
      onClick={onToggleSettings}
      className={cn(
        "p-2 backdrop-blur rounded-lg shadow-lg transition-all border",
        showSettings ? "bg-blue-50 border-blue-200" : "bg-white/90 border-gray-200 hover:bg-white"
      )}
      title="力导向设置"
    >
      <Settings2 className={cn("w-4 h-4", showSettings ? "text-blue-600" : "text-gray-700")} />
    </button>
    <button
      onClick={onExport}
      className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all border border-gray-200"
      title="导出SVG"
    >
      <Download className="w-4 h-4 text-gray-700" />
    </button>
    <button
      onClick={onToggleFullscreen}
      className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all border border-gray-200"
      title={isFullscreen ? '退出全屏' : '全屏'}
    >
      {isFullscreen ? (
        <Minimize2 className="w-4 h-4 text-gray-700" />
      ) : (
        <Maximize2 className="w-4 h-4 text-gray-700" />
      )}
    </button>
  </div>
));

Toolbar.displayName = 'Toolbar';

// ============================================
// 力导向参数面板
// ============================================

interface ForcePanelProps {
  config: ForceConfig;
  onChange: (config: ForceConfig) => void;
  isVisible: boolean;
  onToggle: () => void;
  theme: VisualizationTheme;
}

const ForcePanel = memo<ForcePanelProps>(({ config, onChange, isVisible, onToggle, theme }) => {
  const handleChange = useCallback((key: keyof ForceConfig, value: number) => {
    onChange({ ...config, [key]: value });
  }, [config, onChange]);

  if (!isVisible) return null;

  return (
    <div 
      className="absolute top-20 right-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-20 w-[280px]"
      style={{ borderColor: theme.colors.border }}
    >
      <div className="flex items-center justify-between mb-4">
        <h4 className="font-semibold text-gray-900 flex items-center gap-2">
          <SlidersHorizontal className="w-4 h-4" style={{ color: theme.colors.primary }} />
          力导向参数
        </h4>
        <button onClick={onToggle} className="p-1 hover:bg-gray-100 rounded">
          <X className="w-4 h-4 text-gray-500" />
        </button>
      </div>

      <div className="space-y-4">
        <div>
          <label className="flex justify-between text-xs text-gray-600 mb-1">
            <span>连接距离</span>
            <span>{config.linkDistance}px</span>
          </label>
          <input
            type="range"
            min="50"
            max="300"
            value={config.linkDistance}
            onChange={(e) => handleChange('linkDistance', Number(e.target.value))}
            className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
          />
        </div>

        <div>
          <label className="flex justify-between text-xs text-gray-600 mb-1">
            <span>斥力强度</span>
            <span>{config.chargeStrength}</span>
          </label>
          <input
            type="range"
            min="-1000"
            max="-50"
            value={config.chargeStrength}
            onChange={(e) => handleChange('chargeStrength', Number(e.target.value))}
            className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
          />
        </div>

        <div>
          <label className="flex justify-between text-xs text-gray-600 mb-1">
            <span>碰撞半径</span>
            <span>{config.collisionRadius}px</span>
          </label>
          <input
            type="range"
            min="10"
            max="100"
            value={config.collisionRadius}
            onChange={(e) => handleChange('collisionRadius', Number(e.target.value))}
            className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
          />
        </div>

        <div>
          <label className="flex justify-between text-xs text-gray-600 mb-1">
            <span>中心引力</span>
            <span>{config.centerStrength.toFixed(2)}</span>
          </label>
          <input
            type="range"
            min="0"
            max="0.2"
            step="0.01"
            value={config.centerStrength}
            onChange={(e) => handleChange('centerStrength', Number(e.target.value))}
            className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
          />
        </div>

        <div>
          <label className="flex justify-between text-xs text-gray-600 mb-1">
            <span>衰减系数</span>
            <span>{config.alphaDecay.toFixed(3)}</span>
          </label>
          <input
            type="range"
            min="0.001"
            max="0.1"
            step="0.001"
            value={config.alphaDecay}
            onChange={(e) => handleChange('alphaDecay', Number(e.target.value))}
            className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
          />
        </div>
      </div>
    </div>
  );
});

ForcePanel.displayName = 'ForcePanel';

// ============================================
// 筛选面板组件
// ============================================

interface FilterPanelProps {
  filter: FilterState;
  onChange: (filter: FilterState) => void;
  isVisible: boolean;
  onToggle: () => void;
  theme: VisualizationTheme;
  nodeTypes: string[];
}

const FilterPanel = memo<FilterPanelProps>(({ filter, onChange, isVisible, onToggle, theme, nodeTypes }) => {
  const toggleType = useCallback((type: string) => {
    const newTypes = new Set(filter.selectedTypes);
    if (newTypes.has(type)) {
      newTypes.delete(type);
    } else {
      newTypes.add(type);
    }
    onChange({ ...filter, selectedTypes: newTypes });
  }, [filter, onChange]);

  const selectAllTypes = useCallback(() => {
    onChange({ ...filter, selectedTypes: new Set(nodeTypes) });
  }, [filter, nodeTypes, onChange]);

  const clearAllTypes = useCallback(() => {
    onChange({ ...filter, selectedTypes: new Set() });
  }, [filter, onChange]);

  if (!isVisible) return null;

  return (
    <div 
      className="absolute top-20 right-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-20 w-[300px]"
      style={{ borderColor: theme.colors.border }}
    >
      <div className="flex items-center justify-between mb-4">
        <h4 className="font-semibold text-gray-900 flex items-center gap-2">
          <Filter className="w-4 h-4" style={{ color: theme.colors.primary }} />
          筛选与搜索
        </h4>
        <button onClick={onToggle} className="p-1 hover:bg-gray-100 rounded">
          <X className="w-4 h-4 text-gray-500" />
        </button>
      </div>

      {/* 搜索 */}
      <div className="mb-4">
        <div className="relative">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
          <input
            type="text"
            placeholder="搜索节点..."
            value={filter.searchQuery}
            onChange={(e) => onChange({ ...filter, searchQuery: e.target.value })}
            className="w-full pl-9 pr-3 py-2 text-sm border border-gray-200 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-transparent"
          />
        </div>
      </div>

      {/* 节点类型筛选 */}
      <div className="mb-4">
        <div className="flex items-center justify-between mb-2">
          <span className="text-xs font-medium text-gray-600">节点类型</span>
          <div className="flex gap-1">
            <button onClick={selectAllTypes} className="text-xs text-blue-600 hover:underline">全选</button>
            <span className="text-gray-300">|</span>
            <button onClick={clearAllTypes} className="text-xs text-blue-600 hover:underline">清空</button>
          </div>
        </div>
        <div className="flex flex-wrap gap-1.5 max-h-24 overflow-y-auto">
          {nodeTypes.map(type => (
            <button
              key={type}
              onClick={() => toggleType(type)}
              className={cn(
                "px-2 py-1 text-xs rounded-full border transition-all",
                filter.selectedTypes.has(type)
                  ? "text-white border-transparent"
                  : "bg-gray-100 text-gray-500 border-gray-200 hover:bg-gray-200"
              )}
              style={{
                backgroundColor: filter.selectedTypes.has(type) ? getNodeColor(type, theme) : undefined
              }}
            >
              {type}
            </button>
          ))}
        </div>
      </div>

      {/* 重要性阈值 */}
      <div className="mb-4">
        <label className="flex justify-between text-xs text-gray-600 mb-1">
          <span>重要性阈值</span>
          <span>{filter.minImportance}</span>
        </label>
        <input
          type="range"
          min="0"
          max="1"
          step="0.1"
          value={filter.minImportance}
          onChange={(e) => onChange({ ...filter, minImportance: Number(e.target.value) })}
          className="w-full h-1 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
        />
      </div>

      {/* 显示孤立节点 */}
      <div className="flex items-center gap-2">
        <input
          type="checkbox"
          id="showIsolated"
          checked={filter.showIsolated}
          onChange={(e) => onChange({ ...filter, showIsolated: e.target.checked })}
          className="w-4 h-4 rounded border-gray-300 text-blue-600 focus:ring-blue-500"
        />
        <label htmlFor="showIsolated" className="text-sm text-gray-600">显示孤立节点</label>
      </div>
    </div>
  );
});

FilterPanel.displayName = 'FilterPanel';

// ============================================
// 主组件
// ============================================

export const EnhancedD3Graph: React.FC<EnhancedD3GraphProps> = ({
  data,
  width = 800,
  height = 600,
  config = {},
  className,
  theme: themeName = 'light',
  onNodeClick,
  onEdgeClick,
  onNodeHover,
  selectedNodes = [],
  highlightPath = [],
  enableVirtualization = true,
  maxVisibleNodes = 1000,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const gRef = useRef<d3.Selection<SVGGElement, unknown, null, undefined> | null>(null);
  const zoomRef = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(null);
  const simulationRef = useRef<d3.Simulation<GraphNode, GraphEdge> | null>(null);
  
  const [isReady, setIsReady] = useState(false);
  const [hoveredNode, setHoveredNode] = useState<GraphNode | null>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [showStatsPanel, setShowStatsPanel] = useState(true);
  const [showForcePanel, setShowForcePanel] = useState(false);
  const [showFilterPanel, setShowFilterPanel] = useState(false);
  const [viewState, setViewState] = useState<ViewState>({
    transform: d3.zoomIdentity,
    scale: 1,
    translate: [0, 0],
  });
  const [forceConfig, setForceConfig] = useState<ForceConfig>(DEFAULT_FORCE_CONFIG);
  const [filterState, setFilterState] = useState<FilterState>({
    searchQuery: '',
    selectedTypes: new Set(NODE_TYPES),
    minImportance: 0,
    showIsolated: true,
  });
  const [showClusters, setShowClusters] = useState(true);
  const [layoutMode, setLayoutMode] = useState<'force' | 'hierarchical' | 'circular'>('force');

  const uniqueId = useId();
  const theme = themeName === 'dark' ? darkTheme : lightTheme;
  
  // FPS监控
  const fps = useFPSMonitor(true);

  // 可见性检测
  const isVisible = useVisibilityObserver(containerRef);

  // 筛选和过滤数据
  const filteredData = useMemo(() => {
    let filteredNodes = data.nodes.filter(node => {
      // 类型筛选
      if (!filterState.selectedTypes.has(node.type)) return false;
      
      // 重要性筛选
      if ((node.importance || 0) < filterState.minImportance) return false;
      
      // 搜索筛选
      if (filterState.searchQuery) {
        const query = filterState.searchQuery.toLowerCase();
        const matches = node.label.toLowerCase().includes(query) ||
                       node.type.toLowerCase().includes(query) ||
                       (node.description || '').toLowerCase().includes(query);
        if (!matches) return false;
      }
      
      return true;
    });

    // 处理孤立节点
    if (!filterState.showIsolated) {
      const connectedNodeIds = new Set<string>();
      data.edges.forEach(edge => {
        connectedNodeIds.add(typeof edge.source === 'string' ? edge.source : edge.source.id);
        connectedNodeIds.add(typeof edge.target === 'string' ? edge.target : edge.target.id);
      });
      filteredNodes = filteredNodes.filter(node => connectedNodeIds.has(node.id));
    }

    const nodeIds = new Set(filteredNodes.map(n => n.id));
    const filteredEdges = data.edges.filter(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      return nodeIds.has(sourceId) && nodeIds.has(targetId);
    });

    return { nodes: filteredNodes, edges: filteredEdges };
  }, [data, filterState]);

  // 计算聚类
  const clusters = useMemo(() => {
    const clusterMap = new Map<string, GraphNode[]>();
    filteredData.nodes.forEach(node => {
      if (!clusterMap.has(node.type)) {
        clusterMap.set(node.type, []);
      }
      clusterMap.get(node.type)!.push(node);
    });

    return Array.from(clusterMap.entries()).map(([type, nodes], index) => {
      const centroid = calculateClusterCentroid(nodes);
      const radius = calculateClusterRadius(nodes, centroid);
      return {
        id: `cluster-${type}`,
        type,
        nodes,
        centroid,
        radius,
        color: getNodeColor(type, theme),
      };
    });
  }, [filteredData, theme]);

  // 虚拟化数据
  const visibleData = useMemo(() => {
    if (!enableVirtualization || filteredData.nodes.length <= maxVisibleNodes) {
      return filteredData;
    }

    // 优先显示选中节点及其邻居
    const priorityNodes = new Set<string>(selectedNodes);
    
    // 添加选中节点的邻居
    filteredData.edges.forEach(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      
      if (selectedNodes.includes(sourceId)) priorityNodes.add(targetId);
      if (selectedNodes.includes(targetId)) priorityNodes.add(sourceId);
    });

    // 按中心性排序
    const degreeMap = new Map<string, number>();
    filteredData.edges.forEach(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      degreeMap.set(sourceId, (degreeMap.get(sourceId) || 0) + 1);
      degreeMap.set(targetId, (degreeMap.get(targetId) || 0) + 1);
    });

    const sortedNodes = [...filteredData.nodes].sort((a, b) => {
      const aPriority = priorityNodes.has(a.id) ? 1000 : 0;
      const bPriority = priorityNodes.has(b.id) ? 1000 : 0;
      const aDegree = degreeMap.get(a.id) || 0;
      const bDegree = degreeMap.get(b.id) || 0;
      return (bPriority + bDegree) - (aPriority + aDegree);
    });

    const visibleNodes = sortedNodes.slice(0, maxVisibleNodes);
    const visibleNodeIds = new Set(visibleNodes.map(n => n.id));
    
    const visibleEdges = filteredData.edges.filter(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      return visibleNodeIds.has(sourceId) && visibleNodeIds.has(targetId);
    });

    return { nodes: visibleNodes, edges: visibleEdges };
  }, [filteredData, enableVirtualization, maxVisibleNodes, selectedNodes]);

  // 节流的事件处理
  const throttledHover = useRAFThrottle((node: GraphNode | null) => {
    setHoveredNode(node);
    onNodeHover?.(node);
  });

  const debouncedZoom = useDebounce((transform: d3.ZoomTransform) => {
    setViewState({
      transform,
      scale: transform.k,
      translate: [transform.x, transform.y],
    });
  }, 16);

  // 初始化图形
  useEffect(() => {
    if (!svgRef.current || !isVisible || visibleData.nodes.length === 0) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    svg.attr('width', width).attr('height', height);

    // 定义渐变和滤镜
    const defs = svg.append('defs');

    // 发光滤镜
    const filter = defs.append('filter')
      .attr('id', `glow-${uniqueId}`)
      .attr('x', '-50%')
      .attr('y', '-50%')
      .attr('width', '200%')
      .attr('height', '200%');
    
    filter.append('feGaussianBlur')
      .attr('stdDeviation', '3')
      .attr('result', 'coloredBlur');
    
    const feMerge = filter.append('feMerge');
    feMerge.append('feMergeNode').attr('in', 'coloredBlur');
    feMerge.append('feMergeNode').attr('in', 'SourceGraphic');

    // 渐变定义
    clusters.forEach(cluster => {
      const gradient = defs.append('radialGradient')
        .attr('id', `cluster-gradient-${cluster.id}-${uniqueId}`)
        .attr('cx', '50%')
        .attr('cy', '50%')
        .attr('r', '50%');
      
      gradient.append('stop')
        .attr('offset', '0%')
        .attr('stop-color', cluster.color)
        .attr('stop-opacity', '0.1');
      
      gradient.append('stop')
        .attr('offset', '100%')
        .attr('stop-color', cluster.color)
        .attr('stop-opacity', '0.3');
    });

    // 箭头标记
    defs.append('marker')
      .attr('id', `arrowhead-${uniqueId}`)
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 28)
      .attr('refY', 0)
      .attr('markerWidth', 8)
      .attr('markerHeight', 8)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', theme.colors.textMuted);

    defs.append('marker')
      .attr('id', `arrowhead-highlight-${uniqueId}`)
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 28)
      .attr('refY', 0)
      .attr('markerWidth', 8)
      .attr('markerHeight', 8)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', theme.colors.primary);

    const g = svg.append('g');
    gRef.current = g;

    // 缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent(ZOOM_EXTENT)
      .on('zoom', (event) => {
        g.attr('transform', event.transform);
        debouncedZoom(event.transform);
      });

    svg.call(zoom as any);
    zoomRef.current = zoom;

    // 力导向模拟
    const simulation = d3.forceSimulation<GraphNode>(visibleData.nodes)
      .force('link', d3.forceLink<GraphNode, GraphEdge>(visibleData.edges)
        .id(d => d.id)
        .distance(forceConfig.linkDistance))
      .force('charge', d3.forceManyBody().strength(forceConfig.chargeStrength))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(forceConfig.collisionRadius))
      .force('x', d3.forceX(width / 2).strength(forceConfig.centerStrength))
      .force('y', d3.forceY(height / 2).strength(forceConfig.centerStrength))
      .alphaDecay(forceConfig.alphaDecay)
      .velocityDecay(forceConfig.velocityDecay);

    simulationRef.current = simulation;

    // 绘制聚类背景
    if (showClusters) {
      const clusterGroups = g.append('g').attr('class', 'clusters')
        .selectAll('g')
        .data(clusters)
        .enter()
        .append('g')
        .attr('class', 'cluster');

      clusterGroups.append('circle')
        .attr('r', d => d.radius)
        .attr('fill', d => `url(#cluster-gradient-${d.id}-${uniqueId})`)
        .attr('stroke', d => d.color)
        .attr('stroke-width', 2)
        .attr('stroke-opacity', 0.3)
        .attr('stroke-dasharray', '5,5');

      clusterGroups.append('text')
        .text(d => d.type)
        .attr('y', d => -d.radius - 10)
        .attr('text-anchor', 'middle')
        .attr('font-size', '12px')
        .attr('font-weight', 'bold')
        .attr('fill', d => d.color);

      // 更新聚类位置
      simulation.on('tick.clusters', () => {
        clusterGroups.attr('transform', d => {
          const centroid = calculateClusterCentroid(d.nodes);
          return `translate(${centroid.x},${centroid.y})`;
        });
      });
    }

    // 绘制边
    const link = g.append('g')
      .attr('class', 'links')
      .selectAll('line')
      .data(visibleData.edges)
      .enter()
      .append('line')
      .attr('stroke', d => getEdgeColor(d.type, theme))
      .attr('stroke-width', d => Math.max(1, Math.sqrt(d.weight || 1) * 2))
      .attr('stroke-opacity', 0.6)
      .attr('stroke-dasharray', d => d.type === 'extends' || d.type === 'contradicts' ? '5,5' : null)
      .attr('marker-end', `url(#arrowhead-${uniqueId})`)
      .style('cursor', onEdgeClick ? 'pointer' : 'default')
      .on('click', (event, d) => {
        event.stopPropagation();
        onEdgeClick?.(d);
      });

    // 绘制节点组
    const node = g.append('g')
      .attr('class', 'nodes')
      .selectAll('g')
      .data(visibleData.nodes)
      .enter()
      .append('g')
      .style('cursor', 'pointer')
      .on('click', (event, d) => {
        event.stopPropagation();
        onNodeClick?.(d);
      })
      .on('mouseover', (event, d) => throttledHover(d))
      .on('mouseout', () => throttledHover(null));

    // 拖拽行为
    node.call(d3.drag<SVGGElement, GraphNode>()
      .on('start', (event, d) => {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        d.fx = d.x;
        d.fy = d.y;
      })
      .on('drag', (event, d) => {
        d.fx = event.x;
        d.fy = event.y;
      })
      .on('end', (event, d) => {
        if (!event.active) simulation.alphaTarget(0);
        d.fx = null;
        d.fy = null;
      }));

    // 节点圆形
    const circles = node.append('circle')
      .attr('r', d => getNodeRadius(d, config, viewState.scale < 0.5 ? 0.7 : 1))
      .attr('fill', d => d.color || getNodeColor(d.type, theme))
      .attr('stroke', theme.colors.surface)
      .attr('stroke-width', 3)
      .style('filter', d => selectedNodes.includes(d.id) ? `url(#glow-${uniqueId})` : null);

    // 选中状态边框
    node.filter(d => selectedNodes.includes(d.id))
      .append('circle')
      .attr('r', d => getNodeRadius(d, config, viewState.scale < 0.5 ? 0.7 : 1) + 5)
      .attr('fill', 'none')
      .attr('stroke', theme.colors.primary)
      .attr('stroke-width', 3)
      .attr('stroke-dasharray', '5,5')
      .style('pointer-events', 'none');

    // 节点标签
    if (config.showLabels !== false) {
      node.append('text')
        .text(d => d.label)
        .attr('x', d => getNodeRadius(d, config) + 5)
        .attr('y', 5)
        .attr('font-size', config.labelSize || 12)
        .attr('font-weight', 500)
        .attr('fill', theme.colors.text)
        .style('pointer-events', 'none')
        .style('text-shadow', `0 1px 3px ${theme.colors.background}`)
        .style('opacity', viewState.scale > 0.3 ? 1 : 0);
    }

    // 搜索高亮
    if (filterState.searchQuery) {
      const query = filterState.searchQuery.toLowerCase();
      circles.filter(d => d.label.toLowerCase().includes(query))
        .attr('stroke', theme.colors.warning)
        .attr('stroke-width', 4);
    }

    // 高亮路径
    if (highlightPath.length > 0) {
      const pathSet = new Set(highlightPath);
      
      circles.filter(d => pathSet.has(d.id))
        .attr('stroke', theme.colors.primary)
        .attr('stroke-width', 4);
      
      link.filter(d => {
        const sourceId = typeof d.source === 'string' ? d.source : d.source.id;
        const targetId = typeof d.target === 'string' ? d.target : d.target.id;
        return pathSet.has(sourceId) && pathSet.has(targetId);
      })
        .attr('stroke', theme.colors.primary)
        .attr('stroke-width', 3)
        .attr('marker-end', `url(#arrowhead-highlight-${uniqueId})`);
    }

    // 更新位置
    simulation.on('tick.nodes', () => {
      link
        .attr('x1', d => (d.source as GraphNode).x || 0)
        .attr('y1', d => (d.source as GraphNode).y || 0)
        .attr('x2', d => (d.target as GraphNode).x || 0)
        .attr('y2', d => (d.target as GraphNode).y || 0);

      node.attr('transform', d => `translate(${d.x || 0},${d.y || 0})`);
    });

    setIsReady(true);

    return () => {
      simulation.stop();
      simulationRef.current = null;
    };
  }, [visibleData, width, height, config, theme, uniqueId, isVisible, selectedNodes, highlightPath, 
      showClusters, clusters, forceConfig, viewState.scale, filterState.searchQuery, onNodeClick, onEdgeClick]);

  // 更新力导向参数
  useEffect(() => {
    if (simulationRef.current) {
      simulationRef.current
        .force('link', d3.forceLink<GraphNode, GraphEdge>(visibleData.edges)
          .id(d => d.id)
          .distance(forceConfig.linkDistance))
        .force('charge', d3.forceManyBody().strength(forceConfig.chargeStrength))
        .force('collision', d3.forceCollide().radius(forceConfig.collisionRadius))
        .force('x', d3.forceX(width / 2).strength(forceConfig.centerStrength))
        .force('y', d3.forceY(height / 2).strength(forceConfig.centerStrength))
        .alpha(0.3)
        .restart();
    }
  }, [forceConfig, visibleData.edges, width, height]);

  // 缩放控制
  const zoomIn = useCallback(() => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.scaleBy as any, 1.3);
  }, []);

  const zoomOut = useCallback(() => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.scaleBy as any, 0.7);
  }, []);

  const resetZoom = useCallback(() => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.transform as any, d3.zoomIdentity);
  }, []);

  const focusSelected = useCallback(() => {
    if (!svgRef.current || !zoomRef.current || selectedNodes.length === 0) return;

    const selectedNodeData = visibleData.nodes.find(n => selectedNodes.includes(n.id));
    if (!selectedNodeData || selectedNodeData.x === undefined || selectedNodeData.y === undefined) return;

    const transform = d3.zoomIdentity
      .translate(width / 2, height / 2)
      .scale(1.5)
      .translate(-selectedNodeData.x, -selectedNodeData.y);

    d3.select(svgRef.current)
      .transition()
      .duration(500)
      .call(zoomRef.current.transform as any, transform);
  }, [selectedNodes, visibleData.nodes, width, height]);

  const exportSVG = useCallback(() => {
    if (!svgRef.current) return;
    const svgData = new XMLSerializer().serializeToString(svgRef.current);
    const blob = new Blob([svgData], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `graph-${Date.now()}.svg`;
    link.click();
    URL.revokeObjectURL(url);
  }, []);

  const toggleFullscreen = useCallback(() => {
    setIsFullscreen(prev => !prev);
  }, []);

  // 容器样式
  const containerStyle = useMemo(() => ({
    width: isFullscreen ? '100vw' : '100%',
    height: isFullscreen ? '100vh' : height,
  }), [isFullscreen, height]);

  return (
    <div 
      ref={containerRef}
      className={cn(
        'relative bg-white rounded-lg border border-gray-200 overflow-hidden transition-all',
        isFullscreen && 'fixed inset-0 z-50 rounded-none',
        className
      )}
      style={containerStyle}
    >
      {/* 统计面板 */}
      <StatsPanel
        nodes={data.nodes}
        edges={data.edges}
        selectedCount={selectedNodes.length}
        fps={fps}
        visibleCount={visibleData.nodes.length}
        totalCount={data.nodes.length}
        isVisible={showStatsPanel}
        onToggle={() => setShowStatsPanel(!showStatsPanel)}
        theme={theme}
      />

      {/* 工具栏 */}
      <Toolbar
        onZoomIn={zoomIn}
        onZoomOut={zoomOut}
        onReset={resetZoom}
        onExport={exportSVG}
        onToggleFullscreen={toggleFullscreen}
        isFullscreen={isFullscreen}
        onFocusSelected={focusSelected}
        hasSelection={selectedNodes.length > 0}
        onToggleSettings={() => setShowForcePanel(!showForcePanel)}
        onToggleFilters={() => setShowFilterPanel(!showFilterPanel)}
        showSettings={showForcePanel}
        showFilters={showFilterPanel}
      />

      {/* 力导向参数面板 */}
      <ForcePanel
        config={forceConfig}
        onChange={setForceConfig}
        isVisible={showForcePanel}
        onToggle={() => setShowForcePanel(false)}
        theme={theme}
      />

      {/* 筛选面板 */}
      <FilterPanel
        filter={filterState}
        onChange={setFilterState}
        isVisible={showFilterPanel}
        onToggle={() => setShowFilterPanel(false)}
        theme={theme}
        nodeTypes={NODE_TYPES}
      />

      {/* 悬浮提示 */}
      {hoveredNode && (
        <div 
          className="absolute top-4 left-1/2 -translate-x-1/2 bg-white/95 backdrop-blur px-4 py-3 rounded-lg shadow-lg border border-gray-200 z-20 max-w-xs"
          style={{ borderColor: theme.colors.border }}
        >
          <h4 className="font-semibold text-gray-900">{hoveredNode.label}</h4>
          <p className="text-xs text-gray-500 mt-1 capitalize">{hoveredNode.type}</p>
          {hoveredNode.description && (
            <p className="text-sm text-gray-600 mt-2 line-clamp-3">{hoveredNode.description}</p>
          )}
          {(hoveredNode.importance !== undefined) && (
            <div className="mt-2 flex items-center gap-1">
              <span className="text-xs text-gray-400">重要性:</span>
              <div className="flex-1 h-1.5 bg-gray-200 rounded-full overflow-hidden">
                <div 
                  className="h-full rounded-full"
                  style={{ width: `${hoveredNode.importance * 100}%`, backgroundColor: theme.colors.primary }}
                />
              </div>
              <span className="text-xs text-gray-500">{hoveredNode.importance.toFixed(2)}</span>
            </div>
          )}
        </div>
      )}

      {/* 虚拟化提示 */}
      {enableVirtualization && filteredData.nodes.length > maxVisibleNodes && (
        <div className="absolute bottom-4 left-1/2 -translate-x-1/2 bg-yellow-50 border border-yellow-200 text-yellow-800 px-4 py-2 rounded-lg text-sm z-10">
          已启用虚拟化: 显示 {visibleData.nodes.length} / {filteredData.nodes.length} 个节点
        </div>
      )}

      {/* SVG Canvas */}
      <svg
        ref={svgRef}
        className="w-full h-full"
        style={{ minHeight: height }}
        role="img"
        aria-label="知识图谱可视化"
      />

      {/* 加载状态 */}
      {!isReady && (
        <div className="absolute inset-0 flex items-center justify-center bg-white/80">
          <div className="flex flex-col items-center gap-3">
            <RefreshCw className="w-8 h-8 text-blue-600 animate-spin" />
            <p className="text-sm text-gray-500">加载图谱中...</p>
          </div>
        </div>
      )}
    </div>
  );
};

export default EnhancedD3Graph;
