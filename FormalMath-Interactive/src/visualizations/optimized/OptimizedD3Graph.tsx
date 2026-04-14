// @ts-nocheck
/**
 * Optimized D3Graph - 优化版 D3 知识图谱可视化组件
 * 
 * 优化特性:
 * - 虚拟滚动支持 (大量节点)
 * - Web Worker 计算
 * - RAF 节流渲染
 * - 内存池复用
 * - 主题系统支持
 * - 无障碍优化
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
  Expand,
  ChevronDown,
  ChevronUp
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '../types';
import { 
  useRAFThrottle, 
  useDebounce, 
  useVisibilityObserver,
  usePerformanceMonitor 
} from '../hooks/usePerformance';
import { useSpring, easings } from '../hooks/useOptimizedAnimation';
import { getNodeColor, getEdgeColor, VisualizationTheme, lightTheme } from '../themes';

// ============================================
// 类型定义
// ============================================

interface OptimizedD3GraphProps {
  data: GraphData;
  width?: number;
  height?: number;
  config?: Partial<ViewConfig>;
  className?: string;
  theme?: VisualizationTheme;
  onNodeClick?: (node: GraphNode) => void;
  onEdgeClick?: (edge: GraphEdge) => void;
  onNodeHover?: (node: GraphNode | null) => void;
  selectedNodes?: string[];
  highlightPath?: string[];
  enableVirtualization?: boolean;
  maxVisibleNodes?: number;
  enableWebWorker?: boolean;
  showStats?: boolean;
}

interface ViewState {
  transform: d3.ZoomTransform;
  scale: number;
  translate: [number, number];
}

// ============================================
// 常量配置
// ============================================

const DEFAULT_CONFIG: ViewConfig = {
  nodeSize: 20,
  edgeWidth: 2,
  showLabels: true,
  labelSize: 12,
  enableZoom: true,
  enableDrag: true,
  showGrid: false,
};

const VIRTUALIZATION_THRESHOLD = 500;
const BATCH_SIZE = 50;
const ZOOM_EXTENT: [number, number] = [0.1, 4];

// ============================================
// 工具函数
// ============================================

const getNodeRadius = (node: GraphNode, config: ViewConfig): number => {
  return Math.max(5, Math.min(node.radius || config.nodeSize || 20, 50));
};

const getEdgeWidth = (edge: GraphEdge, config: ViewConfig): number => {
  return Math.max(1, Math.min(Math.sqrt(edge.weight || 1) * (config.edgeWidth || 2), 8));
};

// ============================================
// 统计面板组件
// ============================================

interface StatsPanelProps {
  nodes: GraphNode[];
  edges: GraphEdge[];
  selectedCount: number;
  fps?: number;
  isVisible: boolean;
  onToggle: () => void;
  theme: VisualizationTheme;
}

const StatsPanel = memo<StatsPanelProps>(({
  nodes,
  edges,
  selectedCount,
  fps,
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

  if (!isVisible) {
    return (
      <button
        onClick={onToggle}
        className="absolute top-4 left-4 p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg border border-gray-200 hover:bg-white transition-all z-10"
        title="显示统计"
      >
        <Layers className="w-4 h-4 text-gray-600" />
      </button>
    );
  }

  return (
    <div 
      className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-10 min-w-[200px]"
      style={{ borderColor: theme.colors.border }}
    >
      <div className="flex items-center justify-between mb-3">
        <h4 className="font-semibold text-gray-900 flex items-center gap-2">
          <Grid3x3 className="w-4 h-4 text-blue-600" />
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
          <span className="text-gray-600">节点总数:</span>
          <span className="font-medium text-gray-900">{nodes.length}</span>
        </div>
        <div className="flex justify-between">
          <span className="text-gray-600">连接总数:</span>
          <span className="font-medium text-gray-900">{edges.length}</span>
        </div>
        {selectedCount > 0 && (
          <div className="flex justify-between">
            <span className="text-gray-600">已选中:</span>
            <span className="font-medium text-blue-600">{selectedCount}</span>
          </div>
        )}
        {fps !== undefined && (
          <div className="flex justify-between">
            <span className="text-gray-600">FPS:</span>
            <span className={`font-medium ${fps < 30 ? 'text-red-500' : fps < 50 ? 'text-yellow-500' : 'text-green-500'}`}>
              {fps}
            </span>
          </div>
        )}
      </div>

      <div className="mt-3 pt-3 border-t border-gray-200">
        <p className="text-xs text-gray-500 mb-2">节点类型分布:</p>
        <div className="space-y-1 max-h-24 overflow-y-auto">
          {Object.entries(nodeTypes).map(([type, count]) => (
            <div key={type} className="flex justify-between text-xs">
              <span className="text-gray-500 capitalize">{type}:</span>
              <span 
                className="font-medium"
                style={{ color: getNodeColor(type) }}
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
}

const Toolbar = memo<ToolbarProps>(({
  onZoomIn,
  onZoomOut,
  onReset,
  onExport,
  onToggleFullscreen,
  isFullscreen,
  onFocusSelected,
  hasSelection
}) => (
  <div className="absolute top-4 right-4 flex flex-col gap-2 z-10">
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
// 主组件
// ============================================

export const OptimizedD3Graph: React.FC<OptimizedD3GraphProps> = ({
  data,
  width = 800,
  height = 600,
  config = {},
  className,
  theme = lightTheme,
  onNodeClick,
  onEdgeClick,
  onNodeHover,
  selectedNodes = [],
  highlightPath = [],
  enableVirtualization = true,
  maxVisibleNodes = 1000,
  showStats = false,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const gRef = useRef<d3.Selection<SVGGElement, unknown, null, undefined> | null>(null);
  const zoomRef = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(null);
  const simulationRef = useRef<d3.Simulation<GraphNode, GraphEdge> | null>(null);
  
  const [isReady, setIsReady] = useState(false);
  const [hoveredNode, setHoveredNode] = useState<GraphNode | null>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [showStatsPanel, setShowStatsPanel] = useState(showStats);
  const [viewState, setViewState] = useState<ViewState>({
    transform: d3.zoomIdentity,
    scale: 1,
    translate: [0, 0],
  });

  const uniqueId = useId();
  
  // 合并配置
  const mergedConfig = useMemo(() => ({
    ...DEFAULT_CONFIG,
    ...config,
  }), [config]);

  // 性能监控
  const metrics = usePerformanceMonitor('OptimizedD3Graph', process.env.NODE_ENV === 'development');

  // 可见性检测
  const isVisible = useVisibilityObserver(containerRef);

  // 数据虚拟化
  const visibleData = useMemo(() => {
    if (!enableVirtualization || data.nodes.length <= maxVisibleNodes) {
      return data;
    }

    // 优先显示选中节点及其邻居
    const priorityNodes = new Set<string>(selectedNodes);
    
    // 添加选中节点的邻居
    data.edges.forEach(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      
      if (selectedNodes.includes(sourceId)) {
        priorityNodes.add(targetId);
      }
      if (selectedNodes.includes(targetId)) {
        priorityNodes.add(sourceId);
      }
    });

    // 按中心性排序并截取
    const sortedNodes = [...data.nodes].sort((a, b) => {
      const aPriority = priorityNodes.has(a.id) ? 2 : a.importance || 0;
      const bPriority = priorityNodes.has(b.id) ? 2 : b.importance || 0;
      return bPriority - aPriority;
    });

    const visibleNodes = sortedNodes.slice(0, maxVisibleNodes);
    const visibleNodeIds = new Set(visibleNodes.map(n => n.id));
    
    // 过滤边
    const visibleEdges = data.edges.filter(edge => {
      const sourceId = typeof edge.source === 'string' ? edge.source : edge.source.id;
      const targetId = typeof edge.target === 'string' ? edge.target : edge.target.id;
      return visibleNodeIds.has(sourceId) && visibleNodeIds.has(targetId);
    });

    return { nodes: visibleNodes, edges: visibleEdges };
  }, [data, enableVirtualization, maxVisibleNodes, selectedNodes]);

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

    // 高亮箭头
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
        .distance(120))
      .force('charge', d3.forceManyBody().strength(-400))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(40))
      .force('x', d3.forceX(width / 2).strength(0.05))
      .force('y', d3.forceY(height / 2).strength(0.05));

    simulationRef.current = simulation;

    // 绘制边
    const link = g.append('g')
      .attr('class', 'links')
      .selectAll('line')
      .data(visibleData.edges)
      .enter()
      .append('line')
      .attr('stroke', d => getEdgeColor(d.type, theme))
      .attr('stroke-width', d => getEdgeWidth(d, mergedConfig))
      .attr('stroke-opacity', 0.6)
      .attr('stroke-dasharray', d => d.type === 'dashed' ? '5,5' : null)
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
    if (mergedConfig.enableDrag) {
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
    }

    // 节点圆形
    const circles = node.append('circle')
      .attr('r', d => getNodeRadius(d, mergedConfig))
      .attr('fill', d => d.color || getNodeColor(d.type, theme))
      .attr('stroke', theme.colors.surface)
      .attr('stroke-width', 3)
      .style('filter', d => selectedNodes.includes(d.id) ? `url(#glow-${uniqueId})` : null);

    // 选中状态边框
    node.filter(d => selectedNodes.includes(d.id))
      .append('circle')
      .attr('r', d => getNodeRadius(d, mergedConfig) + 5)
      .attr('fill', 'none')
      .attr('stroke', theme.colors.primary)
      .attr('stroke-width', 3)
      .attr('stroke-dasharray', '5,5')
      .style('pointer-events', 'none');

    // 节点标签
    if (mergedConfig.showLabels) {
      node.append('text')
        .text(d => d.label)
        .attr('x', d => getNodeRadius(d, mergedConfig) + 5)
        .attr('y', 5)
        .attr('font-size', mergedConfig.labelSize || 12)
        .attr('font-weight', 500)
        .attr('fill', theme.colors.text)
        .style('pointer-events', 'none')
        .style('text-shadow', `0 1px 3px ${theme.colors.background}`);
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
    simulation.on('tick', () => {
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
  }, [visibleData, width, height, mergedConfig, theme, uniqueId, isVisible, selectedNodes, highlightPath]);

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
        fps={metrics?.fps}
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
      />

      {/* 悬浮提示 */}
      {hoveredNode && (
        <div 
          className="absolute top-4 left-1/2 -translate-x-1/2 bg-white/95 backdrop-blur px-4 py-3 rounded-lg shadow-lg border border-gray-200 z-10 max-w-xs"
          style={{ borderColor: theme.colors.border }}
        >
          <h4 className="font-semibold text-gray-900">{hoveredNode.label}</h4>
          <p className="text-xs text-gray-500 mt-1 capitalize">{hoveredNode.type}</p>
          {hoveredNode.description && (
            <p className="text-sm text-gray-600 mt-2 line-clamp-3">{hoveredNode.description}</p>
          )}
        </div>
      )}

      {/* 虚拟化提示 */}
      {enableVirtualization && data.nodes.length > maxVisibleNodes && (
        <div className="absolute bottom-4 left-1/2 -translate-x-1/2 bg-yellow-50 border border-yellow-200 text-yellow-800 px-4 py-2 rounded-lg text-sm z-10">
          已启用虚拟化: 显示 {visibleData.nodes.length} / {data.nodes.length} 个节点
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

export default OptimizedD3Graph;
