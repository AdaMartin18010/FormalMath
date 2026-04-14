// @ts-nocheck
import React, { useRef, useEffect, useState, useCallback } from 'react';
import * as d3 from 'd3';
import { ZoomIn, ZoomOut, Maximize, Target, Download, RefreshCw } from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '@types';
import { getNodeTypeColor, getEdgeTypeStyle } from '@utils/helpers';

interface D3GraphProps {
  data: GraphData;
  width?: number;
  height?: number;
  config?: Partial<ViewConfig>;
  className?: string;
  onNodeClick?: (node: GraphNode) => void;
  onEdgeClick?: (edge: GraphEdge) => void;
  selectedNodes?: string[];
  highlightPath?: string[];
}

export const D3Graph: React.FC<D3GraphProps> = ({
  data,
  width = 800,
  height = 600,
  config = {},
  className,
  onNodeClick,
  onEdgeClick,
  selectedNodes = [],
  highlightPath = [],
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const zoomRef = useRef<d3.ZoomBehavior<SVGSVGElement, unknown> | null>(null);
  const [isReady, setIsReady] = useState(false);
  const [hoveredNode, setHoveredNode] = useState<GraphNode | null>(null);

  // 初始化图形
  useEffect(() => {
    if (!svgRef.current || data.nodes.length === 0) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    svg.attr('width', width).attr('height', height);

    // 定义渐变和滤镜
    const defs = svg.append('defs');

    // 发光滤镜
    const filter = defs.append('filter')
      .attr('id', 'glow')
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
      .attr('id', 'arrowhead')
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 28)
      .attr('refY', 0)
      .attr('markerWidth', 8)
      .attr('markerHeight', 8)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', '#6b7280');

    // 高亮箭头
    defs.append('marker')
      .attr('id', 'arrowhead-highlight')
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 28)
      .attr('refY', 0)
      .attr('markerWidth', 8)
      .attr('markerHeight', 8)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', '#3b82f6');

    const g = svg.append('g');

    // 缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.1, 4])
      .on('zoom', (event) => {
        g.attr('transform', event.transform);
      });

    svg.call(zoom as any);
    zoomRef.current = zoom;

    // 力导向模拟
    const simulation = d3.forceSimulation<GraphNode>(data.nodes)
      .force('link', d3.forceLink<GraphNode, GraphEdge>(data.edges)
        .id(d => d.id)
        .distance(120))
      .force('charge', d3.forceManyBody().strength(-400))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(40));

    // 绘制边
    const link = g.append('g')
      .attr('class', 'links')
      .selectAll('line')
      .data(data.edges)
      .enter()
      .append('line')
      .attr('stroke', d => getEdgeTypeStyle(d.type).color)
      .attr('stroke-width', d => Math.sqrt(d.weight || 1) * (config.edgeWidth || 2))
      .attr('stroke-opacity', 0.6)
      .attr('stroke-dasharray', d => getEdgeTypeStyle(d.type).dashed ? '5,5' : null)
      .attr('marker-end', 'url(#arrowhead)')
      .style('cursor', onEdgeClick ? 'pointer' : 'default')
      .on('click', (event, d) => {
        event.stopPropagation();
        onEdgeClick?.(d);
      });

    // 绘制节点组
    const node = g.append('g')
      .attr('class', 'nodes')
      .selectAll('g')
      .data(data.nodes)
      .enter()
      .append('g')
      .call(d3.drag<SVGGElement, GraphNode>()
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
      .attr('r', d => d.radius || config.nodeSize || 20)
      .attr('fill', d => d.color || getNodeTypeColor(d.type))
      .attr('stroke', '#fff')
      .attr('stroke-width', 3)
      .style('cursor', 'pointer')
      .style('filter', d => selectedNodes.includes(d.id) ? 'url(#glow)' : null)
      .on('click', (event, d) => {
        event.stopPropagation();
        onNodeClick?.(d);
      })
      .on('mouseover', (event, d) => setHoveredNode(d))
      .on('mouseout', () => setHoveredNode(null));

    // 选中状态边框
    node.filter(d => selectedNodes.includes(d.id))
      .append('circle')
      .attr('r', d => (d.radius || config.nodeSize || 20) + 5)
      .attr('fill', 'none')
      .attr('stroke', '#3b82f6')
      .attr('stroke-width', 3)
      .attr('stroke-dasharray', '5,5')
      .style('pointer-events', 'none');

    // 节点标签
    if (config.showLabels !== false) {
      node.append('text')
        .text(d => d.label)
        .attr('x', 25)
        .attr('y', 5)
        .attr('font-size', config.labelSize || 12)
        .attr('font-weight', 500)
        .attr('fill', '#374151')
        .style('pointer-events', 'none')
        .style('text-shadow', '0 1px 3px rgba(255,255,255,0.8)');
    }

    // 高亮路径
    if (highlightPath.length > 0) {
      const pathSet = new Set(highlightPath);
      
      circles.filter(d => pathSet.has(d.id))
        .attr('stroke', '#3b82f6')
        .attr('stroke-width', 4);
      
      link.filter(d => pathSet.has(d.source as string) && pathSet.has(d.target as string))
        .attr('stroke', '#3b82f6')
        .attr('stroke-width', 3)
        .attr('marker-end', 'url(#arrowhead-highlight)');
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
    };
  }, [data, width, height, config, onNodeClick, onEdgeClick, selectedNodes, highlightPath]);

  // 缩放控制
  const zoomIn = () => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.scaleBy as any, 1.3);
  };

  const zoomOut = () => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.scaleBy as any, 0.7);
  };

  const resetZoom = () => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.transform as any, d3.zoomIdentity);
  };

  const exportSVG = () => {
    if (!svgRef.current) return;
    const svgData = new XMLSerializer().serializeToString(svgRef.current);
    const blob = new Blob([svgData], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `graph-${Date.now()}.svg`;
    link.click();
    URL.revokeObjectURL(url);
  };

  return (
    <div ref={containerRef} className={cn('relative bg-white rounded-lg border border-gray-200', className)}>
      {/* Toolbar */}
      <div className="absolute top-4 right-4 flex flex-col gap-2 z-10">
        <button
          onClick={zoomIn}
          className="p-2 bg-white rounded-lg shadow-md hover:bg-gray-50 transition-colors"
          title="放大"
        >
          <ZoomIn className="w-4 h-4 text-gray-600" />
        </button>
        <button
          onClick={zoomOut}
          className="p-2 bg-white rounded-lg shadow-md hover:bg-gray-50 transition-colors"
          title="缩小"
        >
          <ZoomOut className="w-4 h-4 text-gray-600" />
        </button>
        <button
          onClick={resetZoom}
          className="p-2 bg-white rounded-lg shadow-md hover:bg-gray-50 transition-colors"
          title="重置视图"
        >
          <Target className="w-4 h-4 text-gray-600" />
        </button>
        <button
          onClick={exportSVG}
          className="p-2 bg-white rounded-lg shadow-md hover:bg-gray-50 transition-colors"
          title="导出SVG"
        >
          <Download className="w-4 h-4 text-gray-600" />
        </button>
      </div>

      {/* Tooltip */}
      {hoveredNode && (
        <div className="absolute top-4 left-4 bg-white/95 backdrop-blur px-4 py-3 rounded-lg shadow-lg border border-gray-200 z-10 max-w-xs">
          <h4 className="font-semibold text-gray-900">{hoveredNode.label}</h4>
          <p className="text-xs text-gray-500 mt-1 capitalize">{hoveredNode.type}</p>
          {hoveredNode.description && (
            <p className="text-sm text-gray-600 mt-2 line-clamp-3">{hoveredNode.description}</p>
          )}
        </div>
      )}

      {/* Status Bar */}
      <div className="absolute bottom-4 left-4 right-4 flex items-center justify-between">
        <div className="flex items-center gap-4 text-xs text-gray-500">
          <span>节点: {data.nodes.length}</span>
          <span>连接: {data.edges.length}</span>
          {selectedNodes.length > 0 && (
            <span className="text-blue-600">已选: {selectedNodes.length}</span>
          )}
        </div>
      </div>

      {/* SVG Canvas */}
      <svg
        ref={svgRef}
        className="w-full h-full"
        style={{ minHeight: height }}
      />
    </div>
  );
};

export default D3Graph;
