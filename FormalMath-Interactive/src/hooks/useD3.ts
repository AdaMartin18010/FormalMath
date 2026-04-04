// ==================== D3可视化Hook ====================

import { useRef, useEffect, useState, useCallback } from 'react';
import * as d3 from 'd3';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '@types';
import { getNodeTypeColor, getEdgeTypeStyle } from '@utils/helpers';

interface UseD3GraphOptions {
  width: number;
  height: number;
  config?: Partial<ViewConfig>;
  onNodeClick?: (node: GraphNode, event: MouseEvent) => void;
  onEdgeClick?: (edge: GraphEdge, event: MouseEvent) => void;
  onNodeHover?: (node: GraphNode | null, event: MouseEvent) => void;
}

interface UseD3GraphReturn {
  containerRef: React.RefObject<HTMLDivElement>;
  svgRef: React.RefObject<SVGSVGElement>;
  zoomIn: () => void;
  zoomOut: () => void;
  resetZoom: () => void;
  centerGraph: () => void;
  exportSVG: () => string;
  isReady: boolean;
}

export function useD3Graph(
  data: GraphData,
  options: UseD3GraphOptions
): UseD3GraphReturn {
  const containerRef = useRef<HTMLDivElement>(null);
  const svgRef = useRef<SVGSVGElement>(null);
  const [isReady, setIsReady] = useState(false);
  const zoomRef = useRef<d3.ZoomBehavior<Element, unknown> | null>(null);
  const simulationRef = useRef<d3.Simulation<GraphNode, GraphEdge> | null>(null);

  const { width, height, config, onNodeClick, onEdgeClick, onNodeHover } = options;

  // 初始化D3图形
  useEffect(() => {
    if (!containerRef.current || !svgRef.current || data.nodes.length === 0) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    // 设置SVG
    svg.attr('width', width).attr('height', height);

    // 创建组
    const g = svg.append('g');

    // 添加缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.1, 4])
      .on('zoom', (event) => {
        g.attr('transform', event.transform);
      });

    svg.call(zoom as any);
    zoomRef.current = zoom;

    // 箭头标记
    svg.append('defs')
      .append('marker')
      .attr('id', 'arrowhead')
      .attr('viewBox', '0 -5 10 10')
      .attr('refX', 25)
      .attr('refY', 0)
      .attr('markerWidth', 8)
      .attr('markerHeight', 8)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,-5L10,0L0,5')
      .attr('fill', '#6b7280');

    // 力导向模拟
    const simulation = d3.forceSimulation<GraphNode>(data.nodes)
      .force('link', d3.forceLink<GraphNode, GraphEdge>(data.edges)
        .id(d => d.id)
        .distance(100))
      .force('charge', d3.forceManyBody().strength(-300))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(30));

    simulationRef.current = simulation;

    // 绘制边
    const link = g.append('g')
      .attr('class', 'links')
      .selectAll('line')
      .data(data.edges)
      .enter()
      .append('line')
      .attr('stroke', d => getEdgeTypeStyle(d.type).color)
      .attr('stroke-width', config?.edgeWidth || 2)
      .attr('stroke-dasharray', d => getEdgeTypeStyle(d.type).dashed ? '5,5' : null)
      .attr('marker-end', 'url(#arrowhead)')
      .on('click', (event, d) => onEdgeClick?.(d, event as MouseEvent));

    // 绘制节点
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
    node.append('circle')
      .attr('r', d => d.radius || config?.nodeSize || 20)
      .attr('fill', d => d.color || getNodeTypeColor(d.type))
      .attr('stroke', '#fff')
      .attr('stroke-width', 2)
      .style('cursor', 'pointer')
      .on('click', (event, d) => onNodeClick?.(d, event as MouseEvent))
      .on('mouseover', (event, d) => onNodeHover?.(d, event as MouseEvent))
      .on('mouseout', (event) => onNodeHover?.(null, event as MouseEvent));

    // 节点标签
    if (config?.showLabels !== false) {
      node.append('text')
        .text(d => d.label)
        .attr('x', 25)
        .attr('y', 5)
        .attr('font-size', config?.labelSize || 12)
        .attr('fill', '#374151')
        .style('pointer-events', 'none');
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
  }, [data, width, height, config, onNodeClick, onEdgeClick, onNodeHover]);

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

  const centerGraph = useCallback(() => {
    if (!svgRef.current || !zoomRef.current) return;
    d3.select(svgRef.current)
      .transition()
      .duration(300)
      .call(zoomRef.current.transform as any, d3.zoomIdentity);
  }, []);

  // 导出SVG
  const exportSVG = useCallback(() => {
    if (!svgRef.current) return '';
    return new XMLSerializer().serializeToString(svgRef.current);
  }, []);

  return {
    containerRef,
    svgRef,
    zoomIn,
    zoomOut,
    resetZoom,
    centerGraph,
    exportSVG,
    isReady,
  };
}

/**
 * 使用D3创建树形图
 */
export function useD3Tree(
  data: { name: string; children?: typeof data[] },
  options: {
    width: number;
    height: number;
    nodeSize?: number;
    onNodeClick?: (node: unknown) => void;
  }
) {
  const svgRef = useRef<SVGSVGElement>(null);

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const { width, height, nodeSize = 20 } = options;
    svg.attr('width', width).attr('height', height);

    const g = svg.append('g').attr('transform', `translate(40,0)`);

    const tree = d3.tree().size([height, width - 160]);

    const root = d3.hierarchy(data);
    tree(root);

    // 绘制连接线
    g.selectAll('.link')
      .data(root.links())
      .enter()
      .append('path')
      .attr('class', 'link')
      .attr('fill', 'none')
      .attr('stroke', '#ccc')
      .attr('stroke-width', 2)
      .attr('d', d3.linkHorizontal()
        .x(d => (d as unknown as { y: number }).y)
        .y(d => (d as unknown as { x: number }).x) as any);

    // 绘制节点
    const node = g.selectAll('.node')
      .data(root.descendants())
      .enter()
      .append('g')
      .attr('class', 'node')
      .attr('transform', d => `translate(${d.y},${d.x})`)
      .on('click', (event, d) => options.onNodeClick?.(d));

    node.append('circle')
      .attr('r', nodeSize / 2)
      .attr('fill', '#69b3a2');

    node.append('text')
      .attr('dy', '.35em')
      .attr('x', d => d.children ? -13 : 13)
      .attr('text-anchor', d => d.children ? 'end' : 'start')
      .text(d => d.data.name);
  }, [data, options]);

  return { svgRef };
}

/**
 * 通用D3 Hook
 * 用于在组件中创建和更新D3可视化
 */
export function useD3<T>(
  renderFn: (svg: d3.Selection<SVGSVGElement, unknown, null, undefined>) => void,
  dependencies: React.DependencyList
): React.RefObject<SVGSVGElement> {
  const svgRef = useRef<SVGSVGElement>(null);

  useEffect(() => {
    if (!svgRef.current) return;
    
    const svg = d3.select(svgRef.current);
    renderFn(svg);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, dependencies);

  return svgRef;
}
