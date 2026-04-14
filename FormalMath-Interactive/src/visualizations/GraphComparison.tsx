// @ts-nocheck
/**
 * FormalMath 知识图谱对比视图组件
 * 并排对比两个知识图谱的差异和相似性
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import * as d3 from 'd3';
import { 
  GitCompare, ArrowRight, Target, Layers,
  Plus, Minus, AlertCircle, CheckCircle, HelpCircle 
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge } from '@types';

// 对比模式
export type ComparisonMode = 'side-by-side' | 'overlay' | 'diff' | 'merge';

// 节点匹配结果
export interface NodeMatch {
  nodeA?: GraphNode;
  nodeB?: GraphNode;
  similarity: number;
  type: 'match' | 'only-in-a' | 'only-in-b' | 'modified';
}

// 对比结果统计
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

// 组件Props
export interface GraphComparisonProps {
  graphA: GraphData;
  graphB: GraphData;
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

// 颜色配置
const COLORS = {
  match: '#10b981',      // 绿色 - 匹配
  onlyInA: '#3b82f6',    // 蓝色 - 仅A
  onlyInB: '#f59e0b',    // 橙色 - 仅B
  modified: '#8b5cf6',   // 紫色 - 修改
  edgeCommon: '#9ca3af', // 灰色 - 共同边
  edgeOnlyA: '#60a5fa',  // 浅蓝 - 仅A边
  edgeOnlyB: '#fbbf24',  // 浅橙 - 仅B边
};

export const GraphComparison: React.FC<GraphComparisonProps> = ({
  graphA,
  graphB,
  titleA = '图谱 A',
  titleB = '图谱 B',
  width = 1200,
  height = 600,
  className,
  mode = 'side-by-side',
  onNodeClick,
  onModeChange,
  showStats = true,
  showLegend = true,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [currentMode, setCurrentMode] = useState<ComparisonMode>(mode);
  const [selectedMatch, setSelectedMatch] = useState<NodeMatch | null>(null);
  const [hoveredNode, setHoveredNode] = useState<string | null>(null);
  const [zoomLevel, setZoomLevel] = useState(1);
  const [showLabels, setShowLabels] = useState(true);
  const [matchThreshold, setMatchThreshold] = useState(0.8);

  // 计算节点匹配
  const nodeMatches = React.useMemo<NodeMatch[]>(() => {
    const matches: NodeMatch[] = [];
    const matchedB = new Set<string>();

    // 寻找匹配和修改的节点
    graphA.nodes.forEach(nodeA => {
      const matchB = graphB.nodes.find(nodeB => 
        nodeB.id === nodeA.id || 
        nodeB.label.toLowerCase() === nodeA.label.toLowerCase()
      );

      if (matchB) {
        matchedB.add(matchB.id);
        const similarity = calculateSimilarity(nodeA, matchB);
        matches.push({
          nodeA,
          nodeB: matchB,
          similarity,
          type: similarity >= matchThreshold ? 'match' : 'modified',
        });
      } else {
        matches.push({
          nodeA,
          similarity: 0,
          type: 'only-in-a',
        });
      }
    });

    // 添加仅B存在的节点
    graphB.nodes.forEach(nodeB => {
      if (!matchedB.has(nodeB.id)) {
        matches.push({
          nodeB,
          similarity: 0,
          type: 'only-in-b',
        });
      }
    });

    return matches;
  }, [graphA, graphB, matchThreshold]);

  // 计算相似度
  const calculateSimilarity = (nodeA: GraphNode, nodeB: GraphNode): number => {
    let score = 0;
    if (nodeA.type === nodeB.type) score += 0.4;
    if (nodeA.label.toLowerCase() === nodeB.label.toLowerCase()) score += 0.6;
    return score;
  };

  // 计算统计数据
  const stats: ComparisonStats = React.useMemo(() => {
    const common = nodeMatches.filter(m => m.type === 'match').length;
    const onlyA = nodeMatches.filter(m => m.type === 'only-in-a').length;
    const onlyB = nodeMatches.filter(m => m.type === 'only-in-b').length;
    const modified = nodeMatches.filter(m => m.type === 'modified').length;
    
    const totalNodes = Math.max(graphA.nodes.length, graphB.nodes.length);
    const similarityScore = totalNodes > 0 ? (common / totalNodes) * 100 : 0;

    return {
      commonNodes: common,
      onlyInA: onlyA,
      onlyInB: onlyB,
      modifiedNodes: modified,
      commonEdges: 0,
      onlyEdgesInA: 0,
      onlyEdgesInB: 0,
      similarityScore: Math.round(similarityScore),
    };
  }, [nodeMatches, graphA, graphB]);

  // 绘制对比视图
  const drawComparison = useCallback(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const margin = { top: 20, right: 20, bottom: 20, left: 20 };
    const innerWidth = width - margin.left - margin.right;
    const innerHeight = height - margin.top - margin.bottom;

    const g = svg.append('g')
      .attr('transform', `translate(${margin.left},${margin.top}) scale(${zoomLevel})`);

    if (currentMode === 'side-by-side') {
      drawSideBySide(g, innerWidth / 2 - 20, innerHeight);
    } else if (currentMode === 'overlay') {
      drawOverlay(g, innerWidth, innerHeight);
    } else if (currentMode === 'diff') {
      drawDiff(g, innerWidth, innerHeight);
    } else if (currentMode === 'merge') {
      drawMerge(g, innerWidth, innerHeight);
    }

    // 添加缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.3, 3])
      .on('zoom', (event) => {
        g.attr('transform', `translate(${margin.left + event.transform.x},${margin.top + event.transform.y}) scale(${event.transform.k})`);
        setZoomLevel(event.transform.k);
      });

    svg.call(zoom as any);

  }, [currentMode, nodeMatches, graphA, graphB, width, height, zoomLevel, showLabels]);

  // 并排视图
  const drawSideBySide = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    panelWidth: number,
    panelHeight: number
  ) => {
    // 左侧面板 - Graph A
    const leftPanel = g.append('g');
    drawGraphPanel(leftPanel, graphA, panelWidth, panelHeight, titleA, '#3b82f6', 0);

    // 分隔线
    g.append('line')
      .attr('x1', panelWidth + 20)
      .attr('y1', 0)
      .attr('x2', panelWidth + 20)
      .attr('y2', panelHeight)
      .attr('stroke', '#e5e7eb')
      .attr('stroke-width', 2)
      .attr('stroke-dasharray', '5,5');

    // 右侧面板 - Graph B
    const rightPanel = g.append('g')
      .attr('transform', `translate(${panelWidth + 40}, 0)`);
    drawGraphPanel(rightPanel, graphB, panelWidth, panelHeight, titleB, '#f59e0b', panelWidth + 40);
  };

  // 绘制单个图谱面板
  const drawGraphPanel = (
    panel: d3.Selection<SVGGElement, unknown, null, undefined>,
    data: GraphData,
    w: number,
    h: number,
    title: string,
    color: string,
    offsetX: number
  ) => {
    // 背景
    panel.append('rect')
      .attr('width', w)
      .attr('height', h)
      .attr('fill', '#f9fafb')
      .attr('rx', 8)
      .attr('stroke', '#e5e7eb');

    // 标题
    panel.append('text')
      .attr('x', w / 2)
      .attr('y', 30)
      .attr('text-anchor', 'middle')
      .attr('class', 'font-semibold text-lg')
      .attr('fill', color)
      .text(title);

    // 创建力导向模拟
    const simulation = d3.forceSimulation<GraphNode>(data.nodes)
      .force('link', d3.forceLink<GraphNode, GraphEdge>(data.edges)
        .id(d => d.id)
        .distance(80))
      .force('charge', d3.forceManyBody().strength(-300))
      .force('center', d3.forceCenter(w / 2, h / 2 + 20))
      .force('collision', d3.forceCollide().radius(30));

    const graphG = panel.append('g');

    // 绘制边
    const links = graphG.selectAll('.link')
      .data(data.edges)
      .enter()
      .append('line')
      .attr('class', 'link')
      .attr('stroke', '#9ca3af')
      .attr('stroke-width', 1.5)
      .attr('opacity', 0.6);

    // 绘制节点
    const nodes = graphG.selectAll('.node')
      .data(data.nodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .style('cursor', 'pointer')
      .on('click', (event, d) => {
        const match = nodeMatches.find(m => 
          m.nodeA?.id === d.id || m.nodeB?.id === d.id
        );
        if (match) {
          setSelectedMatch(match);
          onNodeClick?.(match);
        }
      })
      .on('mouseover', (event, d) => setHoveredNode(d.id))
      .on('mouseout', () => setHoveredNode(null));

    // 节点圆圈
    nodes.append('circle')
      .attr('r', 20)
      .attr('fill', color)
      .attr('stroke', '#fff')
      .attr('stroke-width', 2);

    // 节点标签
    if (showLabels) {
      nodes.append('text')
        .text(d => d.label)
        .attr('y', 35)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-xs')
        .attr('fill', '#374151');
    }

    // 更新位置
    simulation.on('tick', () => {
      links
        .attr('x1', d => (d.source as GraphNode).x || 0)
        .attr('y1', d => (d.source as GraphNode).y || 0)
        .attr('x2', d => (d.target as GraphNode).x || 0)
        .attr('y2', d => (d.target as GraphNode).y || 0);

      nodes.attr('transform', d => `translate(${d.x || 0},${d.y || 0})`);
    });
  };

  // 叠加视图
  const drawOverlay = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    w: number,
    h: number
  ) => {
    const simulation = d3.forceSimulation<GraphNode>([...graphA.nodes, ...graphB.nodes])
      .force('link', d3.forceLink<GraphNode, GraphEdge>([...graphA.edges, ...graphB.edges])
        .id(d => d.id)
        .distance(80))
      .force('charge', d3.forceManyBody().strength(-300))
      .force('center', d3.forceCenter(w / 2, h / 2))
      .force('collision', d3.forceCollide().radius(35));

    // 绘制边
    g.selectAll('.link')
      .data([...graphA.edges, ...graphB.edges])
      .enter()
      .append('line')
      .attr('class', 'link')
      .attr('stroke', '#9ca3af')
      .attr('stroke-width', 1)
      .attr('opacity', 0.4);

    // 绘制节点
    const nodes = g.selectAll('.node')
      .data(nodeMatches)
      .enter()
      .append('g')
      .attr('class', 'node')
      .style('cursor', 'pointer')
      .on('click', (event, d) => {
        setSelectedMatch(d);
        onNodeClick?.(d);
      });

    nodes.each(function(d) {
      const node = d3.select(this);
      
      if (d.type === 'match') {
        // 匹配节点 - 绿色
        node.append('circle')
          .attr('r', 25)
          .attr('fill', COLORS.match)
          .attr('opacity', 0.8);
      } else if (d.type === 'only-in-a') {
        // 仅A - 蓝色
        node.append('circle')
          .attr('r', 20)
          .attr('fill', COLORS.onlyInA);
      } else if (d.type === 'only-in-b') {
        // 仅B - 橙色
        node.append('circle')
          .attr('r', 20)
          .attr('fill', COLORS.onlyInB);
      } else {
        // 修改 - 紫色
        node.append('circle')
          .attr('r', 22)
          .attr('fill', COLORS.modified);
      }
    });

    if (showLabels) {
      nodes.append('text')
        .text(d => d.nodeA?.label || d.nodeB?.label || '')
        .attr('y', 40)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-xs')
        .attr('fill', '#374151');
    }
  };

  // 差异视图
  const drawDiff = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    w: number,
    h: number
  ) => {
    // 只显示差异节点
    const diffMatches = nodeMatches.filter(m => m.type !== 'match');
    
    const cols = 3;
    const colWidth = w / cols;
    const rowHeight = 100;

    const groups = g.selectAll('.diff-group')
      .data(diffMatches)
      .enter()
      .append('g')
      .attr('transform', (d, i) => {
        const col = i % cols;
        const row = Math.floor(i / cols);
        return `translate(${col * colWidth + colWidth / 2}, ${row * rowHeight + 60})`;
      });

    groups.each(function(d) {
      const group = d3.select(this);
      const color = d.type === 'only-in-a' ? COLORS.onlyInA : 
                    d.type === 'only-in-b' ? COLORS.onlyInB : COLORS.modified;
      
      group.append('circle')
        .attr('r', 30)
        .attr('fill', color)
        .attr('opacity', 0.8);

      group.append('text')
        .text(d.nodeA?.label || d.nodeB?.label || '')
        .attr('y', 50)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-sm font-medium')
        .attr('fill', '#374151');

      const typeLabel = d.type === 'only-in-a' ? '仅A' : 
                        d.type === 'only-in-b' ? '仅B' : '修改';
      
      group.append('text')
        .text(typeLabel)
        .attr('y', 70)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-xs')
        .attr('fill', '#6b7280');
    });
  };

  // 合并视图
  const drawMerge = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    w: number,
    h: number
  ) => {
    // 显示合并后的图谱
    const mergedNodes = new Map<string, GraphNode>();
    
    nodeMatches.forEach(match => {
      if (match.nodeA) {
        mergedNodes.set(match.nodeA.id, { ...match.nodeA, color: COLORS.match });
      } else if (match.nodeB) {
        mergedNodes.set(match.nodeB.id, { ...match.nodeB, color: COLORS.onlyInB });
      }
    });

    const nodes = Array.from(mergedNodes.values());
    
    const simulation = d3.forceSimulation<GraphNode>(nodes)
      .force('charge', d3.forceManyBody().strength(-400))
      .force('center', d3.forceCenter(w / 2, h / 2))
      .force('collision', d3.forceCollide().radius(40));

    const nodeGroups = g.selectAll('.merged-node')
      .data(nodes)
      .enter()
      .append('g')
      .attr('class', 'merged-node')
      .style('cursor', 'pointer');

    nodeGroups.append('circle')
      .attr('r', 25)
      .attr('fill', d => d.color || COLORS.match)
      .attr('stroke', '#fff')
      .attr('stroke-width', 3);

    if (showLabels) {
      nodeGroups.append('text')
        .text(d => d.label)
        .attr('y', 45)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-sm')
        .attr('fill', '#374151');
    }

    simulation.on('tick', () => {
      nodeGroups.attr('transform', d => `translate(${d.x || 0},${d.y || 0})`);
    });
  };

  // 重绘
  useEffect(() => {
    drawComparison();
  }, [drawComparison]);

  // 模式切换
  const handleModeChange = (newMode: ComparisonMode) => {
    setCurrentMode(newMode);
    onModeChange?.(newMode);
  };

  return (
    <div className={cn('bg-white rounded-lg border border-gray-200', className)}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center gap-2">
          <GitCompare className="w-5 h-5 text-blue-500" />
          <h3 className="font-semibold text-gray-800">知识图谱对比</h3>
        </div>

        {/* 模式切换 */}
        <div className="flex items-center gap-1 bg-gray-100 rounded-lg p-1">
          {(['side-by-side', 'overlay', 'diff', 'merge'] as ComparisonMode[]).map((m) => (
            <button
              key={m}
              onClick={() => handleModeChange(m)}
              className={cn(
                'px-3 py-1.5 text-sm rounded-md transition-colors',
                currentMode === m 
                  ? 'bg-white shadow-sm text-blue-600 font-medium' 
                  : 'text-gray-600 hover:text-gray-800'
              )}
            >
              {m === 'side-by-side' && '并排'}
              {m === 'overlay' && '叠加'}
              {m === 'diff' && '差异'}
              {m === 'merge' && '合并'}
            </button>
          ))}
        </div>

        {/* 控制选项 */}
        <div className="flex items-center gap-2">
          <button
            onClick={() => setShowLabels(!showLabels)}
            className={cn(
              'px-3 py-1.5 text-sm rounded-lg transition-colors',
              showLabels ? 'bg-blue-100 text-blue-700' : 'bg-gray-100 text-gray-600'
            )}
          >
            标签
          </button>
          <div className="flex items-center gap-1 bg-gray-100 rounded-lg p-1">
            <button
              onClick={() => setZoomLevel(Math.max(0.3, zoomLevel - 0.2))}
              className="p-1 hover:bg-white rounded transition-colors"
            >
              <Minus className="w-4 h-4" />
            </button>
            <span className="text-sm text-gray-600 px-2">{Math.round(zoomLevel * 100)}%</span>
            <button
              onClick={() => setZoomLevel(Math.min(3, zoomLevel + 0.2))}
              className="p-1 hover:bg-white rounded transition-colors"
            >
              <Plus className="w-4 h-4" />
            </button>
          </div>
        </div>
      </div>

      {/* 主可视化区域 */}
      <div className="relative">
        <svg
          ref={svgRef}
          width={width}
          height={height}
          className="w-full"
        />

        {/* 选中详情 */}
        {selectedMatch && (
          <div className="absolute top-4 right-4 bg-white rounded-lg shadow-lg border border-gray-200 p-4 w-72 z-10">
            <div className="flex justify-between items-start mb-3">
              <h4 className="font-semibold text-gray-800">节点详情</h4>
              <button
                onClick={() => setSelectedMatch(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                ×
              </button>
            </div>
            
            <div className="space-y-3">
              {selectedMatch.nodeA && (
                <div className="p-3 bg-blue-50 rounded-lg">
                  <div className="flex items-center gap-2 mb-1">
                    <span className="text-xs font-medium text-blue-600">{titleA}</span>
                  </div>
                  <p className="font-medium text-gray-800">{selectedMatch.nodeA.label}</p>
                  <p className="text-sm text-gray-500">类型: {selectedMatch.nodeA.type}</p>
                </div>
              )}

              {selectedMatch.type === 'match' && (
                <div className="flex justify-center">
                  <ArrowRight className="w-5 h-5 text-green-500" />
                </div>
              )}

              {selectedMatch.nodeB && (
                <div className="p-3 bg-amber-50 rounded-lg">
                  <div className="flex items-center gap-2 mb-1">
                    <span className="text-xs font-medium text-amber-600">{titleB}</span>
                  </div>
                  <p className="font-medium text-gray-800">{selectedMatch.nodeB.label}</p>
                  <p className="text-sm text-gray-500">类型: {selectedMatch.nodeB.type}</p>
                </div>
              )}

              <div className="flex items-center gap-2 pt-2 border-t">
                {selectedMatch.type === 'match' && (
                  <><CheckCircle className="w-4 h-4 text-green-500" /><span className="text-sm text-green-600">匹配节点</span></>
                )}
                {selectedMatch.type === 'only-in-a' && (
                  <><AlertCircle className="w-4 h-4 text-blue-500" /><span className="text-sm text-blue-600">仅存在于A</span></>
                )}
                {selectedMatch.type === 'only-in-b' && (
                  <><AlertCircle className="w-4 h-4 text-amber-500" /><span className="text-sm text-amber-600">仅存在于B</span></>
                )}
                {selectedMatch.type === 'modified' && (
                  <><HelpCircle className="w-4 h-4 text-purple-500" /><span className="text-sm text-purple-600">已修改 (相似度: {Math.round(selectedMatch.similarity * 100)}%)</span></>
                )}
              </div>
            </div>
          </div>
        )}
      </div>

      {/* 统计和图例 */}
      {(showStats || showLegend) && (
        <div className="px-4 py-3 border-t border-gray-200 flex items-center justify-between">
          {showStats && (
            <div className="flex items-center gap-6">
              <div className="flex items-center gap-2">
                <Target className="w-4 h-4 text-gray-400" />
                <span className="text-sm text-gray-600">相似度:</span>
                <span className="font-semibold text-gray-800">{stats.similarityScore}%</span>
              </div>
              <div className="flex items-center gap-4 text-sm">
                <span className="text-green-600">匹配: {stats.commonNodes}</span>
                <span className="text-blue-600">仅A: {stats.onlyInA}</span>
                <span className="text-amber-600">仅B: {stats.onlyInB}</span>
                <span className="text-purple-600">修改: {stats.modifiedNodes}</span>
              </div>
            </div>
          )}

          {showLegend && (
            <div className="flex items-center gap-4">
              <div className="flex items-center gap-1.5">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.match }} />
                <span className="text-xs text-gray-600">匹配</span>
              </div>
              <div className="flex items-center gap-1.5">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.onlyInA }} />
                <span className="text-xs text-gray-600">仅A</span>
              </div>
              <div className="flex items-center gap-1.5">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.onlyInB }} />
                <span className="text-xs text-gray-600">仅B</span>
              </div>
              <div className="flex items-center gap-1.5">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.modified }} />
                <span className="text-xs text-gray-600">修改</span>
              </div>
            </div>
          )}
        </div>
      )}
    </div>
  );
};

export default GraphComparison;
