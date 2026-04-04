/**
 * FormalMath 概念关联强度热力图组件
 * 可视化展示概念之间的关联强度和模式
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import * as d3 from 'd3';
import { 
  Flame, Search, Filter, Download, Eye, EyeOff,
  Maximize2, Minimize2, Info, ArrowUpRight,
  Grid3X3, Layers, Network
} from 'lucide-react';
import { cn } from '@utils/classNames';

// 关联数据
export interface AssociationData {
  concepts: string[];
  matrix: number[][]; // 关联强度矩阵 0-1
  metadata?: {
    conceptCategories?: Record<string, string>;
    conceptDescriptions?: Record<string, string>;
  };
}

// 聚类结果
export interface ClusterResult {
  id: number;
  concepts: string[];
  centroid: number[];
  color: string;
}

// 可视化模式
export type HeatmapMode = 'matrix' | 'clustered' | 'network' | 'circular';

// 组件Props
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

// 颜色比例尺
const getColorScale = (value: number, mode: 'heatmap' | 'diverging' = 'heatmap'): string => {
  if (mode === 'heatmap') {
    // 热力图: 白色 -> 黄色 -> 红色
    if (value < 0.2) return '#fef2f2';
    if (value < 0.4) return '#fee2e2';
    if (value < 0.6) return '#fecaca';
    if (value < 0.8) return '#fca5a5';
    return '#ef4444';
  } else {
    // 发散色: 蓝色 -> 白色 -> 红色
    if (value < -0.5) return '#3b82f6';
    if (value < 0) return '#93c5fd';
    if (value === 0) return '#f3f4f6';
    if (value < 0.5) return '#fca5a5';
    return '#ef4444';
  }
};

// 聚类颜色
const CLUSTER_COLORS = [
  '#3b82f6', '#10b981', '#f59e0b', '#8b5cf6', '#ec4899',
  '#06b6d4', '#84cc16', '#f97316', '#6366f1', '#14b8a6',
];

export const AssociationHeatmap: React.FC<AssociationHeatmapProps> = ({
  data,
  width = 800,
  height = 700,
  className,
  mode = 'matrix',
  onCellClick,
  onModeChange,
  showColorScale = true,
  enableClustering = true,
  threshold = 0.3,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const [currentMode, setCurrentMode] = useState<HeatmapMode>(mode);
  const [hoveredCell, setHoveredCell] = useState<{ i: number; j: number } | null>(null);
  const [selectedCells, setSelectedCells] = useState<Set<string>>(new Set());
  const [searchQuery, setSearchQuery] = useState('');
  const [currentThreshold, setCurrentThreshold] = useState(threshold);
  const [showLabels, setShowLabels] = useState(true);
  const [showValues, setShowValues] = useState(false);
  const [clusters, setClusters] = useState<ClusterResult[]>([]);
  const [zoomLevel, setZoomLevel] = useState(1);

  const { concepts, matrix } = data;

  // 执行聚类分析
  const performClustering = useCallback((): ClusterResult[] => {
    if (!enableClustering || concepts.length < 3) return [];

    // 简化的k-means聚类
    const k = Math.min(5, Math.floor(concepts.length / 3));
    const clusters: ClusterResult[] = [];

    // 初始化聚类中心
    for (let i = 0; i < k; i++) {
      clusters.push({
        id: i,
        concepts: [],
        centroid: matrix[Math.floor(Math.random() * concepts.length)],
        color: CLUSTER_COLORS[i % CLUSTER_COLORS.length],
      });
    }

    // 迭代聚类（简化版）
    for (let iter = 0; iter < 10; iter++) {
      // 清空聚类
      clusters.forEach(c => c.concepts = []);

      // 分配概念到最近聚类
      concepts.forEach((concept, idx) => {
        let minDist = Infinity;
        let closestCluster = 0;

        clusters.forEach((cluster, cIdx) => {
          const dist = euclideanDistance(matrix[idx], cluster.centroid);
          if (dist < minDist) {
            minDist = dist;
            closestCluster = cIdx;
          }
        });

        clusters[closestCluster].concepts.push(concept);
      });

      // 更新聚类中心
      clusters.forEach(cluster => {
        if (cluster.concepts.length > 0) {
          const indices = cluster.concepts.map(c => concepts.indexOf(c));
          cluster.centroid = calculateCentroid(indices.map(i => matrix[i]));
        }
      });
    }

    return clusters.filter(c => c.concepts.length > 0);
  }, [concepts, matrix, enableClustering]);

  // 欧氏距离
  const euclideanDistance = (a: number[], b: number[]): number => {
    return Math.sqrt(a.reduce((sum, val, i) => sum + Math.pow(val - b[i], 0), 0));
  };

  // 计算质心
  const calculateCentroid = (vectors: number[][]): number[] => {
    if (vectors.length === 0) return [];
    const n = vectors[0].length;
    return Array.from({ length: n }, (_, i) => 
      vectors.reduce((sum, v) => sum + v[i], 0) / vectors.length
    );
  };

  // 绘制热力图
  const drawHeatmap = useCallback(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const margin = { top: 80, right: 80, bottom: 40, left: 120 };
    const innerWidth = width - margin.left - margin.right;
    const innerHeight = height - margin.top - margin.bottom;

    const g = svg.append('g')
      .attr('transform', `translate(${margin.left},${margin.top}) scale(${zoomLevel})`);

    // 过滤概念
    const filteredIndices = concepts
      .map((c, i) => ({ concept: c, index: i }))
      .filter(({ concept }) => 
        concept.toLowerCase().includes(searchQuery.toLowerCase())
      )
      .map(({ index }) => index);

    const filteredConcepts = filteredIndices.map(i => concepts[i]);
    const n = filteredConcepts.length;

    if (n === 0) return;

    const cellSize = Math.min(innerWidth / n, innerHeight / n, 60);
    const actualWidth = cellSize * n;
    const actualHeight = cellSize * n;

    if (currentMode === 'matrix') {
      drawMatrixView(g, filteredIndices, cellSize, actualWidth, actualHeight);
    } else if (currentMode === 'clustered') {
      drawClusteredView(g, filteredIndices, cellSize);
    } else if (currentMode === 'network') {
      drawNetworkView(g, filteredIndices, innerWidth, innerHeight);
    } else if (currentMode === 'circular') {
      drawCircularView(g, filteredIndices, Math.min(innerWidth, innerHeight) / 2 - 50);
    }

    // 添加缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.5, 3])
      .on('zoom', (event) => {
        g.attr('transform', `translate(${margin.left + event.transform.x},${margin.top + event.transform.y}) scale(${event.transform.k})`);
        setZoomLevel(event.transform.k);
      });

    svg.call(zoom as any);

  }, [concepts, matrix, currentMode, searchQuery, hoveredCell, selectedCells, 
      currentThreshold, showLabels, showValues, clusters, width, height, zoomLevel]);

  // 矩阵视图
  const drawMatrixView = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    indices: number[],
    cellSize: number,
    width: number,
    height: number
  ) => {
    const n = indices.length;

    // 绘制单元格
    indices.forEach((rowIdx, i) => {
      indices.forEach((colIdx, j) => {
        const value = matrix[rowIdx][colIdx];
        if (value < currentThreshold) return;

        const isHovered = hoveredCell?.i === i && hoveredCell?.j === j;
        const isSelected = selectedCells.has(`${i}-${j}`);
        const isDiagonal = i === j;

        const cell = g.append('rect')
          .attr('x', j * cellSize)
          .attr('y', i * cellSize)
          .attr('width', cellSize - 1)
          .attr('height', cellSize - 1)
          .attr('fill', isDiagonal ? '#e5e7eb' : getColorScale(value))
          .attr('stroke', isSelected ? '#3b82f6' : isHovered ? '#1f2937' : 'none')
          .attr('stroke-width', isSelected ? 3 : 2)
          .attr('rx', 2)
          .style('cursor', 'pointer')
          .on('mouseover', () => setHoveredCell({ i, j }))
          .on('mouseout', () => setHoveredCell(null))
          .on('click', () => {
            const key = `${i}-${j}`;
            const newSelected = new Set(selectedCells);
            if (newSelected.has(key)) {
              newSelected.delete(key);
            } else {
              newSelected.add(key);
            }
            setSelectedCells(newSelected);
            onCellClick?.(concepts[rowIdx], concepts[colIdx], value);
          });

        // 显示数值
        if (showValues && !isDiagonal && cellSize > 30) {
          g.append('text')
            .attr('x', j * cellSize + cellSize / 2)
            .attr('y', i * cellSize + cellSize / 2)
            .attr('text-anchor', 'middle')
            .attr('dominant-baseline', 'middle')
            .attr('class', 'text-xs')
            .attr('fill', value > 0.5 ? '#fff' : '#374151')
            .text(value.toFixed(2));
        }
      });
    });

    // 行标签
    if (showLabels) {
      indices.forEach((idx, i) => {
        g.append('text')
          .attr('x', -10)
          .attr('y', i * cellSize + cellSize / 2)
          .attr('text-anchor', 'end')
          .attr('dominant-baseline', 'middle')
          .attr('class', 'text-xs')
          .attr('fill', '#374151')
          .text(concepts[idx].length > 15 ? concepts[idx].substring(0, 15) + '...' : concepts[idx]);
      });

      // 列标签
      indices.forEach((idx, j) => {
        g.append('text')
          .attr('x', j * cellSize + cellSize / 2)
          .attr('y', -10)
          .attr('text-anchor', 'middle')
          .attr('class', 'text-xs')
          .attr('fill', '#374151')
          .attr('transform', `rotate(-45, ${j * cellSize + cellSize / 2}, -10)`)
          .text(concepts[idx].length > 15 ? concepts[idx].substring(0, 15) + '...' : concepts[idx]);
      });
    }
  };

  // 聚类视图
  const drawClusteredView = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    indices: number[],
    cellSize: number
  ) => {
    // 按聚类分组显示
    let yOffset = 0;
    
    clusters.forEach(cluster => {
      const clusterIndices = cluster.concepts
        .map(c => concepts.indexOf(c))
            .filter(idx => indices.includes(idx));
      
      if (clusterIndices.length === 0) return;

      // 聚类标题
      g.append('rect')
        .attr('x', -110)
        .attr('y', yOffset)
        .attr('width', 100)
        .attr('height', clusterIndices.length * cellSize)
        .attr('fill', cluster.color)
        .attr('opacity', 0.2)
        .attr('rx', 4);

      g.append('text')
        .attr('x', -60)
        .attr('y', yOffset + clusterIndices.length * cellSize / 2)
        .attr('text-anchor', 'middle')
        .attr('dominant-baseline', 'middle')
        .attr('class', 'text-xs font-medium')
        .attr('fill', cluster.color)
        .text(`聚类 ${cluster.id + 1}`);

      clusterIndices.forEach((idx, i) => {
        g.append('text')
          .attr('x', -10)
          .attr('y', yOffset + i * cellSize + cellSize / 2)
          .attr('text-anchor', 'end')
          .attr('dominant-baseline', 'middle')
          .attr('class', 'text-xs')
          .attr('fill', '#374151')
          .text(concepts[idx]);
      });

      yOffset += clusterIndices.length * cellSize + 20;
    });
  };

  // 网络视图
  const drawNetworkView = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    indices: number[],
    width: number,
    height: number
  ) => {
    const nodes = indices.map(i => ({
      id: concepts[i],
      index: i,
      group: clusters.find(c => c.concepts.includes(concepts[i]))?.id || 0,
    }));

    const links: Array<{ source: string; target: string; value: number }> = [];
    indices.forEach((i, idx1) => {
      indices.forEach((j, idx2) => {
        if (i < j && matrix[i][j] >= currentThreshold) {
          links.push({
            source: concepts[i],
            target: concepts[j],
            value: matrix[i][j],
          });
        }
      });
    });

    const simulation = d3.forceSimulation(nodes as any)
      .force('link', d3.forceLink(links).id((d: any) => d.id).strength(d => d.value))
      .force('charge', d3.forceManyBody().strength(-200))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(40));

    // 绘制连线
    const linkElements = g.selectAll('.link')
      .data(links)
      .enter()
      .append('line')
      .attr('class', 'link')
      .attr('stroke', '#9ca3af')
      .attr('stroke-width', d => d.value * 5)
      .attr('stroke-opacity', 0.6);

    // 绘制节点
    const nodeElements = g.selectAll('.node')
      .data(nodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .style('cursor', 'pointer')
      .on('click', (event, d) => onCellClick?.(d.id, d.id, 1));

    nodeElements.append('circle')
      .attr('r', 20)
      .attr('fill', d => {
        const cluster = clusters.find(c => c.concepts.includes(d.id));
        return cluster?.color || '#3b82f6';
      })
      .attr('stroke', '#fff')
      .attr('stroke-width', 2);

    if (showLabels) {
      nodeElements.append('text')
        .text(d => d.id.length > 10 ? d.id.substring(0, 10) + '...' : d.id)
        .attr('y', 35)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-xs')
        .attr('fill', '#374151');
    }

    simulation.on('tick', () => {
      linkElements
        .attr('x1', (d: any) => d.source.x)
        .attr('y1', (d: any) => d.source.y)
        .attr('x2', (d: any) => d.target.x)
        .attr('y2', (d: any) => d.target.y);

      nodeElements.attr('transform', (d: any) => `translate(${d.x},${d.y})`);
    });
  };

  // 圆形视图
  const drawCircularView = (
    g: d3.Selection<SVGGElement, unknown, null, undefined>,
    indices: number[],
    radius: number
  ) => {
    const n = indices.length;
    const angleStep = (2 * Math.PI) / n;

    // 绘制连接线（弦）
    indices.forEach((i, idx1) => {
      indices.forEach((j, idx2) => {
        if (i >= j) return;
        const value = matrix[i][j];
        if (value < currentThreshold) return;

        const angle1 = idx1 * angleStep - Math.PI / 2;
        const angle2 = idx2 * angleStep - Math.PI / 2;
        const x1 = radius * Math.cos(angle1);
        const y1 = radius * Math.sin(angle1);
        const x2 = radius * Math.cos(angle2);
        const y2 = radius * Math.sin(angle2);

        // 绘制曲线连接
        const path = d3.path();
        path.moveTo(x1, y1);
        const midAngle = (angle1 + angle2) / 2;
        const midRadius = radius * 0.3;
        path.quadraticCurveTo(
          midRadius * Math.cos(midAngle),
          midRadius * Math.sin(midAngle),
          x2, y2
        );

        g.append('path')
          .attr('d', path.toString())
          .attr('fill', 'none')
          .attr('stroke', getColorScale(value))
          .attr('stroke-width', value * 3)
          .attr('opacity', 0.6);
      });
    });

    // 绘制节点
    indices.forEach((idx, i) => {
      const angle = i * angleStep - Math.PI / 2;
      const x = radius * Math.cos(angle);
      const y = radius * Math.sin(angle);

      const cluster = clusters.find(c => c.concepts.includes(concepts[idx]));

      g.append('circle')
        .attr('cx', x)
        .attr('cy', y)
        .attr('r', 15)
        .attr('fill', cluster?.color || '#3b82f6')
        .attr('stroke', '#fff')
        .attr('stroke-width', 2)
        .style('cursor', 'pointer')
        .on('click', () => onCellClick?.(concepts[idx], concepts[idx], 1));

      if (showLabels) {
        const labelRadius = radius + 30;
        const labelX = labelRadius * Math.cos(angle);
        const labelY = labelRadius * Math.sin(angle);

        g.append('text')
          .attr('x', labelX)
          .attr('y', labelY)
          .attr('text-anchor', angle > Math.PI / 2 || angle < -Math.PI / 2 ? 'end' : 'start')
          .attr('dominant-baseline', 'middle')
          .attr('class', 'text-xs')
          .attr('fill', '#374151')
          .text(concepts[idx].length > 12 ? concepts[idx].substring(0, 12) + '...' : concepts[idx]);
      }
    });
  };

  // 执行聚类
  useEffect(() => {
    if (enableClustering) {
      setClusters(performClustering());
    }
  }, [enableClustering, performClustering]);

  // 重绘
  useEffect(() => {
    drawHeatmap();
  }, [drawHeatmap]);

  // 模式切换
  const handleModeChange = (newMode: HeatmapMode) => {
    setCurrentMode(newMode);
    onModeChange?.(newMode);
  };

  // 统计信息
  const stats = React.useMemo(() => {
    let totalStrength = 0;
    let connectionCount = 0;
    let maxStrength = 0;

    matrix.forEach((row, i) => {
      row.forEach((val, j) => {
        if (i !== j && val >= currentThreshold) {
          totalStrength += val;
          connectionCount++;
          maxStrength = Math.max(maxStrength, val);
        }
      });
    });

    return {
      avgStrength: connectionCount > 0 ? (totalStrength / connectionCount).toFixed(2) : '0',
      connectionCount: Math.floor(connectionCount / 2),
      maxStrength: maxStrength.toFixed(2),
      density: ((connectionCount / 2) / (concepts.length * (concepts.length - 1) / 2) * 100).toFixed(1),
    };
  }, [matrix, currentThreshold, concepts.length]);

  return (
    <div ref={containerRef} className={cn('bg-white rounded-lg border border-gray-200', className)}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center gap-3">
          <div className="p-2 bg-red-100 rounded-lg">
            <Flame className="w-5 h-5 text-red-600" />
          </div>
          <div>
            <h3 className="font-semibold text-gray-800">概念关联热力图</h3>
            <p className="text-sm text-gray-500">{concepts.length} 个概念</p>
          </div>
        </div>

        {/* 视图模式切换 */}
        <div className="flex items-center gap-1 bg-gray-100 rounded-lg p-1">
          {(['matrix', 'clustered', 'network', 'circular'] as HeatmapMode[]).map((m) => (
            <button
              key={m}
              onClick={() => handleModeChange(m)}
              className={cn(
                'px-3 py-1.5 text-sm rounded-md transition-colors flex items-center gap-1',
                currentMode === m 
                  ? 'bg-white shadow-sm text-red-600 font-medium' 
                  : 'text-gray-600 hover:text-gray-800'
              )}
            >
              {m === 'matrix' && <Grid3X3 className="w-4 h-4" />}
              {m === 'clustered' && <Layers className="w-4 h-4" />}
              {m === 'network' && <Network className="w-4 h-4" />}
              {m === 'circular' && <ArrowUpRight className="w-4 h-4" />}
              {m === 'matrix' && '矩阵'}
              {m === 'clustered' && '聚类'}
              {m === 'network' && '网络'}
              {m === 'circular' && '圆形'}
            </button>
          ))}
        </div>

        {/* 控制选项 */}
        <div className="flex items-center gap-2">
          <div className="relative">
            <Search className="absolute left-2 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
            <input
              type="text"
              placeholder="搜索概念..."
              value={searchQuery}
              onChange={(e) => setSearchQuery(e.target.value)}
              className="pl-8 pr-3 py-1.5 text-sm border border-gray-200 rounded-lg w-40"
            />
          </div>
          <button
            onClick={() => setShowLabels(!showLabels)}
            className={cn(
              'p-2 rounded-lg transition-colors',
              showLabels ? 'bg-blue-100 text-blue-600' : 'hover:bg-gray-100 text-gray-600'
            )}
            title="显示标签"
          >
            {showLabels ? <Eye className="w-4 h-4" /> : <EyeOff className="w-4 h-4" />}
          </button>
          <button
            onClick={() => setShowValues(!showValues)}
            className={cn(
              'p-2 rounded-lg transition-colors text-sm font-medium',
              showValues ? 'bg-blue-100 text-blue-600' : 'hover:bg-gray-100 text-gray-600'
            )}
          >
            123
          </button>
        </div>
      </div>

      {/* 阈值控制 */}
      <div className="px-4 py-2 bg-gray-50 border-b border-gray-200 flex items-center gap-4">
        <span className="text-sm text-gray-600">关联强度阈值:</span>
        <input
          type="range"
          min="0"
          max="1"
          step="0.05"
          value={currentThreshold}
          onChange={(e) => setCurrentThreshold(Number(e.target.value))}
          className="flex-1 max-w-xs"
        />
        <span className="text-sm font-medium text-gray-800 w-12">{currentThreshold.toFixed(2)}</span>
        
        <div className="ml-auto flex items-center gap-4 text-sm">
          <span className="text-gray-600">平均强度: <span className="font-medium">{stats.avgStrength}</span></span>
          <span className="text-gray-600">连接数: <span className="font-medium">{stats.connectionCount}</span></span>
          <span className="text-gray-600">密度: <span className="font-medium">{stats.density}%</span></span>
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

        {/* 悬浮提示 */}
        {hoveredCell && currentMode === 'matrix' && (
          <div className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-10">
            {(() => {
              const filteredIndices = concepts
                .map((c, i) => ({ concept: c, index: i }))
                .filter(({ concept }) => 
                  concept.toLowerCase().includes(searchQuery.toLowerCase())
                )
                .map(({ index }) => index);
              
              const rowIdx = filteredIndices[hoveredCell.i];
              const colIdx = filteredIndices[hoveredCell.j];
              const value = matrix[rowIdx][colIdx];
              
              return (
                <>
                  <div className="flex items-center gap-2 mb-2">
                    <span className="font-medium text-gray-800">{concepts[rowIdx]}</span>
                    <span className="text-gray-400">↔</span>
                    <span className="font-medium text-gray-800">{concepts[colIdx]}</span>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="text-sm text-gray-600">关联强度:</span>
                    <div className="flex items-center gap-2">
                      <div className="w-20 h-2 bg-gray-200 rounded-full overflow-hidden">
                        <div 
                          className="h-full rounded-full"
                          style={{ 
                            width: `${value * 100}%`,
                            backgroundColor: getColorScale(value)
                          }}
                        />
                      </div>
                      <span className="font-semibold" style={{ color: getColorScale(value) }}>
                        {value.toFixed(2)}
                      </span>
                    </div>
                  </div>
                </>
              );
            })()}
          </div>
        )}
      </div>

      {/* 颜色比例尺 */}
      {showColorScale && (
        <div className="px-4 py-3 border-t border-gray-200 flex items-center gap-4">
          <span className="text-sm text-gray-600">关联强度:</span>
          <div className="flex items-center gap-1">
            <span className="text-xs text-gray-500">0</span>
            {[0.2, 0.4, 0.6, 0.8, 1.0].map(val => (
              <div
                key={val}
                className="w-8 h-4"
                style={{ backgroundColor: getColorScale(val) }}
              />
            ))}
            <span className="text-xs text-gray-500">1</span>
          </div>
          <div className="ml-auto flex items-center gap-2">
            {clusters.map(cluster => (
              <div key={cluster.id} className="flex items-center gap-1">
                <div 
                  className="w-3 h-3 rounded-full"
                  style={{ backgroundColor: cluster.color }}
                />
                <span className="text-xs text-gray-600">聚类 {cluster.id + 1}</span>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

export default AssociationHeatmap;
