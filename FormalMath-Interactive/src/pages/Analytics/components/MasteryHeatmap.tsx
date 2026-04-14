// @ts-nocheck
/**
 * 概念掌握热力图组件
 * 可视化展示各概念的掌握程度
 */

import React, { useMemo, useState } from 'react';
import * as d3 from 'd3';
import { useD3 } from '@hooks/useD3';
import type { MasteryHeatmapData, HeatmapCell, ConceptCategory } from '@types/analytics';

interface MasteryHeatmapProps {
  data: MasteryHeatmapData;
  onCellClick?: (cell: HeatmapCell) => void;
  className?: string;
}

/**
 * 概念掌握热力图组件
 */
export const MasteryHeatmap: React.FC<MasteryHeatmapProps> = ({
  data,
  onCellClick,
  className = '',
}) => {
  const [selectedCategory, setSelectedCategory] = useState<string | 'all'>('all');
  const [hoveredCell, setHoveredCell] = useState<HeatmapCell | null>(null);

  // 过滤数据
  const filteredCells = useMemo(() => {
    if (selectedCategory === 'all') return data.cells;
    return data.cells.filter((cell) => cell.categoryId === selectedCategory);
  }, [data.cells, selectedCategory]);

  // 颜色比例尺
  const colorScale = useMemo(() => {
    return d3
      .scaleSequential(d3.interpolateRdYlGn)
      .domain([0, 100]);
  }, []);

  // 获取掌握度标签
  const getMasteryLabel = (level: number): string => {
    if (level === 0) return '未开始';
    if (level < 25) return '初学';
    if (level < 50) return '理解';
    if (level < 75) return '熟练';
    return '精通';
  };

  const svgRef = useD3(
    (svg) => {
      if (filteredCells.length === 0) return;

      const cellSize = 40;
      const gap = 4;
      const cols = Math.min(10, Math.ceil(Math.sqrt(filteredCells.length)));
      const rows = Math.ceil(filteredCells.length / cols);

      const width = cols * (cellSize + gap) + gap;
      const height = rows * (cellSize + gap) + gap;

      svg.selectAll('*').remove();

      svg.attr('width', width).attr('height', height);

      // 绘制单元格
      const cells = svg
        .selectAll('.cell')
        .data(filteredCells)
        .enter()
        .append('g')
        .attr('class', 'cell')
        .attr('transform', (_, i) => {
          const row = Math.floor(i / cols);
          const col = i % cols;
          return `translate(${col * (cellSize + gap) + gap}, ${row * (cellSize + gap) + gap})`;
        })
        .style('cursor', 'pointer')
        .on('click', (_, d) => onCellClick?.(d))
        .on('mouseenter', (_, d) => setHoveredCell(d))
        .on('mouseleave', () => setHoveredCell(null));

      // 单元格矩形
      cells
        .append('rect')
        .attr('width', cellSize)
        .attr('height', cellSize)
        .attr('rx', 4)
        .attr('fill', (d) => colorScale(d.masteryLevel))
        .attr('stroke', '#fff')
        .attr('stroke-width', 1);

      // 概念名称
      cells
        .append('text')
        .attr('x', cellSize / 2)
        .attr('y', cellSize / 2 - 4)
        .attr('text-anchor', 'middle')
        .attr('dominant-baseline', 'middle')
        .style('font-size', '10px')
        .style('font-weight', '500')
        .style('fill', (d) => (d.masteryLevel > 50 ? '#fff' : '#374151'))
        .style('pointer-events', 'none')
        .text((d) => (d.conceptName.length > 4 ? d.conceptName.slice(0, 3) + '...' : d.conceptName));

      // 掌握度百分比
      cells
        .append('text')
        .attr('x', cellSize / 2)
        .attr('y', cellSize / 2 + 10)
        .attr('text-anchor', 'middle')
        .attr('dominant-baseline', 'middle')
        .style('font-size', '9px')
        .style('fill', (d) => (d.masteryLevel > 50 ? '#fff' : '#374151'))
        .style('pointer-events', 'none')
        .text((d) => `${d.masteryLevel}%`);
    },
    [filteredCells, colorScale, onCellClick]
  );

  return (
    <div className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg ${className}`}>
      {/* 头部 */}
      <div className="p-4 border-b border-gray-200 dark:border-slate-700">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <h3 className="text-lg font-semibold text-gray-800 dark:text-gray-200">概念掌握热力图</h3>
          
          {/* 分类筛选 */}
          <select
            value={selectedCategory}
            onChange={(e) => setSelectedCategory(e.target.value)}
            className="px-3 py-1.5 text-sm border border-gray-300 dark:border-slate-600 rounded-lg 
                       bg-white dark:bg-slate-700 text-gray-700 dark:text-gray-300
                       focus:outline-none focus:ring-2 focus:ring-blue-500"
          >
            <option value="all">全部分类</option>
            {data.categories.map((cat) => (
              <option key={cat.id} value={cat.id}>
                {cat.name} ({cat.conceptCount})
              </option>
            ))}
          </select>
        </div>

        {/* 统计信息 */}
        <div className="flex flex-wrap gap-4 mt-3 text-sm text-gray-600 dark:text-gray-400">
          <span>平均掌握度: <strong className="text-gray-800 dark:text-gray-200">{data.overallStats.averageMastery}%</strong></span>
          <span>最强分类: <strong className="text-gray-800 dark:text-gray-200">{data.overallStats.strongestCategory}</strong></span>
          <span>最弱分类: <strong className="text-gray-800 dark:text-gray-200">{data.overallStats.weakestCategory}</strong></span>
        </div>
      </div>

      {/* 热力图 */}
      <div className="p-4">
        <div className="overflow-x-auto">
          <svg ref={svgRef} className="mx-auto" />
        </div>

        {filteredCells.length === 0 && (
          <div className="text-center py-8 text-gray-500 dark:text-gray-400">
            暂无数据
          </div>
        )}
      </div>

      {/* 图例 */}
      <div className="px-4 pb-4">
        <div className="flex items-center justify-center gap-2">
          <span className="text-xs text-gray-500 dark:text-gray-400">0%</span>
          <div className="w-32 h-3 rounded" style={{ background: 'linear-gradient(to right, #d73027, #fee08b, #1a9850)' }} />
          <span className="text-xs text-gray-500 dark:text-gray-400">100%</span>
        </div>
        <div className="flex justify-center gap-4 mt-2 text-xs text-gray-500 dark:text-gray-400">
          <span>🔴 需加强</span>
          <span>🟡 学习中</span>
          <span>🟢 已掌握</span>
        </div>
      </div>

      {/* 悬停提示 */}
      {hoveredCell && (
        <div className="px-4 pb-4">
          <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-3">
            <div className="flex items-center justify-between">
              <h4 className="font-medium text-gray-800 dark:text-gray-200">{hoveredCell.conceptName}</h4>
              <span
                className={`text-xs px-2 py-0.5 rounded-full ${
                  hoveredCell.masteryLevel >= 75
                    ? 'bg-green-100 text-green-600 dark:bg-green-900/30 dark:text-green-400'
                    : hoveredCell.masteryLevel >= 50
                    ? 'bg-yellow-100 text-yellow-600 dark:bg-yellow-900/30 dark:text-yellow-400'
                    : hoveredCell.masteryLevel > 0
                    ? 'bg-orange-100 text-orange-600 dark:bg-orange-900/30 dark:text-orange-400'
                    : 'bg-gray-100 text-gray-600 dark:bg-slate-600 dark:text-gray-400'
                }`}
              >
                {getMasteryLabel(hoveredCell.masteryLevel)}
              </span>
            </div>
            <div className="grid grid-cols-3 gap-4 mt-2 text-sm text-gray-600 dark:text-gray-400">
              <div>
                <span className="block text-xs opacity-70">掌握度</span>
                <span className="font-medium text-gray-800 dark:text-gray-200">{hoveredCell.masteryLevel}%</span>
              </div>
              <div>
                <span className="block text-xs opacity-70">学习次数</span>
                <span className="font-medium text-gray-800 dark:text-gray-200">{hoveredCell.studyCount} 次</span>
              </div>
              <div>
                <span className="block text-xs opacity-70">学习时长</span>
                <span className="font-medium text-gray-800 dark:text-gray-200">
                  {Math.round(hoveredCell.timeSpent / 60)} 分钟
                </span>
              </div>
            </div>
          </div>
        </div>
      )}

      {/* 需要复习的概念 */}
      {data.overallStats.needsReview.length > 0 && (
        <div className="px-4 pb-4">
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-2">需要复习</h4>
          <div className="flex flex-wrap gap-2">
            {data.overallStats.needsReview.slice(0, 5).map((conceptId) => {
              const cell = data.cells.find((c) => c.conceptId === conceptId);
              return cell ? (
                <span
                  key={conceptId}
                  className="text-xs px-2 py-1 bg-orange-100 text-orange-700 dark:bg-orange-900/30 dark:text-orange-400 rounded cursor-pointer hover:bg-orange-200 dark:hover:bg-orange-900/50"
                  onClick={() => onCellClick?.(cell)}
                >
                  {cell.conceptName}
                </span>
              ) : null;
            })}
            {data.overallStats.needsReview.length > 5 && (
              <span className="text-xs px-2 py-1 text-gray-500 dark:text-gray-400">
                +{data.overallStats.needsReview.length - 5} 更多
              </span>
            )}
          </div>
        </div>
      )}
    </div>
  );
};

export default MasteryHeatmap;
