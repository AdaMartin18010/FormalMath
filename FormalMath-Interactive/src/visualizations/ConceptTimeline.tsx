// @ts-nocheck
/**
 * FormalMath 概念演化时间线可视化组件
 * 展示数学概念随时间的演化历程
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import * as d3 from 'd3';
import { 
  Play, Pause, SkipForward, SkipBack, 
  Calendar, Users, BookOpen, GitBranch 
} from 'lucide-react';
import { cn } from '@utils/classNames';

// 时间线事件类型
export interface TimelineEvent {
  id: string;
  date: Date;
  year: number;
  title: string;
  description: string;
  type: 'discovery' | 'proof' | 'publication' | 'application' | 'extension';
  mathematician?: string;
  conceptId: string;
  impact: number; // 1-10
  references?: string[];
}

// 概念演化阶段
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

// 组件Props
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

// 事件类型配置
const EVENT_TYPE_CONFIG: Record<TimelineEvent['type'], { color: string; icon: string; label: string }> = {
  discovery: { color: '#3b82f6', icon: '🔍', label: '发现' },
  proof: { color: '#10b981', icon: '✓', label: '证明' },
  publication: { color: '#8b5cf6', icon: '📄', label: '发表' },
  application: { color: '#f59e0b', icon: '🚀', label: '应用' },
  extension: { color: '#ec4899', icon: '↗', label: '扩展' },
};

// 成熟度配置
const MATURITY_CONFIG: Record<ConceptStage['maturity'], { color: string; label: string }> = {
  nascent: { color: '#fef3c7', label: '萌芽期' },
  developing: { color: '#dbeafe', label: '发展期' },
  mature: { color: '#d1fae5', label: '成熟期' },
  refined: { color: '#f3e8ff', label: '精炼期' },
};

export const ConceptTimeline: React.FC<ConceptTimelineProps> = ({
  events,
  stages = [],
  width = 1000,
  height = 600,
  className,
  autoPlay = false,
  onEventClick,
  onStageClick,
  highlightedConcepts = [],
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const [currentTime, setCurrentTime] = useState<Date | null>(null);
  const [isPlaying, setIsPlaying] = useState(autoPlay);
  const [playbackSpeed, setPlaybackSpeed] = useState(1);
  const [selectedEvent, setSelectedEvent] = useState<TimelineEvent | null>(null);
  const [hoveredEvent, setHoveredEvent] = useState<TimelineEvent | null>(null);
  const [viewMode, setViewMode] = useState<'timeline' | 'stages'>('timeline');
  const animationRef = useRef<number | null>(null);

  // 按时间排序事件
  const sortedEvents = React.useMemo(() => {
    return [...events].sort((a, b) => a.date.getTime() - b.date.getTime());
  }, [events]);

  // 时间范围
  const timeRange = React.useMemo(() => {
    if (sortedEvents.length === 0) return { start: new Date(), end: new Date() };
    return {
      start: sortedEvents[0].date,
      end: sortedEvents[sortedEvents.length - 1].date,
    };
  }, [sortedEvents]);

  // 初始化当前时间
  useEffect(() => {
    if (!currentTime && sortedEvents.length > 0) {
      setCurrentTime(sortedEvents[0].date);
    }
  }, [sortedEvents, currentTime]);

  // 绘制时间线
  const drawTimeline = useCallback(() => {
    if (!svgRef.current || sortedEvents.length === 0) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const margin = { top: 60, right: 50, bottom: 80, left: 80 };
    const innerWidth = width - margin.left - margin.right;
    const innerHeight = height - margin.top - margin.bottom;

    const g = svg.append('g')
      .attr('transform', `translate(${margin.left},${margin.top})`);

    // 创建时间比例尺
    const xScale = d3.scaleTime()
      .domain([timeRange.start, timeRange.end])
      .range([0, innerWidth]);

    // Y轴比例尺 - 根据影响力分布
    const yScale = d3.scaleLinear()
      .domain([0, 10])
      .range([innerHeight, 0]);

    // 绘制阶段背景（如果存在）
    if (viewMode === 'stages' && stages.length > 0) {
      stages.forEach((stage, i) => {
        const startX = xScale(stage.startDate);
        const endX = stage.endDate ? xScale(stage.endDate) : innerWidth;
        const config = MATURITY_CONFIG[stage.maturity];

        g.append('rect')
          .attr('x', startX)
          .attr('y', 0)
          .attr('width', endX - startX)
          .attr('height', innerHeight)
          .attr('fill', config.color)
          .attr('opacity', 0.3)
          .style('cursor', onStageClick ? 'pointer' : 'default')
          .on('click', () => onStageClick?.(stage));

        // 阶段标签
        g.append('text')
          .attr('x', (startX + endX) / 2)
          .attr('y', -10)
          .attr('text-anchor', 'middle')
          .attr('class', 'text-xs font-medium')
          .attr('fill', '#6b7280')
          .text(stage.name);
      });
    }

    // 绘制主时间轴线
    g.append('line')
      .attr('x1', 0)
      .attr('y1', innerHeight + 30)
      .attr('x2', innerWidth)
      .attr('y2', innerHeight + 30)
      .attr('stroke', '#e5e7eb')
      .attr('stroke-width', 2);

    // 绘制时间轴刻度
    const tickCount = Math.min(10, sortedEvents.length);
    const ticks = xScale.ticks(tickCount);
    
    ticks.forEach(tick => {
      const x = xScale(tick);
      g.append('line')
        .attr('x1', x)
        .attr('y1', innerHeight + 25)
        .attr('x2', x)
        .attr('y2', innerHeight + 35)
        .attr('stroke', '#9ca3af')
        .attr('stroke-width', 1);

      g.append('text')
        .attr('x', x)
        .attr('y', innerHeight + 55)
        .attr('text-anchor', 'middle')
        .attr('class', 'text-xs')
        .attr('fill', '#6b7280')
        .text(tick.getFullYear());
    });

    // 绘制事件点
    const eventGroups = g.selectAll('.event-group')
      .data(sortedEvents)
      .enter()
      .append('g')
      .attr('class', 'event-group')
      .attr('transform', d => `translate(${xScale(d.date)}, ${yScale(d.impact)})`)
      .style('cursor', 'pointer')
      .on('click', (event, d) => {
        event.stopPropagation();
        setSelectedEvent(d);
        onEventClick?.(d);
      })
      .on('mouseover', (event, d) => setHoveredEvent(d))
      .on('mouseout', () => setHoveredEvent(null));

    // 事件连接线
    eventGroups.each(function(d, i) {
      if (i > 0) {
        const prev = sortedEvents[i - 1];
        d3.select(this.parentNode)
          .insert('line', '.event-group')
          .attr('x1', xScale(prev.date))
          .attr('y1', yScale(prev.impact))
          .attr('x2', xScale(d.date))
          .attr('y2', yScale(d.impact))
          .attr('stroke', '#e5e7eb')
          .attr('stroke-width', 1)
          .attr('stroke-dasharray', '4,4');
      }
    });

    // 事件圆圈
    eventGroups.append('circle')
      .attr('r', d => 4 + d.impact * 1.5)
      .attr('fill', d => EVENT_TYPE_CONFIG[d.type].color)
      .attr('stroke', '#fff')
      .attr('stroke-width', 2)
      .attr('opacity', d => {
        if (highlightedConcepts.length > 0) {
          return highlightedConcepts.includes(d.conceptId) ? 1 : 0.3;
        }
        return currentTime && d.date > currentTime ? 0.3 : 1;
      })
      .transition()
      .duration(500)
      .attr('r', d => 5 + d.impact * 1.5);

    // 事件图标
    eventGroups.append('text')
      .attr('y', d => -8 - d.impact * 1.5)
      .attr('text-anchor', 'middle')
      .attr('class', 'text-sm')
      .text(d => EVENT_TYPE_CONFIG[d.type].icon);

    // 当前时间指示器
    if (currentTime) {
      const currentX = xScale(currentTime);
      g.append('line')
        .attr('x1', currentX)
        .attr('y1', 0)
        .attr('x2', currentX)
        .attr('y2', innerHeight + 40)
        .attr('stroke', '#ef4444')
        .attr('stroke-width', 2)
        .attr('stroke-dasharray', '5,5');

      g.append('polygon')
        .attr('points', `${currentX - 8},0 ${currentX + 8},0 ${currentX},10`)
        .attr('fill', '#ef4444');
    }

    // 缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.5, 5])
      .on('zoom', (event) => {
        g.attr('transform', `translate(${margin.left + event.transform.x},${margin.top}) scale(${event.transform.k}, 1)`);
      });

    svg.call(zoom as any);

  }, [sortedEvents, stages, width, height, timeRange, currentTime, highlightedConcepts, viewMode, onEventClick, onStageClick]);

  // 动画播放
  useEffect(() => {
    if (!isPlaying || !currentTime) return;

    const startTime = timeRange.start.getTime();
    const endTime = timeRange.end.getTime();
    const duration = (endTime - startTime) / (365 * 24 * 60 * 60 * 1000) * 10000 / playbackSpeed;
    const startAnimationTime = Date.now();
    const initialTime = currentTime.getTime();

    const animate = () => {
      const elapsed = Date.now() - startAnimationTime;
      const progress = Math.min(elapsed / duration, 1);
      
      const newTime = new Date(initialTime + (endTime - initialTime) * progress);
      setCurrentTime(newTime);

      if (progress < 1 && isPlaying) {
        animationRef.current = requestAnimationFrame(animate);
      } else {
        setIsPlaying(false);
      }
    };

    animationRef.current = requestAnimationFrame(animate);

    return () => {
      if (animationRef.current) {
        cancelAnimationFrame(animationRef.current);
      }
    };
  }, [isPlaying, timeRange, playbackSpeed]);

  // 重绘时间线
  useEffect(() => {
    drawTimeline();
  }, [drawTimeline]);

  // 播放控制
  const handlePlay = () => setIsPlaying(!isPlaying);
  const handleReset = () => {
    setIsPlaying(false);
    setCurrentTime(timeRange.start);
  };
  const handleSkipForward = () => {
    const idx = sortedEvents.findIndex(e => e.date > (currentTime || timeRange.start));
    if (idx >= 0) setCurrentTime(sortedEvents[idx].date);
  };
  const handleSkipBack = () => {
    const idx = sortedEvents.findIndex(e => e.date >= (currentTime || timeRange.start));
    if (idx > 0) setCurrentTime(sortedEvents[idx - 1].date);
  };

  return (
    <div ref={containerRef} className={cn('bg-white rounded-lg border border-gray-200', className)}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center gap-4">
          <h3 className="font-semibold text-gray-800">概念演化时间线</h3>
          <div className="flex items-center gap-1 bg-gray-100 rounded-lg p-1">
            <button
              onClick={() => setViewMode('timeline')}
              className={cn(
                'px-3 py-1 text-sm rounded-md transition-colors',
                viewMode === 'timeline' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-600 hover:text-gray-800'
              )}
            >
              时间线
            </button>
            <button
              onClick={() => setViewMode('stages')}
              className={cn(
                'px-3 py-1 text-sm rounded-md transition-colors',
                viewMode === 'stages' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-600 hover:text-gray-800'
              )}
            >
              发展阶段
            </button>
          </div>
        </div>

        {/* 播放控制 */}
        <div className="flex items-center gap-2">
          <button
            onClick={handleSkipBack}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="上一个事件"
          >
            <SkipBack className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={handlePlay}
            className="p-2 bg-blue-500 hover:bg-blue-600 rounded-lg transition-colors"
            title={isPlaying ? '暂停' : '播放'}
          >
            {isPlaying ? (
              <Pause className="w-4 h-4 text-white" />
            ) : (
              <Play className="w-4 h-4 text-white" />
            )}
          </button>
          <button
            onClick={handleSkipForward}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="下一个事件"
          >
            <SkipForward className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={handleReset}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="重置"
          >
            <Calendar className="w-4 h-4 text-gray-600" />
          </button>
          <select
            value={playbackSpeed}
            onChange={(e) => setPlaybackSpeed(Number(e.target.value))}
            className="ml-2 text-sm border border-gray-200 rounded-lg px-2 py-1"
          >
            <option value={0.5}>0.5x</option>
            <option value={1}>1x</option>
            <option value={2}>2x</option>
            <option value={5}>5x</option>
          </select>
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
        {hoveredEvent && (
          <div className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 max-w-xs z-10">
            <div className="flex items-center gap-2 mb-2">
              <span className="text-lg">{EVENT_TYPE_CONFIG[hoveredEvent.type].icon}</span>
              <span 
                className="text-xs font-medium px-2 py-0.5 rounded-full"
                style={{ 
                  backgroundColor: `${EVENT_TYPE_CONFIG[hoveredEvent.type].color}20`,
                  color: EVENT_TYPE_CONFIG[hoveredEvent.type].color 
                }}
              >
                {EVENT_TYPE_CONFIG[hoveredEvent.type].label}
              </span>
            </div>
            <h4 className="font-semibold text-gray-800">{hoveredEvent.title}</h4>
            <p className="text-sm text-gray-500 mt-1">{hoveredEvent.year}年</p>
            <p className="text-sm text-gray-600 mt-2 line-clamp-2">{hoveredEvent.description}</p>
            {hoveredEvent.mathematician && (
              <div className="flex items-center gap-1 mt-2 text-sm text-gray-500">
                <Users className="w-3 h-3" />
                <span>{hoveredEvent.mathematician}</span>
              </div>
            )}
          </div>
        )}

        {/* 选中事件详情 */}
        {selectedEvent && (
          <div className="absolute bottom-4 left-4 right-4 bg-white rounded-lg shadow-lg border border-gray-200 p-4 z-10">
            <div className="flex justify-between items-start">
              <div>
                <div className="flex items-center gap-2">
                  <span className="text-2xl">{EVENT_TYPE_CONFIG[selectedEvent.type].icon}</span>
                  <h4 className="font-semibold text-lg text-gray-800">{selectedEvent.title}</h4>
                </div>
                <p className="text-gray-600 mt-2">{selectedEvent.description}</p>
                <div className="flex items-center gap-4 mt-3 text-sm text-gray-500">
                  <span className="flex items-center gap-1">
                    <Calendar className="w-4 h-4" />
                    {selectedEvent.year}年
                  </span>
                  {selectedEvent.mathematician && (
                    <span className="flex items-center gap-1">
                      <Users className="w-4 h-4" />
                      {selectedEvent.mathematician}
                    </span>
                  )}
                  <span className="flex items-center gap-1">
                    <BookOpen className="w-4 h-4" />
                    影响力: {selectedEvent.impact}/10
                  </span>
                </div>
              </div>
              <button
                onClick={() => setSelectedEvent(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                ×
              </button>
            </div>
          </div>
        )}
      </div>

      {/* 图例 */}
      <div className="px-4 py-3 border-t border-gray-200 flex flex-wrap items-center gap-4">
        <span className="text-sm text-gray-500">事件类型:</span>
        {Object.entries(EVENT_TYPE_CONFIG).map(([type, config]) => (
          <div key={type} className="flex items-center gap-1.5">
            <span className="text-sm">{config.icon}</span>
            <span className="text-xs text-gray-600">{config.label}</span>
          </div>
        ))}
        <div className="ml-auto flex items-center gap-2">
          <GitBranch className="w-4 h-4 text-gray-400" />
          <span className="text-xs text-gray-500">共 {sortedEvents.length} 个事件</span>
        </div>
      </div>
    </div>
  );
};

export default ConceptTimeline;
