/**
 * 学习效率分析组件
 * 展示学习时间分布、效率和优化建议
 */

import React, { useMemo, useState } from 'react';
import * as d3 from 'd3';
import { useD3 } from '@hooks/useD3';
import type { EfficiencyAnalysisData, HourlyData, DayOfWeekData, LearningPattern } from '@types/analytics';

interface EfficiencyAnalysisProps {
  data: EfficiencyAnalysisData;
  className?: string;
}

type AnalysisView = 'overview' | 'hourly' | 'weekly' | 'patterns';

/**
 * 学习效率分析组件
 */
export const EfficiencyAnalysis: React.FC<EfficiencyAnalysisProps> = ({
  data,
  className = '',
}) => {
  const [activeView, setActiveView] = useState<AnalysisView>('overview');

  // 计算最佳学习时间
  const optimalHours = useMemo(() => {
    return data.timeDistribution.byHour
      .filter((h) => h.avgEfficiency >= 80)
      .map((h) => h.hour)
      .sort((a, b) => a - b);
  }, [data.timeDistribution.byHour]);

  return (
    <div className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg ${className}`}>
      {/* 头部 */}
      <div className="p-4 border-b border-gray-200 dark:border-slate-700">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <div>
            <h3 className="text-lg font-semibold text-gray-800 dark:text-gray-200">学习效率分析</h3>
            <p className="text-sm text-gray-500 dark:text-gray-400 mt-1">
              总体效率: <span className="font-medium text-blue-600 dark:text-blue-400">{data.overallEfficiency}%</span>
            </p>
          </div>

          {/* 视图切换 */}
          <div className="flex bg-gray-100 dark:bg-slate-700 rounded-lg p-1">
            {[
              { key: 'overview', label: '总览' },
              { key: 'hourly', label: '时段' },
              { key: 'weekly', label: '星期' },
              { key: 'patterns', label: '模式' },
            ].map((view) => (
              <button
                key={view.key}
                onClick={() => setActiveView(view.key as AnalysisView)}
                className={`px-3 py-1.5 text-sm rounded-md transition-colors ${
                  activeView === view.key
                    ? 'bg-white dark:bg-slate-600 text-blue-600 dark:text-blue-400 shadow-sm'
                    : 'text-gray-600 dark:text-gray-400 hover:text-gray-900 dark:hover:text-gray-200'
                }`}
              >
                {view.label}
              </button>
            ))}
          </div>
        </div>

        {/* 最佳学习时间 */}
        {optimalHours.length > 0 && (
          <div className="mt-3 text-sm">
            <span className="text-gray-500 dark:text-gray-400">最佳学习时间: </span>
            <span className="text-green-600 dark:text-green-400 font-medium">
              {optimalHours.map((h) => `${h}:00`).join(', ')}
            </span>
          </div>
        )}
      </div>

      {/* 内容区域 */}
      <div className="p-4">
        {activeView === 'overview' && <OverviewView data={data} />}
        {activeView === 'hourly' && <HourlyView data={data.timeDistribution.byHour} />}
        {activeView === 'weekly' && <WeeklyView data={data.timeDistribution.byDayOfWeek} />}
        {activeView === 'patterns' && <PatternsView patterns={data.learningPatterns} recommendations={data.recommendations} />}
      </div>
    </div>
  );
};

// 总览视图
const OverviewView: React.FC<{ data: EfficiencyAnalysisData }> = ({ data }) => {
  return (
    <div className="space-y-6">
      {/* 关键指标 */}
      <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
        <MetricCard
          label="总体效率"
          value={`${data.overallEfficiency}%`}
          trend={data.overallEfficiency >= 70 ? 'good' : data.overallEfficiency >= 50 ? 'average' : 'poor'}
        />
        <MetricCard
          label="最佳时段效率"
          value={`${Math.max(...data.timeDistribution.byHour.map((h) => h.avgEfficiency))}%`}
          trend="good"
        />
        <MetricCard
          label="学习模式数"
          value={data.learningPatterns.length}
          trend="neutral"
        />
        <MetricCard
          label="优化建议"
          value={data.recommendations.length}
          trend={data.recommendations.length > 0 ? 'attention' : 'good'}
        />
      </div>

      {/* 最优条件 */}
      {data.optimalConditions.length > 0 && (
        <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">最优学习条件</h4>
          <div className="space-y-2">
            {data.optimalConditions.map((condition, index) => (
              <div
                key={index}
                className="flex items-center justify-between py-2 border-b border-gray-200 dark:border-slate-600 last:border-0"
              >
                <div>
                  <span className="text-sm text-gray-700 dark:text-gray-300">{condition.factor}</span>
                  <span className="text-xs text-gray-500 dark:text-gray-400 ml-2">({condition.optimalValue})</span>
                </div>
                <div className="text-right">
                  <span className="text-sm font-medium text-green-600 dark:text-green-400">
                    +{condition.impact}%
                  </span>
                  <span className="text-xs text-gray-500 dark:text-gray-400 ml-2">
                    置信度: {Math.round(condition.confidence * 100)}%
                  </span>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 会话长度效率 */}
      <SessionLengthChart data={data.timeDistribution.bySessionLength} />
    </div>
  );
};

// 指标卡片
const MetricCard: React.FC<{
  label: string;
  value: string | number;
  trend: 'good' | 'average' | 'poor' | 'neutral' | 'attention';
}> = ({ label, value, trend }) => {
  const trendColors = {
    good: 'text-green-600 dark:text-green-400',
    average: 'text-yellow-600 dark:text-yellow-400',
    poor: 'text-red-600 dark:text-red-400',
    neutral: 'text-gray-600 dark:text-gray-400',
    attention: 'text-orange-600 dark:text-orange-400',
  };

  const trendIcons = {
    good: '✓',
    average: '~',
    poor: '✗',
    neutral: '-',
    attention: '!',
  };

  return (
    <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-3">
      <div className="text-xs text-gray-500 dark:text-gray-400 mb-1">{label}</div>
      <div className={`text-xl font-bold ${trendColors[trend]}`}>
        {value}
        <span className="text-sm ml-1">{trendIcons[trend]}</span>
      </div>
    </div>
  );
};

// 会话长度效率图表
const SessionLengthChart: React.FC<{
  data: EfficiencyAnalysisData['timeDistribution']['bySessionLength'];
}> = ({ data }) => {
  const svgRef = useD3(
    (svg) => {
      if (data.length === 0) return;

      const margin = { top: 20, right: 30, bottom: 60, left: 50 };
      const width = 600 - margin.left - margin.right;
      const height = 250 - margin.top - margin.bottom;

      svg.selectAll('*').remove();

      const g = svg
        .attr('width', width + margin.left + margin.right)
        .attr('height', height + margin.top + margin.bottom)
        .append('g')
        .attr('transform', `translate(${margin.left},${margin.top})`);

      // 比例尺
      const x = d3.scaleBand().domain(data.map((d) => d.range)).range([0, width]).padding(0.2);

      const y = d3.scaleLinear().domain([0, 100]).nice().range([height, 0]);

      // X轴
      g.append('g')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x))
        .selectAll('text')
        .style('text-anchor', 'end')
        .attr('dx', '-.8em')
        .attr('dy', '.15em')
        .attr('transform', 'rotate(-45)')
        .style('fill', '#6b7280');

      // Y轴
      g.append('g').call(d3.axisLeft(y).ticks(5).tickFormat((d) => `${d}%`)).style('color', '#6b7280');

      // 柱状图
      g.selectAll('.bar')
        .data(data)
        .enter()
        .append('rect')
        .attr('class', 'bar')
        .attr('x', (d) => x(d.range) || 0)
        .attr('width', x.bandwidth())
        .attr('y', (d) => y(d.avgEfficiency))
        .attr('height', (d) => height - y(d.avgEfficiency))
        .attr('fill', (d) => (d.avgEfficiency >= 80 ? '#22c55e' : d.avgEfficiency >= 60 ? '#eab308' : '#ef4444'))
        .attr('rx', 4);

      // 数值标签
      g.selectAll('.label')
        .data(data)
        .enter()
        .append('text')
        .attr('class', 'label')
        .attr('x', (d) => (x(d.range) || 0) + x.bandwidth() / 2)
        .attr('y', (d) => y(d.avgEfficiency) - 5)
        .attr('text-anchor', 'middle')
        .style('font-size', '11px')
        .style('fill', '#6b7280')
        .text((d) => `${d.avgEfficiency}%`);

      // 标题
      g.append('text')
        .attr('x', width / 2)
        .attr('y', -5)
        .attr('text-anchor', 'middle')
        .style('font-size', '12px')
        .style('fill', '#374151')
        .text('不同学习时长的效率分析');
    },
    [data]
  );

  return (
    <div>
      <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">学习时长效率</h4>
      <div className="overflow-x-auto">
        <svg ref={svgRef} />
      </div>
    </div>
  );
};

// 时段视图
const HourlyView: React.FC<{ data: HourlyData[] }> = ({ data }) => {
  const svgRef = useD3(
    (svg) => {
      if (data.length === 0) return;

      const margin = { top: 20, right: 30, bottom: 40, left: 50 };
      const width = 700 - margin.left - margin.right;
      const height = 250 - margin.top - margin.bottom;

      svg.selectAll('*').remove();

      const g = svg
        .attr('width', width + margin.left + margin.right)
        .attr('height', height + margin.top + margin.bottom)
        .append('g')
        .attr('transform', `translate(${margin.left},${margin.top})`);

      // 比例尺
      const x = d3.scaleLinear().domain([0, 23]).range([0, width]);
      const y = d3.scaleLinear().domain([0, 100]).range([height, 0]);

      // 区域生成器
      const area = d3
        .area<HourlyData>()
        .x((d) => x(d.hour))
        .y0(height)
        .y1((d) => y(d.avgEfficiency))
        .curve(d3.curveMonotoneX);

      // 线条生成器
      const line = d3
        .line<HourlyData>()
        .x((d) => x(d.hour))
        .y((d) => y(d.avgEfficiency))
        .curve(d3.curveMonotoneX);

      // 绘制区域
      g.append('path')
        .datum(data)
        .attr('fill', 'url(#gradient)')
        .attr('d', area);

      // 渐变色
      const defs = svg.append('defs');
      const gradient = defs
        .append('linearGradient')
        .attr('id', 'gradient')
        .attr('x1', '0%')
        .attr('y1', '0%')
        .attr('x2', '0%')
        .attr('y2', '100%');
      gradient.append('stop').attr('offset', '0%').attr('stop-color', '#3b82f6').attr('stop-opacity', 0.3);
      gradient.append('stop').attr('offset', '100%').attr('stop-color', '#3b82f6').attr('stop-opacity', 0.05);

      // 绘制线条
      g.append('path').datum(data).attr('fill', 'none').attr('stroke', '#3b82f6').attr('stroke-width', 2).attr('d', line);

      // X轴
      g.append('g')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x).ticks(12).tickFormat((d) => `${d}:00`))
        .style('color', '#6b7280');

      // Y轴
      g.append('g').call(d3.axisLeft(y).ticks(5).tickFormat((d) => `${d}%`)).style('color', '#6b7280');

      // 数据点
      g.selectAll('.dot')
        .data(data.filter((d) => d.avgEfficiency > 0))
        .enter()
        .append('circle')
        .attr('class', 'dot')
        .attr('cx', (d) => x(d.hour))
        .attr('cy', (d) => y(d.avgEfficiency))
        .attr('r', (d) => (d.avgEfficiency >= 80 ? 5 : 3))
        .attr('fill', (d) => (d.avgEfficiency >= 80 ? '#22c55e' : '#3b82f6'))
        .attr('stroke', '#fff')
        .attr('stroke-width', 1);
    },
    [data]
  );

  return (
    <div>
      <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">24小时学习效率分布</h4>
      <div className="overflow-x-auto">
        <svg ref={svgRef} className="w-full min-w-[600px]" />
      </div>
      <div className="flex justify-center gap-4 mt-3 text-xs text-gray-500 dark:text-gray-400">
        <span className="flex items-center gap-1">
          <span className="w-3 h-3 rounded-full bg-green-500" /> 高效时段 (≥80%)
        </span>
        <span className="flex items-center gap-1">
          <span className="w-3 h-3 rounded-full bg-blue-500" /> 普通时段
        </span>
      </div>
    </div>
  );
};

// 星期视图
const WeeklyView: React.FC<{ data: DayOfWeekData[] }> = ({ data }) => {
  const svgRef = useD3(
    (svg) => {
      if (data.length === 0) return;

      const margin = { top: 20, right: 30, bottom: 40, left: 50 };
      const width = 500 - margin.left - margin.right;
      const height = 250 - margin.top - margin.bottom;

      svg.selectAll('*').remove();

      const g = svg
        .attr('width', width + margin.left + margin.right)
        .attr('height', height + margin.top + margin.bottom)
        .append('g')
        .attr('transform', `translate(${margin.left},${margin.top})`);

      // 比例尺
      const x = d3.scaleBand().domain(data.map((d) => d.dayName)).range([0, width]).padding(0.3);

      const y = d3.scaleLinear().domain([0, 100]).nice().range([height, 0]);

      // 柱状图
      g.selectAll('.bar')
        .data(data)
        .enter()
        .append('rect')
        .attr('class', 'bar')
        .attr('x', (d) => x(d.dayName) || 0)
        .attr('width', x.bandwidth())
        .attr('y', (d) => y(d.avgEfficiency))
        .attr('height', (d) => height - y(d.avgEfficiency))
        .attr('fill', (d) => (d.avgEfficiency >= 80 ? '#22c55e' : d.avgEfficiency >= 60 ? '#eab308' : '#ef4444'))
        .attr('rx', 4);

      // X轴
      g.append('g')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x))
        .style('color', '#6b7280');

      // Y轴
      g.append('g').call(d3.axisLeft(y).ticks(5).tickFormat((d) => `${d}%`)).style('color', '#6b7280');

      // 数值标签
      g.selectAll('.label')
        .data(data)
        .enter()
        .append('text')
        .attr('class', 'label')
        .attr('x', (d) => (x(d.dayName) || 0) + x.bandwidth() / 2)
        .attr('y', (d) => y(d.avgEfficiency) - 5)
        .attr('text-anchor', 'middle')
        .style('font-size', '11px')
        .style('fill', '#6b7280')
        .text((d) => `${d.avgEfficiency}%`);
    },
    [data]
  );

  return (
    <div>
      <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">每周学习效率分布</h4>
      <div className="overflow-x-auto">
        <svg ref={svgRef} />
      </div>
    </div>
  );
};

// 模式和建议视图
const PatternsView: React.FC<{
  patterns: LearningPattern[];
  recommendations: EfficiencyAnalysisData['recommendations'];
}> = ({ patterns, recommendations }) => {
  return (
    <div className="space-y-6">
      {/* 学习模式 */}
      {patterns.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">检测到的学习模式</h4>
          <div className="space-y-3">
            {patterns.map((pattern) => (
              <div
                key={pattern.id}
                className="bg-gray-50 dark:bg-slate-700 rounded-lg p-3 flex items-center justify-between"
              >
                <div>
                  <div className="font-medium text-gray-800 dark:text-gray-200">{pattern.name}</div>
                  <div className="text-xs text-gray-500 dark:text-gray-400 mt-0.5">{pattern.description}</div>
                </div>
                <div className="text-right">
                  <div className="text-sm font-medium text-gray-800 dark:text-gray-200">{pattern.avgEfficiency}% 效率</div>
                  <div
                    className={`text-xs ${
                      pattern.trend === 'improving'
                        ? 'text-green-600 dark:text-green-400'
                        : pattern.trend === 'declining'
                        ? 'text-red-600 dark:text-red-400'
                        : 'text-gray-500 dark:text-gray-400'
                    }`}
                  >
                    {pattern.trend === 'improving' ? '↗ 改善中' : pattern.trend === 'declining' ? '↘ 下滑中' : '→ 稳定'}
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 效率建议 */}
      {recommendations.length > 0 && (
        <div>
          <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">优化建议</h4>
          <div className="space-y-3">
            {recommendations.map((rec) => (
              <div
                key={rec.id}
                className={`rounded-lg p-3 border-l-4 ${
                  rec.priority === 'high'
                    ? 'bg-red-50 border-red-500 dark:bg-red-900/20 dark:border-red-400'
                    : rec.priority === 'medium'
                    ? 'bg-yellow-50 border-yellow-500 dark:bg-yellow-900/20 dark:border-yellow-400'
                    : 'bg-blue-50 border-blue-500 dark:bg-blue-900/20 dark:border-blue-400'
                }`}
              >
                <div className="flex items-start justify-between">
                  <div>
                    <div className="font-medium text-gray-800 dark:text-gray-200">{rec.title}</div>
                    <div className="text-sm text-gray-600 dark:text-gray-400 mt-1">{rec.description}</div>
                  </div>
                  <span
                    className={`text-xs px-2 py-0.5 rounded ${
                      rec.priority === 'high'
                        ? 'bg-red-100 text-red-700 dark:bg-red-900/30 dark:text-red-400'
                        : rec.priority === 'medium'
                        ? 'bg-yellow-100 text-yellow-700 dark:bg-yellow-900/30 dark:text-yellow-400'
                        : 'bg-blue-100 text-blue-700 dark:bg-blue-900/30 dark:text-blue-400'
                    }`}
                  >
                    {rec.priority === 'high' ? '高优先级' : rec.priority === 'medium' ? '中优先级' : '低优先级'}
                  </span>
                </div>
                <div className="text-xs text-green-600 dark:text-green-400 mt-2">
                  预期提升: +{rec.expectedImprovement}% 效率
                </div>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

export default EfficiencyAnalysis;
