// @ts-nocheck
/**
 * 学习进度仪表板组件
 * 展示学习统计、趋势、里程碑和目标
 */

import React, { useEffect, useState, useMemo } from 'react';
import * as d3 from 'd3';
import { useD3 } from '@hooks/useD3';
import type { LearningProgressData, ProgressTrend, Milestone, LearningGoal } from '@types/analytics';

interface ProgressDashboardProps {
  data: LearningProgressData;
  onMilestoneClick?: (milestone: Milestone) => void;
  onGoalClick?: (goal: LearningGoal) => void;
  className?: string;
}

/**
 * 学习进度仪表板组件
 */
export const ProgressDashboard: React.FC<ProgressDashboardProps> = ({
  data,
  onMilestoneClick,
  onGoalClick,
  className = '',
}) => {
  const [activeTab, setActiveTab] = useState<'overview' | 'trends' | 'milestones' | 'goals'>('overview');

  return (
    <div className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg ${className}`}>
      {/* 标签栏 */}
      <div className="flex border-b border-gray-200 dark:border-slate-700">
        <TabButton active={activeTab === 'overview'} onClick={() => setActiveTab('overview')} label="总览" />
        <TabButton active={activeTab === 'trends'} onClick={() => setActiveTab('trends')} label="趋势" />
        <TabButton active={activeTab === 'milestones'} onClick={() => setActiveTab('milestones')} label="里程碑" />
        <TabButton active={activeTab === 'goals'} onClick={() => setActiveTab('goals')} label="目标" />
      </div>

      {/* 内容区域 */}
      <div className="p-6">
        {activeTab === 'overview' && <OverviewSection data={data} />}
        {activeTab === 'trends' && <TrendsSection trends={data.trends} />}
        {activeTab === 'milestones' && (
          <MilestonesSection milestones={data.milestones} onMilestoneClick={onMilestoneClick} />
        )}
        {activeTab === 'goals' && <GoalsSection goals={data.goals} onGoalClick={onGoalClick} />}
      </div>
    </div>
  );
};

// 标签按钮组件
const TabButton: React.FC<{
  active: boolean;
  onClick: () => void;
  label: string;
}> = ({ active, onClick, label }) => (
  <button
    onClick={onClick}
    className={`flex-1 py-3 px-4 text-sm font-medium transition-colors ${
      active
        ? 'text-blue-600 border-b-2 border-blue-600 dark:text-blue-400 dark:border-blue-400'
        : 'text-gray-600 hover:text-gray-900 dark:text-gray-400 dark:hover:text-gray-200'
    }`}
  >
    {label}
  </button>
);

// 总览区域
const OverviewSection: React.FC<{ data: LearningProgressData }> = ({ data }) => {
  const { summary } = data;

  const stats = useMemo(
    () => [
      { icon: '📚', label: '总概念', value: summary.totalConcepts, color: 'blue' },
      { icon: '✅', label: '已掌握', value: summary.masteredConcepts, color: 'green' },
      { icon: '📖', label: '学习中', value: summary.inProgressConcepts, color: 'yellow' },
      { icon: '⏱️', label: '总时长(小时)', value: Math.round(summary.totalTimeSpent / 60), color: 'purple' },
    ],
    [summary]
  );

  return (
    <div className="space-y-6">
      {/* 统计卡片 */}
      <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
        {stats.map((stat) => (
          <StatCard key={stat.label} {...stat} />
        ))}
      </div>

      {/* 总体进度 */}
      <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
        <div className="flex items-center justify-between mb-2">
          <span className="text-gray-700 dark:text-gray-300 font-medium">总体进度</span>
          <span className="text-2xl font-bold text-blue-600 dark:text-blue-400">
            {summary.overallProgress}%
          </span>
        </div>
        <ProgressBar progress={summary.overallProgress} size="lg" />
        <div className="mt-2 text-sm text-gray-500 dark:text-gray-400">
          平均掌握度: <span className="font-medium">{summary.averageMastery}%</span> | 
          日均学习: <span className="font-medium">{Math.round(summary.dailyAverage)} 分钟</span>
        </div>
      </div>

      {/* 掌握度分布 */}
      <MasteryDistribution mastered={summary.masteredConcepts} inProgress={summary.inProgressConcepts} notStarted={summary.notStartedConcepts} />
    </div>
  );
};

// 统计卡片
const StatCard: React.FC<{
  icon: string;
  label: string;
  value: number;
  color: string;
}> = ({ icon, label, value, color }) => {
  const colorClasses: Record<string, string> = {
    blue: 'bg-blue-50 text-blue-600 dark:bg-blue-900/30 dark:text-blue-400',
    green: 'bg-green-50 text-green-600 dark:bg-green-900/30 dark:text-green-400',
    yellow: 'bg-yellow-50 text-yellow-600 dark:bg-yellow-900/30 dark:text-yellow-400',
    purple: 'bg-purple-50 text-purple-600 dark:bg-purple-900/30 dark:text-purple-400',
  };

  return (
    <div className={`${colorClasses[color]} rounded-lg p-4 text-center`}>
      <div className="text-2xl mb-1">{icon}</div>
      <div className="text-2xl font-bold">{value}</div>
      <div className="text-sm opacity-80">{label}</div>
    </div>
  );
};

// 进度条
const ProgressBar: React.FC<{ progress: number; size?: 'sm' | 'md' | 'lg' }> = ({ progress, size = 'md' }) => {
  const heightClasses = {
    sm: 'h-1',
    md: 'h-2',
    lg: 'h-3',
  };

  return (
    <div className={`w-full bg-gray-200 dark:bg-slate-600 rounded-full overflow-hidden ${heightClasses[size]}`}>
      <div
        className="h-full bg-gradient-to-r from-blue-500 to-blue-600 transition-all duration-500"
        style={{ width: `${progress}%` }}
      />
    </div>
  );
};

// 掌握度分布
const MasteryDistribution: React.FC<{
  mastered: number;
  inProgress: number;
  notStarted: number;
}> = ({ mastered, inProgress, notStarted }) => {
  const total = mastered + inProgress + notStarted;
  if (total === 0) return null;

  const items = [
    { label: '已掌握', value: mastered, color: 'bg-green-500', width: (mastered / total) * 100 },
    { label: '学习中', value: inProgress, color: 'bg-yellow-500', width: (inProgress / total) * 100 },
    { label: '未开始', value: notStarted, color: 'bg-gray-300 dark:bg-gray-600', width: (notStarted / total) * 100 },
  ];

  return (
    <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
      <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 mb-3">掌握度分布</h4>
      
      {/* 堆叠条形图 */}
      <div className="h-8 flex rounded-full overflow-hidden">
        {items.map((item) =>
          item.value > 0 ? (
            <div
              key={item.label}
              className={`${item.color} h-full transition-all duration-500`}
              style={{ width: `${item.width}%` }}
              title={`${item.label}: ${item.value} (${Math.round(item.width)}%)`}
            />
          ) : null
        )}
      </div>

      {/* 图例 */}
      <div className="flex gap-4 mt-3">
        {items.map((item) => (
          <div key={item.label} className="flex items-center gap-1">
            <div className={`w-3 h-3 rounded ${item.color}`} />
            <span className="text-xs text-gray-600 dark:text-gray-400">
              {item.label}: {item.value}
            </span>
          </div>
        ))}
      </div>
    </div>
  );
};

// 趋势区域
const TrendsSection: React.FC<{ trends: ProgressTrend[] }> = ({ trends }) => {
  const svgRef = useD3(
    (svg) => {
      if (trends.length === 0) return;

      const margin = { top: 20, right: 30, bottom: 40, left: 50 };
      const width = 800 - margin.left - margin.right;
      const height = 300 - margin.top - margin.bottom;

      svg.selectAll('*').remove();

      const g = svg
        .attr('width', width + margin.left + margin.right)
        .attr('height', height + margin.top + margin.bottom)
        .append('g')
        .attr('transform', `translate(${margin.left},${margin.top})`);

      // 解析日期
      const parseDate = d3.timeParse('%Y-%m-%d');
      const data = trends.map((d) => ({
        ...d,
        date: parseDate(d.date) as Date,
      }));

      // 比例尺
      const x = d3.scaleTime().domain(d3.extent(data, (d) => d.date) as [Date, Date]).range([0, width]);

      const y = d3.scaleLinear().domain([0, d3.max(data, (d) => d.masteryGrowth) || 0]).nice().range([height, 0]);

      // 网格线
      g.append('g')
        .attr('class', 'grid')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x).tickSize(-height).tickFormat(() => ''))
        .style('stroke-dasharray', '3,3')
        .style('opacity', 0.1);

      g.append('g')
        .attr('class', 'grid')
        .call(d3.axisLeft(y).tickSize(-width).tickFormat(() => ''))
        .style('stroke-dasharray', '3,3')
        .style('opacity', 0.1);

      // X轴
      g.append('g')
        .attr('transform', `translate(0,${height})`)
        .call(d3.axisBottom(x).tickFormat(d3.timeFormat('%m/%d') as any))
        .style('color', '#6b7280');

      // Y轴
      g.append('g').call(d3.axisLeft(y)).style('color', '#6b7280');

      // 线条生成器
      const line = d3
        .line<{ date: Date; masteryGrowth: number }>()
        .x((d) => x(d.date))
        .y((d) => y(d.masteryGrowth))
        .curve(d3.curveMonotoneX);

      // 绘制线条
      g.append('path')
        .datum(data)
        .attr('fill', 'none')
        .attr('stroke', '#3b82f6')
        .attr('stroke-width', 2)
        .attr('d', line);

      // 数据点
      g.selectAll('.dot')
        .data(data)
        .enter()
        .append('circle')
        .attr('class', 'dot')
        .attr('cx', (d) => x(d.date))
        .attr('cy', (d) => y(d.masteryGrowth))
        .attr('r', 4)
        .attr('fill', '#3b82f6')
        .attr('stroke', '#fff')
        .attr('stroke-width', 2);

      // Y轴标签
      g.append('text')
        .attr('transform', 'rotate(-90)')
        .attr('y', 0 - margin.left)
        .attr('x', 0 - height / 2)
        .attr('dy', '1em')
        .style('text-anchor', 'middle')
        .style('fill', '#6b7280')
        .style('font-size', '12px')
        .text('掌握度增长');
    },
    [trends]
  );

  if (trends.length === 0) {
    return (
      <div className="text-center py-8 text-gray-500 dark:text-gray-400">暂无趋势数据</div>
    );
  }

  return (
    <div className="space-y-4">
      <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300">掌握度增长趋势</h4>
      <div className="overflow-x-auto">
        <svg ref={svgRef} className="w-full min-w-[600px]" />
      </div>
    </div>
  );
};

// 里程碑区域
const MilestonesSection: React.FC<{
  milestones: Milestone[];
  onMilestoneClick?: (milestone: Milestone) => void;
}> = ({ milestones, onMilestoneClick }) => {
  if (milestones.length === 0) {
    return (
      <div className="text-center py-8 text-gray-500 dark:text-gray-400">暂无里程碑</div>
    );
  }

  const getStatusColor = (status: Milestone['status']) => {
    const colors: Record<string, string> = {
      pending: 'bg-gray-100 text-gray-600 dark:bg-slate-700 dark:text-gray-400',
      in_progress: 'bg-blue-100 text-blue-600 dark:bg-blue-900/30 dark:text-blue-400',
      achieved: 'bg-green-100 text-green-600 dark:bg-green-900/30 dark:text-green-400',
      overdue: 'bg-red-100 text-red-600 dark:bg-red-900/30 dark:text-red-400',
    };
    return colors[status] || colors.pending;
  };

  const getStatusLabel = (status: Milestone['status']) => {
    const labels: Record<string, string> = {
      pending: '待开始',
      in_progress: '进行中',
      achieved: '已完成',
      overdue: '已逾期',
    };
    return labels[status] || status;
  };

  return (
    <div className="space-y-3">
      {milestones.map((milestone) => (
        <div
          key={milestone.id}
          onClick={() => onMilestoneClick?.(milestone)}
          className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4 cursor-pointer hover:shadow-md transition-shadow"
        >
          <div className="flex items-start justify-between">
            <div className="flex-1">
              <div className="flex items-center gap-2">
                <h4 className="font-medium text-gray-800 dark:text-gray-200">{milestone.title}</h4>
                <span className={`text-xs px-2 py-0.5 rounded-full ${getStatusColor(milestone.status)}`}>
                  {getStatusLabel(milestone.status)}
                </span>
              </div>
              <p className="text-sm text-gray-600 dark:text-gray-400 mt-1">{milestone.description}</p>
              
              {/* 进度条 */}
              <div className="mt-3">
                <div className="flex justify-between text-xs text-gray-500 dark:text-gray-400 mb-1">
                  <span>
                    进度: {milestone.completedConcepts}/{milestone.targetConcepts}
                  </span>
                  <span>{milestone.progress}%</span>
                </div>
                <ProgressBar progress={milestone.progress} size="sm" />
              </div>

              {milestone.deadline && (
                <div className="text-xs text-gray-500 dark:text-gray-400 mt-2">
                  截止日期: {new Date(milestone.deadline).toLocaleDateString('zh-CN')}
                </div>
              )}
            </div>
          </div>
        </div>
      ))}
    </div>
  );
};

// 目标区域
const GoalsSection: React.FC<{
  goals: LearningGoal[];
  onGoalClick?: (goal: LearningGoal) => void;
}> = ({ goals, onGoalClick }) => {
  if (goals.length === 0) {
    return (
      <div className="text-center py-8 text-gray-500 dark:text-gray-400">暂无学习目标</div>
    );
  }

  return (
    <div className="space-y-3">
      {goals.map((goal) => (
        <div
          key={goal.id}
          onClick={() => onGoalClick?.(goal)}
          className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4 cursor-pointer hover:shadow-md transition-shadow"
        >
          <div className="flex items-center justify-between">
            <div className="flex-1">
              <h4 className="font-medium text-gray-800 dark:text-gray-200">{goal.title}</h4>
              <p className="text-sm text-gray-600 dark:text-gray-400 mt-1">{goal.description}</p>
              
              <div className="flex items-center gap-4 mt-3">
                <div className="flex-1">
                  <div className="flex justify-between text-xs text-gray-500 dark:text-gray-400 mb-1">
                    <span>
                      {goal.currentValue} / {goal.targetValue} {goal.unit}
                    </span>
                    <span>{goal.progress}%</span>
                  </div>
                  <ProgressBar progress={goal.progress} size="sm" />
                </div>
                <span
                  className={`text-xs px-2 py-1 rounded ${
                    goal.status === 'completed'
                      ? 'bg-green-100 text-green-600 dark:bg-green-900/30 dark:text-green-400'
                      : goal.status === 'abandoned'
                      ? 'bg-gray-100 text-gray-600 dark:bg-slate-600 dark:text-gray-400'
                      : 'bg-blue-100 text-blue-600 dark:bg-blue-900/30 dark:text-blue-400'
                  }`}
                >
                  {goal.status === 'completed' ? '已完成' : goal.status === 'abandoned' ? '已放弃' : '进行中'}
                </span>
              </div>
            </div>
          </div>
        </div>
      ))}
    </div>
  );
};

export default ProgressDashboard;
