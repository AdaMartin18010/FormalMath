/**
 * 播放统计组件
 * 显示视频观看统计数据和分析
 */

import React, { useState, useMemo } from 'react';
import {
  BarChart3,
  TrendingUp,
  TrendingDown,
  Users,
  Clock,
  Play,
  Heart,
  Share2,
  Calendar,
  Download,
  MoreHorizontal,
  ChevronDown,
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { PlaybackStats, HourlyStat } from '../../types/video';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

// 播放统计组件 Props
export interface PlaybackStatsProps {
  stats: PlaybackStats;
  className?: string;
}

// 时间段类型
 type TimeRange = '24h' | '7d' | '30d' | '90d' | '1y' | 'all';

export const PlaybackStatsView: React.FC<PlaybackStatsProps> = ({
  stats,
  className,
}) => {
  const [timeRange, setTimeRange] = useState<TimeRange>('7d');
  const [activeMetric, setActiveMetric] = useState<'views' | 'watchTime' | 'engagement'>('views');

  // 计算统计数据
  const statsData = useMemo(() => {
    const totalViews = stats.totalViews;
    const uniqueViewers = stats.uniqueViewers;
    const avgWatchTime = stats.averageWatchTime;
    const completionRate = stats.completionRate;
    
    // 计算趋势（模拟数据，实际应从历史数据计算）
    const viewsTrend = 12.5;
    const watchTimeTrend = -5.2;
    const engagementTrend = 8.7;

    return {
      totalViews,
      uniqueViewers,
      avgWatchTime,
      completionRate,
      viewsTrend,
      watchTimeTrend,
      engagementTrend,
    };
  }, [stats]);

  // 格式化数字
  const formatNumber = (num: number): string => {
    if (num >= 1000000) {
      return `${(num / 1000000).toFixed(1)}M`;
    }
    if (num >= 1000) {
      return `${(num / 1000).toFixed(1)}K`;
    }
    return num.toString();
  };

  // 格式化时长
  const formatDuration = (seconds: number): string => {
    if (seconds < 60) {
      return `${Math.round(seconds)}秒`;
    }
    const mins = Math.floor(seconds / 60);
    if (mins < 60) {
      return `${mins}分钟`;
    }
    const hours = Math.floor(mins / 60);
    const remainingMins = mins % 60;
    return `${hours}小时${remainingMins}分钟`;
  };

  // 格式化百分比
  const formatPercent = (value: number): string => {
    const sign = value >= 0 ? '+' : '';
    return `${sign}${value.toFixed(1)}%`;
  };

  const timeRangeOptions: { value: TimeRange; label: string }[] = [
    { value: '24h', label: '24小时' },
    { value: '7d', label: '7天' },
    { value: '30d', label: '30天' },
    { value: '90d', label: '90天' },
    { value: '1y', label: '1年' },
    { value: 'all', label: '全部' },
  ];

  return (
    <div className={cn('space-y-6', className)}>
      {/* 头部 */}
      <div className="flex flex-wrap items-center justify-between gap-4">
        <h2 className="text-xl font-bold text-white flex items-center gap-2">
          <BarChart3 className="w-5 h-5" />
          播放统计
        </h2>
        
        {/* 时间范围选择 */}
        <div className="flex items-center gap-2">
          {timeRangeOptions.map((option) => (
            <button
              key={option.value}
              onClick={() => setTimeRange(option.value)}
              className={cn(
                'px-3 py-1.5 rounded-lg text-sm transition-colors',
                timeRange === option.value
                  ? 'bg-blue-500 text-white'
                  : 'text-white/60 hover:text-white hover:bg-white/10'
              )}
            >
              {option.label}
            </button>
          ))}
        </div>
      </div>

      {/* 核心指标卡片 */}
      <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4">
        <StatCard
          title="总观看次数"
          value={formatNumber(statsData.totalViews)}
          trend={statsData.viewsTrend}
          icon={<Play className="w-5 h-5" />}
        />
        <StatCard
          title="独立观众"
          value={formatNumber(statsData.uniqueViewers)}
          trend={statsData.viewsTrend * 0.8}
          icon={<Users className="w-5 h-5" />}
        />
        <StatCard
          title="平均观看时长"
          value={formatDuration(statsData.avgWatchTime)}
          trend={statsData.watchTimeTrend}
          icon={<Clock className="w-5 h-5" />}
        />
        <StatCard
          title="完播率"
          value={`${(statsData.completionRate * 100).toFixed(1)}%`}
          trend={statsData.engagementTrend}
          icon={<BarChart3 className="w-5 h-5" />}
        />
      </div>

      {/* 图表区域 */}
      <div className="bg-gray-900 rounded-lg p-4">
        {/* 图表类型切换 */}
        <div className="flex items-center gap-2 mb-4">
          {(['views', 'watchTime', 'engagement'] as const).map((metric) => (
            <button
              key={metric}
              onClick={() => setActiveMetric(metric)}
              className={cn(
                'px-3 py-1.5 rounded-lg text-sm transition-colors',
                activeMetric === metric
                  ? 'bg-blue-500 text-white'
                  : 'text-white/60 hover:text-white hover:bg-white/10'
              )}
            >
              {metric === 'views' && '观看次数'}
              {metric === 'watchTime' && '观看时长'}
              {metric === 'engagement' && '互动率'}
            </button>
          ))}
        </div>

        {/* 图表占位 */}
        <div className="h-64 bg-gray-800 rounded-lg flex items-center justify-center">
          <SimpleBarChart data={stats.hourlyStats} metric={activeMetric} />
        </div>
      </div>

      {/* 详细数据表格 */}
      <div className="bg-gray-900 rounded-lg overflow-hidden">
        <div className="px-4 py-3 border-b border-white/10">
          <h3 className="text-white font-medium">每小时统计</h3>
        </div>
        <div className="overflow-x-auto">
          <table className="w-full">
            <thead>
              <tr className="bg-gray-800">
                <th className="px-4 py-2 text-left text-white/60 text-sm font-medium">时间</th>
                <th className="px-4 py-2 text-right text-white/60 text-sm font-medium">观看次数</th>
                <th className="px-4 py-2 text-right text-white/60 text-sm font-medium">平均观看时长</th>
                <th className="px-4 py-2 text-right text-white/60 text-sm font-medium">完播率</th>
              </tr>
            </thead>
            <tbody>
              {stats.hourlyStats.slice(-10).map((stat, index) => (
                <tr key={index} className="border-b border-white/5 hover:bg-white/5 transition-colors">
                  <td className="px-4 py-3 text-white text-sm">{stat.hour}</td>
                  <td className="px-4 py-3 text-white text-sm text-right">{formatNumber(stat.views)}</td>
                  <td className="px-4 py-3 text-white text-sm text-right">{formatDuration(stat.avgWatchTime)}</td>
                  <td className="px-4 py-3 text-white text-sm text-right">
                    {((stat.avgWatchTime / (stats.averageWatchTime * 2)) * 100).toFixed(1)}%
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      {/* 互动数据 */}
      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <EngagementCard
          title="点赞数"
          value={formatNumber(Math.floor(stats.totalViews * 0.1))}
          icon={<Heart className="w-5 h-5" />}
          color="text-red-400"
        />
        <EngagementCard
          title="分享数"
          value={formatNumber(Math.floor(stats.totalViews * 0.05))}
          icon={<Share2 className="w-5 h-5" />}
          color="text-blue-400"
        />
        <EngagementCard
          title="收藏数"
          value={formatNumber(Math.floor(stats.totalViews * 0.03))}
          icon={<BarChart3 className="w-5 h-5" />}
          color="text-yellow-400"
        />
      </div>
    </div>
  );
};

// 统计卡片
interface StatCardProps {
  title: string;
  value: string;
  trend: number;
  icon: React.ReactNode;
}

const StatCard: React.FC<StatCardProps> = ({ title, value, trend, icon }) => {
  const isPositive = trend >= 0;

  return (
    <div className="bg-gray-900 rounded-lg p-4">
      <div className="flex items-start justify-between">
        <div className="p-2 bg-blue-500/20 rounded-lg text-blue-400">
          {icon}
        </div>
        <div className={cn(
          'flex items-center gap-1 text-sm',
          isPositive ? 'text-green-400' : 'text-red-400'
        )}>
          {isPositive ? <TrendingUp className="w-4 h-4" /> : <TrendingDown className="w-4 h-4" />}
          <span>{Math.abs(trend).toFixed(1)}%</span>
        </div>
      </div>
      <div className="mt-3">
        <div className="text-2xl font-bold text-white">{value}</div>
        <div className="text-white/50 text-sm mt-1">{title}</div>
      </div>
    </div>
  );
};

// 互动卡片
interface EngagementCardProps {
  title: string;
  value: string;
  icon: React.ReactNode;
  color: string;
}

const EngagementCard: React.FC<EngagementCardProps> = ({ title, value, icon, color }) => {
  return (
    <div className="bg-gray-900 rounded-lg p-4 flex items-center gap-4">
      <div className={cn('p-3 rounded-lg bg-opacity-20', color.replace('text-', 'bg-'))}>
        <div className={color}>{icon}</div>
      </div>
      <div>
        <div className="text-2xl font-bold text-white">{value}</div>
        <div className="text-white/50 text-sm">{title}</div>
      </div>
    </div>
  );
};

// 简单柱状图
interface SimpleBarChartProps {
  data: HourlyStat[];
  metric: 'views' | 'watchTime' | 'engagement';
}

const SimpleBarChart: React.FC<SimpleBarChartProps> = ({ data, metric }) => {
  if (!data || data.length === 0) {
    return (
      <div className="text-white/40 text-center">
        <BarChart3 className="w-12 h-12 mx-auto mb-2 opacity-30" />
        暂无数据
      </div>
    );
  }

  const maxValue = Math.max(...data.map(d => d.views));
  const displayData = data.slice(-24); // 显示最近24小时

  return (
    <div className="w-full h-full flex items-end gap-1 px-4 pb-8">
      {displayData.map((item, index) => {
        const height = maxValue > 0 ? (item.views / maxValue) * 100 : 0;
        
        return (
          <div
            key={index}
            className="flex-1 flex flex-col items-center gap-1 group"
          >
            {/* 柱子 */}
            <div
              className="w-full bg-blue-500/50 hover:bg-blue-500 rounded-t transition-all relative"
              style={{ height: `${Math.max(height, 5)}%` }}
            >
              {/* 提示框 */}
              <div className="absolute bottom-full left-1/2 -translate-x-1/2 mb-2 px-2 py-1 bg-gray-800 text-white text-xs rounded opacity-0 group-hover:opacity-100 transition-opacity whitespace-nowrap z-10">
                {item.views} 次观看
                <div className="absolute top-full left-1/2 -translate-x-1/2 border-4 border-transparent border-t-gray-800" />
              </div>
            </div>
            
            {/* 时间标签（每隔4个显示） */}
            {index % 4 === 0 && (
              <div className="text-white/40 text-[10px] -rotate-45 origin-top-left translate-y-2">
                {item.hour.split(' ')[1]}
              </div>
            )}
          </div>
        );
      })}
    </div>
  );
};

// 播放热力图
export interface PlaybackHeatmapProps {
  data: Array<{
    timestamp: number;
    views: number;
  }>;
  duration: number;
  className?: string;
}

export const PlaybackHeatmap: React.FC<PlaybackHeatmapProps> = ({
  data,
  duration,
  className,
}) => {
  const segments = 50; // 分成50段
  const segmentDuration = duration / segments;

  // 计算每段的观看次数
  const heatmapData = Array.from({ length: segments }, (_, i) => {
    const startTime = i * segmentDuration;
    const endTime = (i + 1) * segmentDuration;
    
    const views = data
      .filter(d => d.timestamp >= startTime && d.timestamp < endTime)
      .reduce((sum, d) => sum + d.views, 0);
    
    return { segment: i, views };
  });

  const maxViews = Math.max(...heatmapData.map(d => d.views), 1);

  // 获取热度颜色
  const getHeatColor = (views: number): string => {
    const intensity = views / maxViews;
    if (intensity > 0.8) return 'bg-red-500';
    if (intensity > 0.6) return 'bg-orange-500';
    if (intensity > 0.4) return 'bg-yellow-500';
    if (intensity > 0.2) return 'bg-green-500';
    return 'bg-blue-500';
  };

  return (
    <div className={cn('space-y-2', className)}>
      <div className="flex items-center justify-between">
        <h4 className="text-white font-medium text-sm">观看热力图</h4>
        <div className="flex items-center gap-2 text-xs">
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 rounded-full bg-blue-500" /> 低
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 rounded-full bg-green-500" />
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 rounded-full bg-yellow-500" />
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 rounded-full bg-orange-500" />
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 rounded-full bg-red-500" /> 高
          </span>
        </div>
      </div>
      
      <div className="flex gap-0.5 h-8">
        {heatmapData.map((item) => (
          <div
            key={item.segment}
            className={cn(
              'flex-1 rounded-sm transition-opacity hover:opacity-80 cursor-pointer',
              getHeatColor(item.views)
            )}
            title={`时间段: ${(item.segment * segmentDuration / 60).toFixed(1)}分钟 - 观看: ${item.views}`}
          />
        ))}
      </div>
    </div>
  );
};

// 观众留存率曲线
export interface RetentionCurveProps {
  data: Array<{
    percentage: number;
    retention: number;
  }>;
  className?: string;
}

export const RetentionCurve: React.FC<RetentionCurveProps> = ({
  data,
  className,
}) => {
  if (!data || data.length === 0) {
    return (
      <div className={cn('text-white/40 text-center py-8', className)}>
        暂无留存数据
      </div>
    );
  }

  // 构建SVG路径
  const width = 100;
  const height = 50;
  const points = data.map((d, i) => ({
    x: (i / (data.length - 1)) * width,
    y: height - (d.retention * height),
  }));

  const pathD = points.reduce((acc, point, i) => {
    if (i === 0) return `M ${point.x} ${point.y}`;
    return `${acc} L ${point.x} ${point.y}`;
  }, '');

  return (
    <div className={cn('space-y-2', className)}>
      <h4 className="text-white font-medium text-sm">观众留存率</h4>
      
      <div className="relative h-32 bg-gray-800 rounded-lg overflow-hidden">
        <svg
          viewBox={`0 0 ${width} ${height}`}
          preserveAspectRatio="none"
          className="absolute inset-0 w-full h-full"
        >
          {/* 网格线 */}
          <line x1="0" y1={height * 0.25} x2={width} y2={height * 0.25} stroke="rgba(255,255,255,0.1)" strokeWidth="0.2" />
          <line x1="0" y1={height * 0.5} x2={width} y2={height * 0.5} stroke="rgba(255,255,255,0.1)" strokeWidth="0.2" />
          <line x1="0" y1={height * 0.75} x2={width} y2={height * 0.75} stroke="rgba(255,255,255,0.1)" strokeWidth="0.2" />
          
          {/* 填充区域 */}
          <path
            d={`${pathD} L ${width} ${height} L 0 ${height} Z`}
            fill="rgba(59, 130, 246, 0.2)"
          />
          
          {/* 曲线 */}
          <path
            d={pathD}
            fill="none"
            stroke="#3b82f6"
            strokeWidth="0.5"
          />
        </svg>
        
        {/* 标签 */}
        <div className="absolute left-2 top-2 text-white/60 text-xs">100%</div>
        <div className="absolute left-2 bottom-2 text-white/60 text-xs">0%</div>
        <div className="absolute right-2 bottom-2 text-white/60 text-xs">100%</div>
      </div>
    </div>
  );
};
