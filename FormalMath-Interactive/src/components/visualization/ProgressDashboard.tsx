/**
 * FormalMath 进度追踪仪表盘组件
 * 显示学习统计、成就、徽章
 */

import React, { useEffect, useState } from 'react';
import { progressTracker } from '../../integrations/progressTracker';
import type { RealtimeProgress, Notification } from '../../integrations/progressTracker';

interface ProgressDashboardProps {
  userId: string;
  className?: string;
}

/**
 * 进度追踪仪表盘组件
 */
export const ProgressDashboard: React.FC<ProgressDashboardProps> = ({
  userId,
  className = '',
}) => {
  const [progress, setProgress] = useState<RealtimeProgress | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<Error | null>(null);
  const [activeTab, setActiveTab] = useState<'overview' | 'achievements' | 'badges'>('overview');

  useEffect(() => {
    setLoading(true);
    progressTracker.getRealtimeProgress(userId)
      .then(data => {
        setProgress(data);
        setLoading(false);
      })
      .catch(err => {
        setError(err instanceof Error ? err : new Error('Failed to load progress'));
        setLoading(false);
      });
  }, [userId]);

  if (loading) {
    return (
      <div className={`p-6 bg-white rounded-lg shadow ${className}`}>
        <div className="text-center text-gray-500">加载进度数据...</div>
      </div>
    );
  }

  if (error || !progress) {
    return (
      <div className={`p-6 bg-white rounded-lg shadow ${className}`}>
        <div className="text-center text-red-500">
          加载失败: {error?.message || 'Unknown error'}
        </div>
      </div>
    );
  }

  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 标签栏 */}
      <div className="flex border-b">
        <TabButton
          active={activeTab === 'overview'}
          onClick={() => setActiveTab('overview')}
          label="总览"
        />
        <TabButton
          active={activeTab === 'achievements'}
          onClick={() => setActiveTab('achievements')}
          label="成就"
          badge={`${progress.achievements.completed}/${progress.achievements.total}`}
        />
        <TabButton
          active={activeTab === 'badges'}
          onClick={() => setActiveTab('badges')}
          label="徽章"
          badge={progress.badges.total.toString()}
        />
      </div>

      {/* 内容区域 */}
      <div className="p-6">
        {activeTab === 'overview' && <OverviewTab progress={progress} />}
        {activeTab === 'achievements' && <AchievementsTab progress={progress} />}
        {activeTab === 'badges' && <BadgesTab progress={progress} />}
      </div>
    </div>
  );
};

// 标签按钮
const TabButton: React.FC<{
  active: boolean;
  onClick: () => void;
  label: string;
  badge?: string;
}> = ({ active, onClick, label, badge }) => (
  <button
    className={`flex-1 py-3 px-4 font-medium transition-colors ${
      active
        ? 'text-blue-600 border-b-2 border-blue-600'
        : 'text-gray-600 hover:text-gray-800'
    }`}
    onClick={onClick}
  >
    {label}
    {badge && (
      <span className="ml-2 text-xs bg-gray-100 text-gray-600 px-2 py-0.5 rounded-full">
        {badge}
      </span>
    )}
  </button>
);

// 总览标签
const OverviewTab: React.FC<{ progress: RealtimeProgress }> = ({ progress }) => (
  <div className="space-y-6">
    {/* 学习统计卡片 */}
    <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
      <StatCard
        icon="📚"
        label="总概念数"
        value={progress.summary.totalConcepts}
        subtext={`已掌握 ${progress.summary.masteredConcepts}`}
      />
      <StatCard
        icon="✅"
        label="已完成"
        value={progress.summary.masteredConcepts}
        color="green"
      />
      <StatCard
        icon="⏱️"
        label="学习时长"
        value={formatHours(progress.summary.totalTimeSpent)}
        subtext="小时"
      />
      <StatCard
        icon="🔥"
        label="连续学习"
        value={progress.summary.streakDays}
        subtext="天"
        color="orange"
      />
    </div>

    {/* 掌握度分布 */}
    <div className="bg-gray-50 rounded-lg p-4">
      <h4 className="font-semibold text-gray-800 mb-4">掌握度分布</h4>
      <MasteryDistributionChart distribution={progress.masteryDistribution} />
    </div>

    {/* 本周进度 */}
    <div className="bg-gray-50 rounded-lg p-4">
      <h4 className="font-semibold text-gray-800 mb-4">本周进度</h4>
      <WeeklyProgress data={progress.weeklyProgress} />
    </div>

    {/* 技能增长 */}
    <div className="bg-gray-50 rounded-lg p-4">
      <h4 className="font-semibold text-gray-800 mb-4">技能增长</h4>
      <SkillGrowthChart growth={progress.skillGrowth} />
    </div>

    {/* 学习速度 */}
    <div className="bg-blue-50 rounded-lg p-4">
      <h4 className="font-semibold text-blue-800 mb-2">学习速度</h4>
      <div className="grid grid-cols-2 gap-4">
        <div>
          <span className="text-blue-600">日均完成:</span>
          <span className="ml-2 font-medium">{progress.velocity.nodesPerDay.toFixed(1)} 个概念</span>
        </div>
        <div>
          <span className="text-blue-600">预计完成:</span>
          <span className="ml-2 font-medium">
            {new Date(progress.velocity.estimatedCompletionDate).toLocaleDateString('zh-CN')}
          </span>
        </div>
      </div>
    </div>
  </div>
);

// 成就标签
const AchievementsTab: React.FC<{ progress: RealtimeProgress }> = ({ progress }) => (
  <div className="space-y-4">
    {/* 完成进度 */}
    <div className="bg-gray-50 rounded-lg p-4">
      <div className="flex items-center justify-between mb-2">
        <span className="text-gray-600">总进度</span>
        <span className="font-medium">
          {progress.achievements.completed}/{progress.achievements.total}
        </span>
      </div>
      <div className="h-2 bg-gray-200 rounded-full overflow-hidden">
        <div
          className="h-full bg-blue-500 transition-all"
          style={{
            width: `${(progress.achievements.completed / progress.achievements.total) * 100}%`,
          }}
        />
      </div>
    </div>

    {/* 进行中成就 */}
    {progress.achievements.inProgress.length > 0 && (
      <div>
        <h4 className="font-semibold text-gray-800 mb-3">进行中</h4>
        <div className="space-y-3">
          {progress.achievements.inProgress.map(achievement => (
            <AchievementCard key={achievement.id} achievement={achievement} />
          ))}
        </div>
      </div>
    )}
  </div>
);

// 徽章标签
const BadgesTab: React.FC<{ progress: RealtimeProgress }> = ({ progress }) => (
  <div className="space-y-4">
    {/* 徽章统计 */}
    <div className="grid grid-cols-4 gap-4">
      <BadgeStat count={progress.badges.byRarity.common} label="普通" color="gray" />
      <BadgeStat count={progress.badges.byRarity.rare} label="稀有" color="blue" />
      <BadgeStat count={progress.badges.byRarity.epic} label="史诗" color="purple" />
      <BadgeStat count={progress.badges.byRarity.legendary} label="传说" color="yellow" />
    </div>

    {/* 最近获得 */}
    {progress.badges.recent.length > 0 && (
      <div>
        <h4 className="font-semibold text-gray-800 mb-3">最近获得</h4>
        <div className="flex gap-3">
          {progress.badges.recent.map(badge => (
            <div
              key={badge.id}
              className="w-16 h-16 bg-gray-100 rounded-lg flex items-center justify-center text-2xl"
              title={badge.name}
            >
              {badge.icon}
            </div>
          ))}
        </div>
      </div>
    )}
  </div>
);

// 统计卡片
const StatCard: React.FC<{
  icon: string;
  label: string;
  value: string | number;
  subtext?: string;
  color?: 'default' | 'green' | 'orange';
}> = ({ icon, label, value, subtext, color = 'default' }) => {
  const colorClasses = {
    default: 'bg-gray-50',
    green: 'bg-green-50',
    orange: 'bg-orange-50',
  };

  return (
    <div className={`${colorClasses[color]} rounded-lg p-4`}>
      <div className="text-2xl mb-1">{icon}</div>
      <div className="text-2xl font-bold text-gray-800">{value}</div>
      <div className="text-sm text-gray-600">{label}</div>
      {subtext && <div className="text-xs text-gray-400 mt-1">{subtext}</div>}
    </div>
  );
};

// 掌握度分布图
const MasteryDistributionChart: React.FC<{ distribution: RealtimeProgress['masteryDistribution'] }> = ({
  distribution,
}) => {
  const total = Object.values(distribution).reduce((a, b) => a + b, 0);
  if (total === 0) return <div className="text-gray-400">暂无数据</div>;

  const items = [
    { key: 'notStarted', label: '未开始', color: 'bg-gray-400' },
    { key: 'beginner', label: '初学', color: 'bg-orange-400' },
    { key: 'intermediate', label: '理解', color: 'bg-yellow-400' },
    { key: 'advanced', label: '熟练', color: 'bg-green-400' },
    { key: 'master', label: '精通', color: 'bg-blue-400' },
  ];

  return (
    <div className="space-y-2">
      {items.map(item => {
        const count = distribution[item.key as keyof typeof distribution];
        const percentage = total > 0 ? (count / total) * 100 : 0;
        return (
          <div key={item.key} className="flex items-center gap-2">
            <span className="w-16 text-sm text-gray-600">{item.label}</span>
            <div className="flex-1 h-4 bg-gray-200 rounded-full overflow-hidden">
              <div
                className={`h-full ${item.color} transition-all`}
                style={{ width: `${percentage}%` }}
              />
            </div>
            <span className="w-12 text-right text-sm text-gray-600">{count}</span>
          </div>
        );
      })}
    </div>
  );
};

// 本周进度
const WeeklyProgress: React.FC<{ data: RealtimeProgress['weeklyProgress'] }> = ({ data }) => (
  <div>
    <div className="flex items-center justify-between mb-4">
      <div className="flex gap-4">
        <div>
          <span className="text-gray-600">完成节点:</span>
          <span className="ml-2 font-medium">{data.nodesCompleted}</span>
        </div>
        <div>
          <span className="text-gray-600">学习时长:</span>
          <span className="ml-2 font-medium">{formatHours(data.timeSpent)} 小时</span>
        </div>
      </div>
      <div className="text-sm">
        <span className="text-gray-500">较上周:</span>
        <span className={`ml-1 ${data.comparison.nodesChange >= 0 ? 'text-green-600' : 'text-red-600'}`}>
          {data.comparison.nodesChange >= 0 ? '+' : ''}{data.comparison.nodesChange}%
        </span>
      </div>
    </div>

    {/* 每日分解 */}
    <div className="grid grid-cols-7 gap-2">
      {data.dailyBreakdown.map((day, idx) => (
        <div key={idx} className="text-center">
          <div className="text-xs text-gray-500 mb-1">{day.day}</div>
          <div
            className="w-full bg-blue-500 rounded-t"
            style={{ height: `${Math.max(day.nodes * 10, 4)}px` }}
          />
          <div className="text-xs text-gray-600 mt-1">{day.nodes}</div>
        </div>
      ))}
    </div>
  </div>
);

// 技能增长图
const SkillGrowth: React.FC<{ growth: RealtimeProgress['skillGrowth'] }> = ({ growth }) => {
  const dimensions = [
    { key: 'knowledge', label: '知识掌握', change: growth.changes.knowledge },
    { key: 'problemSolving', label: '问题解决', change: growth.changes.problemSolving },
    { key: 'proofAbility', label: '证明能力', change: growth.changes.proofAbility },
    { key: 'application', label: '应用实践', change: growth.changes.application },
    { key: 'innovation', label: '创新思维', change: growth.changes.innovation },
  ];

  return (
    <div className="space-y-2">
      <div className="flex items-center gap-2 mb-3">
        <span className="text-gray-600">整体趋势:</span>
        <span className={`font-medium ${
          growth.trend === 'improving' ? 'text-green-600' :
          growth.trend === 'declining' ? 'text-red-600' :
          'text-gray-600'
        }`}>
          {growth.trend === 'improving' ? '📈 上升' :
           growth.trend === 'declining' ? '📉 下降' :
           '➡️ 稳定'}
        </span>
      </div>

      {dimensions.map(dim => (
        <div key={dim.key} className="flex items-center gap-2">
          <span className="w-20 text-sm text-gray-600">{dim.label}</span>
          <div className={`text-sm font-medium ${
            dim.change > 0 ? 'text-green-600' :
            dim.change < 0 ? 'text-red-600' :
            'text-gray-600'
          }`}>
            {dim.change > 0 ? '+' : ''}{dim.change}
          </div>
        </div>
      ))}
    </div>
  );
};

// 成就卡片
const AchievementCard: React.FC<{ achievement: import('../../types/learning').Achievement }> = ({
  achievement,
}) => (
  <div className="bg-gray-50 rounded-lg p-3">
    <div className="flex justify-between items-start">
      <div>
        <div className="font-medium text-gray-800">{achievement.title}</div>
        <div className="text-sm text-gray-500">{achievement.description}</div>
      </div>
      <div className="text-right">
        <div className="text-sm font-medium text-blue-600">{achievement.progress}%</div>
      </div>
    </div>
    <div className="mt-2 h-2 bg-gray-200 rounded-full overflow-hidden">
      <div
        className="h-full bg-blue-500 transition-all"
        style={{ width: `${achievement.progress}%` }}
      />
    </div>
  </div>
);

// 徽章统计
const BadgeStat: React.FC<{ count: number; label: string; color: string }> = ({
  count,
  label,
  color,
}) => (
  <div className={`bg-${color}-50 rounded-lg p-3 text-center`}>
    <div className="text-2xl font-bold text-gray-800">{count}</div>
    <div className={`text-xs text-${color}-600`}>{label}</div>
  </div>
);

// 工具函数
const formatHours = (minutes: number): string => {
  return (minutes / 60).toFixed(1);
};

export default ProgressDashboard;
