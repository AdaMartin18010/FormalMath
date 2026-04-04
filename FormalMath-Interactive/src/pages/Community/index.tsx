import React, { useState } from 'react';
import { 
  MessageSquare, 
  HelpCircle, 
  Users, 
  Share2, 
  Trophy,
  Bell,
  Search,
  TrendingUp,
  Flame,
  Star
} from 'lucide-react';
import { cn } from '@utils/classNames';
import { DiscussionForum } from '@components/Community/DiscussionForum';
import { QASystem } from '@components/Community/QASystem';
import { StudyGroups } from '@components/Community/StudyGroups';
import { ResourceSharing } from '@components/Community/ResourceSharing';
import { PointsSystem } from '@components/Community/PointsSystem';

const tabs = [
  { id: 'discussion', label: '讨论区', icon: MessageSquare },
  { id: 'qa', label: '问答', icon: HelpCircle },
  { id: 'groups', label: '学习小组', icon: Users },
  { id: 'resources', label: '资源分享', icon: Share2 },
  { id: 'points', label: '积分', icon: Trophy },
];

// 社区统计数据
const communityStats = [
  { label: '今日活跃', value: '1,234', icon: Flame, color: 'text-orange-500' },
  { label: '总主题', value: '5,678', icon: MessageSquare, color: 'text-blue-500' },
  { label: '已解决问题', value: '12,345', icon: HelpCircle, color: 'text-green-500' },
  { label: '学习小组', value: '156', icon: Users, color: 'text-purple-500' },
];

// 热门话题
const hotTopics = [
  { id: 1, title: '如何理解群论中的Sylow定理？', replies: 45, views: 1234 },
  { id: 2, title: '数学分析中一致连续性的直观理解', replies: 32, views: 987 },
  { id: 3, title: '拓扑学学习路径推荐', replies: 28, views: 856 },
  { id: 4, title: '数论入门书籍推荐', replies: 56, views: 2341 },
];

// 活跃用户
const activeUsers = [
  { id: 1, name: '数学大师', level: 12, points: 12500 },
  { id: 2, name: '代数专家', level: 11, points: 10800 },
  { id: 3, name: '分析达人', level: 10, points: 9200 },
  { id: 4, name: '几何爱好者', level: 8, points: 6500 },
];

export const CommunityPage: React.FC = () => {
  const [activeTab, setActiveTab] = useState('discussion');
  const [notifications, setNotifications] = useState(3);

  const renderContent = () => {
    switch (activeTab) {
      case 'discussion':
        return <DiscussionForum />;
      case 'qa':
        return <QASystem />;
      case 'groups':
        return <StudyGroups />;
      case 'resources':
        return <ResourceSharing />;
      case 'points':
        return <PointsSystem />;
      default:
        return <DiscussionForum />;
    }
  };

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-slate-900">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-8">
        {/* 页面标题 */}
        <div className="mb-8">
          <h1 className="text-3xl font-bold text-gray-900 dark:text-white">学习社区</h1>
          <p className="text-gray-600 dark:text-gray-400 mt-2">
            与全球数学爱好者一起交流、学习、成长
          </p>
        </div>

        {/* 统计卡片 */}
        <div className="grid grid-cols-2 md:grid-cols-4 gap-4 mb-8">
          {communityStats.map(stat => (
            <div key={stat.label} className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700">
              <div className="flex items-center gap-3">
                <div className={cn("w-10 h-10 rounded-lg flex items-center justify-center bg-gray-100 dark:bg-slate-700", stat.color)}>
                  <stat.icon className="w-5 h-5" />
                </div>
                <div>
                  <div className="text-2xl font-bold text-gray-900 dark:text-white">{stat.value}</div>
                  <div className="text-sm text-gray-500">{stat.label}</div>
                </div>
              </div>
            </div>
          ))}
        </div>

        {/* 主内容区域 */}
        <div className="grid grid-cols-1 lg:grid-cols-4 gap-8">
          {/* 左侧主内容 */}
          <div className="lg:col-span-3">
            {/* Tab 导航 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 mb-6">
              <div className="flex overflow-x-auto">
                {tabs.map(tab => (
                  <button
                    key={tab.id}
                    onClick={() => setActiveTab(tab.id)}
                    className={cn(
                      "flex items-center gap-2 px-6 py-4 text-sm font-medium transition-colors border-b-2 whitespace-nowrap",
                      activeTab === tab.id
                        ? "text-blue-600 border-blue-600"
                        : "text-gray-600 border-transparent hover:text-gray-900 dark:text-gray-400 dark:hover:text-white"
                    )}
                  >
                    <tab.icon className="w-4 h-4" />
                    {tab.label}
                  </button>
                ))}
              </div>
            </div>

            {/* 内容区域 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              {renderContent()}
            </div>
          </div>

          {/* 右侧边栏 */}
          <div className="space-y-6">
            {/* 用户信息卡片 */}
            <div className="bg-gradient-to-br from-blue-600 to-purple-600 rounded-xl p-6 text-white">
              <div className="flex items-center gap-4 mb-4">
                <div className="w-14 h-14 rounded-full bg-white/20 flex items-center justify-center text-2xl">
                  👤
                </div>
                <div>
                  <div className="font-semibold">我的社区</div>
                  <div className="text-sm text-blue-100">等级 7 · 2,850 积分</div>
                </div>
              </div>
              <div className="flex items-center justify-between text-sm">
                <span>今日获得: +45</span>
                <button className="flex items-center gap-1 bg-white/20 px-3 py-1 rounded-lg hover:bg-white/30 transition-colors">
                  <Bell className="w-4 h-4" />
                  消息 {notifications > 0 && <span className="bg-red-500 text-white text-xs px-1.5 py-0.5 rounded-full">{notifications}</span>}
                </button>
              </div>
            </div>

            {/* 热门话题 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-5">
              <div className="flex items-center gap-2 mb-4">
                <TrendingUp className="w-5 h-5 text-red-500" />
                <h3 className="font-semibold text-gray-900 dark:text-white">热门话题</h3>
              </div>
              <div className="space-y-3">
                {hotTopics.map((topic, index) => (
                  <div key={topic.id} className="flex items-start gap-3 group cursor-pointer">
                    <span className={cn(
                      "w-5 h-5 rounded flex items-center justify-center text-xs font-bold",
                      index < 3 ? "bg-red-100 text-red-600" : "bg-gray-100 text-gray-500"
                    )}>
                      {index + 1}
                    </span>
                    <div className="flex-1 min-w-0">
                      <p className="text-sm text-gray-700 dark:text-gray-300 group-hover:text-blue-600 transition-colors line-clamp-2">
                        {topic.title}
                      </p>
                      <div className="flex items-center gap-3 mt-1 text-xs text-gray-500">
                        <span>{topic.replies} 回复</span>
                        <span>{topic.views} 浏览</span>
                      </div>
                    </div>
                  </div>
                ))}
              </div>
            </div>

            {/* 活跃用户 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-5">
              <div className="flex items-center gap-2 mb-4">
                <Star className="w-5 h-5 text-yellow-500" />
                <h3 className="font-semibold text-gray-900 dark:text-white">活跃用户</h3>
              </div>
              <div className="space-y-3">
                {activeUsers.map((user, index) => (
                  <div key={user.id} className="flex items-center gap-3">
                    <div className="w-8 h-8 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white text-sm font-medium">
                      {user.name.charAt(0)}
                    </div>
                    <div className="flex-1 min-w-0">
                      <div className="text-sm font-medium text-gray-900 dark:text-white truncate">
                        {user.name}
                      </div>
                      <div className="text-xs text-gray-500">
                        Lv.{user.level} · {user.points.toLocaleString()} 分
                      </div>
                    </div>
                  </div>
                ))}
              </div>
            </div>

            {/* 快速链接 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-5">
              <h3 className="font-semibold text-gray-900 dark:text-white mb-4">快速链接</h3>
              <div className="space-y-2">
                <button className="w-full text-left px-3 py-2 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-700 transition-colors text-sm text-gray-700 dark:text-gray-300">
                  📋 社区规范
                </button>
                <button className="w-full text-left px-3 py-2 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-700 transition-colors text-sm text-gray-700 dark:text-gray-300">
                  🎯 新手指南
                </button>
                <button className="w-full text-left px-3 py-2 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-700 transition-colors text-sm text-gray-700 dark:text-gray-300">
                  🏆 积分规则
                </button>
                <button className="w-full text-left px-3 py-2 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-700 transition-colors text-sm text-gray-700 dark:text-gray-300">
                  💬 反馈建议
                </button>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

export default CommunityPage;
