import React, { useState } from 'react';
import {
  LayoutDashboard,
  MessageSquare,
  HelpCircle,
  Users,
  FileText,
  Flag,
  Settings,
  Search,
  Filter,
  MoreHorizontal,
  CheckCircle2,
  XCircle,
  AlertTriangle,
  Ban,
  Eye,
  Trash2,
  ChevronLeft,
  ChevronRight,
  BarChart3,
  TrendingUp,
  UserCheck,
  Shield
} from 'lucide-react';
import { cn } from '@utils/classNames';

const adminTabs = [
  { id: 'dashboard', label: '概览', icon: LayoutDashboard },
  { id: 'discussions', label: '讨论管理', icon: MessageSquare },
  { id: 'questions', label: '问答管理', icon: HelpCircle },
  { id: 'groups', label: '小组管理', icon: Users },
  { id: 'resources', label: '资源管理', icon: FileText },
  { id: 'reports', label: '举报处理', icon: Flag },
  { id: 'users', label: '用户管理', icon: UserCheck },
  { id: 'settings', label: '社区设置', icon: Settings },
];

// 模拟统计数据
const statsData = {
  totalUsers: 12345,
  newUsersToday: 56,
  totalTopics: 8923,
  topicsToday: 23,
  totalQuestions: 15678,
  answeredQuestions: 12345,
  pendingReports: 12,
  activeGroups: 156,
};

// 模拟讨论数据
const mockDiscussions = [
  { id: 1, title: '如何理解群论中的Sylow定理？', author: '数学爱好者', category: '问题求助', status: 'active', reports: 0, createdAt: '2024-01-15 10:30' },
  { id: 2, title: '【公告】社区规范更新', author: '管理员', category: '公告', status: 'pinned', reports: 0, createdAt: '2024-01-14 09:00' },
  { id: 3, title: '分享一些拓扑学的学习资源', author: '拓扑迷', category: '资源分享', status: 'active', reports: 1, createdAt: '2024-01-13 15:20' },
  { id: 4, title: '不当内容测试', author: 'test_user', category: '综合讨论', status: 'flagged', reports: 5, createdAt: '2024-01-12 08:45' },
];

// 模拟举报数据
const mockReports = [
  { id: 1, targetType: 'topic', targetTitle: '不当内容测试', reporter: '用户A', reason: 'spam', status: 'pending', createdAt: '2024-01-15 14:30' },
  { id: 2, targetType: 'reply', targetTitle: '回复: 如何理解群论...', reporter: '用户B', reason: 'harassment', status: 'investigating', createdAt: '2024-01-15 12:15' },
  { id: 3, targetType: 'user', targetTitle: '用户: spam_bot', reporter: '用户C', reason: 'spam', status: 'resolved', createdAt: '2024-01-14 09:45' },
];

// 模拟用户数据
const mockUsers = [
  { id: 1, name: '数学大师', email: 'master@example.com', level: 12, points: 12500, status: 'active', role: 'expert', joinedAt: '2023-01-15' },
  { id: 2, name: '代数专家', email: 'algebra@example.com', level: 11, points: 10800, status: 'active', role: 'moderator', joinedAt: '2023-03-20' },
  { id: 3, name: 'test_user', email: 'test@example.com', level: 2, points: 100, status: 'banned', role: 'member', joinedAt: '2024-01-10' },
];

export const CommunityAdmin: React.FC = () => {
  const [activeTab, setActiveTab] = useState('dashboard');
  const [searchQuery, setSearchQuery] = useState('');

  const renderContent = () => {
    switch (activeTab) {
      case 'dashboard':
        return <DashboardView />;
      case 'discussions':
        return <DiscussionsView />;
      case 'questions':
        return <QuestionsView />;
      case 'groups':
        return <GroupsView />;
      case 'resources':
        return <ResourcesView />;
      case 'reports':
        return <ReportsView />;
      case 'users':
        return <UsersView />;
      case 'settings':
        return <SettingsView />;
      default:
        return <DashboardView />;
    }
  };

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-slate-900">
      <div className="flex">
        {/* 侧边栏 */}
        <aside className="w-64 bg-white dark:bg-slate-800 border-r border-gray-200 dark:border-slate-700 min-h-screen">
          <div className="p-6">
            <div className="flex items-center gap-2 text-xl font-bold text-gray-900 dark:text-white">
              <Shield className="w-6 h-6 text-blue-600" />
              社区管理
            </div>
          </div>
          
          <nav className="px-4 pb-4">
            {adminTabs.map(tab => (
              <button
                key={tab.id}
                onClick={() => setActiveTab(tab.id)}
                className={cn(
                  "w-full flex items-center gap-3 px-4 py-3 rounded-lg text-sm font-medium transition-colors",
                  activeTab === tab.id
                    ? "bg-blue-100 text-blue-700 dark:bg-blue-900/30 dark:text-blue-400"
                    : "text-gray-600 hover:bg-gray-100 dark:text-gray-400 dark:hover:bg-slate-700"
                )}
              >
                <tab.icon className="w-5 h-5" />
                {tab.label}
              </button>
            ))}
          </nav>
        </aside>

        {/* 主内容区 */}
        <main className="flex-1 p-8">
          {renderContent()}
        </main>
      </div>
    </div>
  );
};

// 概览视图
const DashboardView = () => (
  <div className="space-y-6">
    <h1 className="text-2xl font-bold text-gray-900 dark:text-white">社区概览</h1>
    
    {/* 统计卡片 */}
    <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
      <StatCard title="总用户数" value={statsData.totalUsers.toLocaleString()} change={`+${statsData.newUsersToday}`} icon={Users} color="blue" />
      <StatCard title="讨论主题" value={statsData.totalTopics.toLocaleString()} change={`+${statsData.topicsToday}`} icon={MessageSquare} color="green" />
      <StatCard title="问题解答率" value={`${Math.round(statsData.answeredQuestions / statsData.totalQuestions * 100)}%`} change="+2%" icon={HelpCircle} color="purple" />
      <StatCard title="待处理举报" value={statsData.pendingReports} alert={statsData.pendingReports > 10} icon={Flag} color="red" />
    </div>

    {/* 趋势图表 */}
    <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
      <div className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">用户增长趋势</h3>
        <div className="h-64 flex items-end justify-between gap-2">
          {[45, 52, 48, 65, 58, 72, 68, 75, 82, 78, 85, 92].map((val, i) => (
            <div key={i} className="flex-1 flex flex-col items-center gap-2">
              <div 
                className="w-full bg-blue-500 rounded-t-lg transition-all"
                style={{ height: `${val}%` }}
              />
              <span className="text-xs text-gray-500">{i + 1}月</span>
            </div>
          ))}
        </div>
      </div>

      <div className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">内容发布趋势</h3>
        <div className="h-64 flex items-end justify-between gap-2">
          {[30, 45, 35, 55, 48, 62, 58, 70, 65, 75, 72, 80].map((val, i) => (
            <div key={i} className="flex-1 flex flex-col items-center gap-2">
              <div 
                className="w-full bg-green-500 rounded-t-lg transition-all"
                style={{ height: `${val}%` }}
              />
              <span className="text-xs text-gray-500">{i + 1}月</span>
            </div>
          ))}
        </div>
      </div>
    </div>

    {/* 最新动态 */}
    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700">
      <div className="p-6 border-b border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white">最新动态</h3>
      </div>
      <div className="divide-y divide-gray-200 dark:divide-slate-700">
        {[
          { action: '新用户注册', detail: '用户 "数学新手" 加入了社区', time: '5分钟前' },
          { action: '新问题', detail: '发布了新问题 "如何理解极限？"', time: '15分钟前' },
          { action: '举报处理', detail: '管理员处理了1条举报', time: '30分钟前' },
          { action: '资源分享', detail: '用户分享了 "拓扑学笔记"', time: '1小时前' },
        ].map((item, i) => (
          <div key={i} className="p-4 flex items-center justify-between">
            <div>
              <span className="font-medium text-gray-900 dark:text-white">{item.action}</span>
              <span className="text-gray-500 mx-2">·</span>
              <span className="text-gray-600 dark:text-gray-400">{item.detail}</span>
            </div>
            <span className="text-sm text-gray-500">{item.time}</span>
          </div>
        ))}
      </div>
    </div>
  </div>
);

// 讨论管理视图
const DiscussionsView = () => (
  <div className="space-y-6">
    <div className="flex items-center justify-between">
      <h1 className="text-2xl font-bold text-gray-900 dark:text-white">讨论管理</h1>
      <div className="flex items-center gap-2">
        <input
          type="text"
          placeholder="搜索讨论..."
          className="px-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
        />
        <button className="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700">
          <Filter className="w-4 h-4" />
        </button>
      </div>
    </div>

    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden">
      <table className="w-full">
        <thead className="bg-gray-50 dark:bg-slate-700">
          <tr>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">标题</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">作者</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">分类</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">状态</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">举报</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">操作</th>
          </tr>
        </thead>
        <tbody className="divide-y divide-gray-200 dark:divide-slate-700">
          {mockDiscussions.map(discussion => (
            <tr key={discussion.id}>
              <td className="px-6 py-4 text-sm text-gray-900 dark:text-white">{discussion.title}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{discussion.author}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{discussion.category}</td>
              <td className="px-6 py-4">
                <span className={cn(
                  "px-2 py-1 text-xs rounded-full",
                  discussion.status === 'active' ? 'bg-green-100 text-green-700' :
                  discussion.status === 'pinned' ? 'bg-blue-100 text-blue-700' :
                  'bg-red-100 text-red-700'
                )}>
                  {discussion.status === 'active' ? '正常' : discussion.status === 'pinned' ? '置顶' : '标记'}
                </span>
              </td>
              <td className="px-6 py-4 text-sm text-gray-500">{discussion.reports}</td>
              <td className="px-6 py-4">
                <div className="flex items-center gap-2">
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <Eye className="w-4 h-4 text-gray-500" />
                  </button>
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <CheckCircle2 className="w-4 h-4 text-green-500" />
                  </button>
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <Trash2 className="w-4 h-4 text-red-500" />
                  </button>
                </div>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  </div>
);

// 问答管理视图
const QuestionsView = () => (
  <div className="space-y-6">
    <h1 className="text-2xl font-bold text-gray-900 dark:text-white">问答管理</h1>
    <div className="bg-white dark:bg-slate-800 rounded-xl p-8 border border-gray-200 dark:border-slate-700 text-center">
      <HelpCircle className="w-12 h-12 text-gray-300 mx-auto mb-4" />
      <p className="text-gray-500">问答管理功能开发中...</p>
    </div>
  </div>
);

// 小组管理视图
const GroupsView = () => (
  <div className="space-y-6">
    <h1 className="text-2xl font-bold text-gray-900 dark:text-white">小组管理</h1>
    <div className="bg-white dark:bg-slate-800 rounded-xl p-8 border border-gray-200 dark:border-slate-700 text-center">
      <Users className="w-12 h-12 text-gray-300 mx-auto mb-4" />
      <p className="text-gray-500">小组管理功能开发中...</p>
    </div>
  </div>
);

// 资源管理视图
const ResourcesView = () => (
  <div className="space-y-6">
    <h1 className="text-2xl font-bold text-gray-900 dark:text-white">资源管理</h1>
    <div className="bg-white dark:bg-slate-800 rounded-xl p-8 border border-gray-200 dark:border-slate-700 text-center">
      <FileText className="w-12 h-12 text-gray-300 mx-auto mb-4" />
      <p className="text-gray-500">资源管理功能开发中...</p>
    </div>
  </div>
);

// 举报处理视图
const ReportsView = () => (
  <div className="space-y-6">
    <div className="flex items-center justify-between">
      <h1 className="text-2xl font-bold text-gray-900 dark:text-white">举报处理</h1>
      <div className="flex items-center gap-2">
        <select className="px-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white">
          <option>全部状态</option>
          <option>待处理</option>
          <option>处理中</option>
          <option>已解决</option>
        </select>
      </div>
    </div>

    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden">
      <table className="w-full">
        <thead className="bg-gray-50 dark:bg-slate-700">
          <tr>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">类型</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">目标</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">举报原因</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">举报人</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">状态</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">操作</th>
          </tr>
        </thead>
        <tbody className="divide-y divide-gray-200 dark:divide-slate-700">
          {mockReports.map(report => (
            <tr key={report.id}>
              <td className="px-6 py-4 text-sm text-gray-900 dark:text-white">
                {report.targetType === 'topic' ? '主题' : report.targetType === 'reply' ? '回复' : '用户'}
              </td>
              <td className="px-6 py-4 text-sm text-gray-500 max-w-xs truncate">{report.targetTitle}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{report.reason}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{report.reporter}</td>
              <td className="px-6 py-4">
                <span className={cn(
                  "px-2 py-1 text-xs rounded-full",
                  report.status === 'pending' ? 'bg-yellow-100 text-yellow-700' :
                  report.status === 'investigating' ? 'bg-blue-100 text-blue-700' :
                  'bg-green-100 text-green-700'
                )}>
                  {report.status === 'pending' ? '待处理' : report.status === 'investigating' ? '处理中' : '已解决'}
                </span>
              </td>
              <td className="px-6 py-4">
                <div className="flex items-center gap-2">
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <Eye className="w-4 h-4 text-gray-500" />
                  </button>
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <CheckCircle2 className="w-4 h-4 text-green-500" />
                  </button>
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <XCircle className="w-4 h-4 text-red-500" />
                  </button>
                </div>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  </div>
);

// 用户管理视图
const UsersView = () => (
  <div className="space-y-6">
    <div className="flex items-center justify-between">
      <h1 className="text-2xl font-bold text-gray-900 dark:text-white">用户管理</h1>
      <div className="flex items-center gap-2">
        <input
          type="text"
          placeholder="搜索用户..."
          className="px-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
        />
      </div>
    </div>

    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden">
      <table className="w-full">
        <thead className="bg-gray-50 dark:bg-slate-700">
          <tr>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">用户</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">等级</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">积分</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">角色</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">状态</th>
            <th className="px-6 py-3 text-left text-xs font-medium text-gray-500 uppercase">操作</th>
          </tr>
        </thead>
        <tbody className="divide-y divide-gray-200 dark:divide-slate-700">
          {mockUsers.map(user => (
            <tr key={user.id}>
              <td className="px-6 py-4">
                <div className="flex items-center gap-3">
                  <div className="w-8 h-8 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white text-sm font-medium">
                    {user.name.charAt(0)}
                  </div>
                  <div>
                    <div className="text-sm font-medium text-gray-900 dark:text-white">{user.name}</div>
                    <div className="text-sm text-gray-500">{user.email}</div>
                  </div>
                </div>
              </td>
              <td className="px-6 py-4 text-sm text-gray-900 dark:text-white">{user.level}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{user.points.toLocaleString()}</td>
              <td className="px-6 py-4 text-sm text-gray-500">{user.role}</td>
              <td className="px-6 py-4">
                <span className={cn(
                  "px-2 py-1 text-xs rounded-full",
                  user.status === 'active' ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'
                )}>
                  {user.status === 'active' ? '正常' : '封禁'}
                </span>
              </td>
              <td className="px-6 py-4">
                <div className="flex items-center gap-2">
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <Eye className="w-4 h-4 text-gray-500" />
                  </button>
                  <button className="p-1 hover:bg-gray-100 dark:hover:bg-slate-700 rounded">
                    <Ban className="w-4 h-4 text-red-500" />
                  </button>
                </div>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  </div>
);

// 设置视图
const SettingsView = () => (
  <div className="space-y-6">
    <h1 className="text-2xl font-bold text-gray-900 dark:text-white">社区设置</h1>
    
    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6 space-y-6">
      <div>
        <h3 className="text-lg font-medium text-gray-900 dark:text-white mb-4">基础设置</h3>
        <div className="space-y-4">
          <div className="flex items-center justify-between">
            <div>
              <div className="font-medium text-gray-900 dark:text-white">允许新用户注册</div>
              <div className="text-sm text-gray-500">关闭后将禁止新用户注册</div>
            </div>
            <label className="relative inline-flex items-center cursor-pointer">
              <input type="checkbox" className="sr-only peer" defaultChecked />
              <div className="w-11 h-6 bg-gray-200 peer-focus:ring-4 peer-focus:ring-blue-300 rounded-full peer peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after:left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all peer-checked:bg-blue-600"></div>
            </label>
          </div>
          
          <div className="flex items-center justify-between">
            <div>
              <div className="font-medium text-gray-900 dark:text-white">内容审核</div>
              <div className="text-sm text-gray-500">新发布的内容需要审核</div>
            </div>
            <label className="relative inline-flex items-center cursor-pointer">
              <input type="checkbox" className="sr-only peer" />
              <div className="w-11 h-6 bg-gray-200 peer-focus:ring-4 peer-focus:ring-blue-300 rounded-full peer peer-checked:after:translate-x-full peer-checked:after:border-white after:content-[''] after:absolute after:top-[2px] after-left-[2px] after:bg-white after:border-gray-300 after:border after:rounded-full after:h-5 after:w-5 after:transition-all peer-checked:bg-blue-600"></div>
            </label>
          </div>
        </div>
      </div>

      <div className="border-t border-gray-200 dark:border-slate-700 pt-6">
        <h3 className="text-lg font-medium text-gray-900 dark:text-white mb-4">积分设置</h3>
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          <div>
            <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">每日登录积分</label>
            <input type="number" defaultValue={10} className="w-full px-3 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white" />
          </div>
          <div>
            <label className="block text-sm font-medium text-gray-700 dark:text-gray-300 mb-1">发布主题积分</label>
            <input type="number" defaultValue={20} className="w-full px-3 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white" />
          </div>
        </div>
      </div>
    </div>
  </div>
);

// 统计卡片组件
const StatCard = ({ title, value, change, icon: Icon, color, alert }: any) => (
  <div className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700">
    <div className="flex items-center justify-between">
      <div>
        <p className="text-sm text-gray-500">{title}</p>
        <p className="text-2xl font-bold text-gray-900 dark:text-white mt-1">{value}</p>
        {change && <p className="text-sm text-green-600 mt-1">{change}</p>}
      </div>
      <div className={cn("w-12 h-12 rounded-lg flex items-center justify-center", `bg-${color}-100 text-${color}-600`)}>
        <Icon className="w-6 h-6" />
      </div>
    </div>
    {alert && (
      <div className="mt-3 flex items-center gap-2 text-sm text-red-600">
        <AlertTriangle className="w-4 h-4" />
        需要关注
      </div>
    )}
  </div>
);

export default CommunityAdmin;
