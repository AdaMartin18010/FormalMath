import React, { useState } from 'react';
import {
  Users,
  UserPlus,
  Calendar,
  BookOpen,
  MessageSquare,
  Settings,
  Search,
  Plus,
  ChevronRight,
  Clock,
  MapPin,
  Star,
  MoreVertical,
  Lock,
  Globe
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { StudyGroup, GroupCategory, GroupActivity } from '../../types/community';

interface StudyGroupsProps {
  className?: string;
}

const groupCategories: { value: GroupCategory; label: string; icon: string }[] = [
  { value: 'algebra', label: '代数学', icon: '📐' },
  { value: 'geometry', label: '几何学', icon: '📏' },
  { value: 'analysis', label: '分析学', icon: '📊' },
  { value: 'topology', label: '拓扑学', icon: '🍩' },
  { value: 'logic', label: '数理逻辑', icon: '🧩' },
  { value: 'number-theory', label: '数论', icon: '🔢' },
  { value: 'applied-math', label: '应用数学', icon: '📈' },
  { value: 'general', label: '综合', icon: '📚' },
];

// 格式化时间
const formatDistanceToNow = (timestamp: number): string => {
  const seconds = Math.floor((Date.now() - timestamp) / 1000);
  if (seconds < 60) return '刚刚';
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}分钟前`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}小时前`;
  const days = Math.floor(hours / 24);
  return `${days}天前`;
};

// 模拟小组数据
const mockGroups: StudyGroup[] = [
  {
    id: 'g1',
    name: '抽象代数研讨组',
    description: '深入学习群论、环论和域论，每周讨论经典教材《Algebra》中的习题和概念。',
    category: 'algebra',
    tags: ['群论', '环论', '交换代数'],
    owner: { id: 'u1', name: '代数达人', level: 10, points: 5000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 200 },
    members: [
      { user: { id: 'u1', name: '代数达人', level: 10, points: 5000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 200 }, role: 'owner', joinedAt: Date.now() - 86400000 * 100, contribution: 500, lastActive: Date.now() },
      { user: { id: 'u2', name: '数学爱好者', level: 5, points: 1200, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 50 }, role: 'member', joinedAt: Date.now() - 86400000 * 30, contribution: 120, lastActive: Date.now() - 3600000 },
      { user: { id: 'u3', name: '群论新手', level: 3, points: 600, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 30 }, role: 'member', joinedAt: Date.now() - 86400000 * 20, contribution: 50, lastActive: Date.now() - 86400000 },
    ],
    maxMembers: 20,
    isPublic: true,
    createdAt: Date.now() - 86400000 * 100,
    activities: [
      { id: 'a1', type: 'study', title: 'Sylow定理专题研讨', description: '深入讨论Sylow定理的证明和应用', scheduledAt: Date.now() + 86400000, duration: 120, participants: [], status: 'upcoming' },
    ],
    resources: [],
    discussionTopics: [],
    schedule: [
      { id: 's1', dayOfWeek: 6, startTime: '20:00', duration: 120, topic: '群论习题讨论', isRecurring: true },
    ],
  },
  {
    id: 'g2',
    name: '数学分析进阶',
    description: '面向有一定分析基础的学习者，探讨实分析、复分析和泛函分析的高级主题。',
    category: 'analysis',
    tags: ['实分析', '测度论', '泛函分析'],
    owner: { id: 'u4', name: '分析专家', level: 12, points: 8000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 300 },
    members: [
      { user: { id: 'u4', name: '分析专家', level: 12, points: 8000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 300 }, role: 'owner', joinedAt: Date.now() - 86400000 * 150, contribution: 800, lastActive: Date.now() },
      { user: { id: 'u5', name: '极限追求者', level: 7, points: 2500, badges: [], role: 'admin', joinDate: Date.now() - 86400000 * 120 }, role: 'admin', joinedAt: Date.now() - 86400000 * 100, contribution: 300, lastActive: Date.now() - 3600000 * 2 },
    ],
    maxMembers: 15,
    isPublic: true,
    createdAt: Date.now() - 86400000 * 150,
    activities: [],
    resources: [],
    discussionTopics: [],
    schedule: [
      { id: 's2', dayOfWeek: 3, startTime: '19:30', duration: 90, topic: '测度论专题', isRecurring: true },
    ],
  },
  {
    id: 'g3',
    name: '拓扑学探索者',
    description: '从点集拓扑到代数拓扑，一起探索拓扑学的奇妙世界。',
    category: 'topology',
    tags: ['点集拓扑', '代数拓扑', '同伦论'],
    owner: { id: 'u6', name: '拓扑迷', level: 8, points: 3500, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 180 },
    members: [
      { user: { id: 'u6', name: '拓扑迷', level: 8, points: 3500, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 180 }, role: 'owner', joinedAt: Date.now() - 86400000 * 80, contribution: 250, lastActive: Date.now() - 3600000 },
    ],
    maxMembers: 25,
    isPublic: true,
    createdAt: Date.now() - 86400000 * 80,
    activities: [],
    resources: [],
    discussionTopics: [],
    schedule: [],
  },
];

export const StudyGroups: React.FC<StudyGroupsProps> = ({ className }) => {
  const [groups, setGroups] = useState<StudyGroup[]>(mockGroups);
  const [selectedGroup, setSelectedGroup] = useState<StudyGroup | null>(null);
  const [activeTab, setActiveTab] = useState<'all' | 'my'>('all');
  const [selectedCategory, setSelectedCategory] = useState<GroupCategory | null>(null);
  const [searchQuery, setSearchQuery] = useState('');

  const filteredGroups = groups.filter(group => {
    if (selectedCategory && group.category !== selectedCategory) return false;
    if (searchQuery && !group.name.toLowerCase().includes(searchQuery.toLowerCase())) return false;
    return true;
  });

  const handleJoinGroup = (groupId: string) => {
    setGroups(prev => prev.map(g => {
      if (g.id === groupId) {
        return {
          ...g,
          members: [...g.members, {
            user: { id: 'me', name: '我', level: 5, points: 1000, badges: [], role: 'member', joinDate: Date.now() },
            role: 'member',
            joinedAt: Date.now(),
            contribution: 0,
            lastActive: Date.now(),
          }],
        };
      }
      return g;
    }));
  };

  // 小组详情视图
  if (selectedGroup) {
    return (
      <div className={cn("space-y-6", className)}>
        {/* 返回按钮 */}
        <button
          onClick={() => setSelectedGroup(null)}
          className="flex items-center gap-2 text-gray-600 hover:text-gray-900 dark:text-gray-400 dark:hover:text-white transition-colors"
        >
          <ChevronRight className="w-4 h-4 rotate-180" />
          返回小组列表
        </button>

        {/* 小组封面 */}
        <div className="bg-gradient-to-r from-blue-600 to-purple-600 rounded-2xl p-8 text-white">
          <div className="flex items-start justify-between">
            <div>
              <div className="flex items-center gap-3 mb-3">
                <span className="text-4xl">{groupCategories.find(c => c.value === selectedGroup.category)?.icon}</span>
                <div>
                  <h1 className="text-3xl font-bold">{selectedGroup.name}</h1>
                  <div className="flex items-center gap-2 text-blue-100">
                    {selectedGroup.isPublic ? <Globe className="w-4 h-4" /> : <Lock className="w-4 h-4" />}
                    <span>{selectedGroup.isPublic ? '公开小组' : '私密小组'}</span>
                  </div>
                </div>
              </div>
              <p className="text-blue-100 max-w-2xl">{selectedGroup.description}</p>
              
              <div className="flex items-center gap-6 mt-6">
                <div className="flex items-center gap-2">
                  <Users className="w-5 h-5" />
                  <span>{selectedGroup.members.length}/{selectedGroup.maxMembers} 成员</span>
                </div>
                <div className="flex items-center gap-2">
                  <Calendar className="w-5 h-5" />
                  <span>创建于 {formatDistanceToNow(selectedGroup.createdAt)}</span>
                </div>
              </div>
            </div>

            {/* 加入按钮 */}
            {!selectedGroup.members.find(m => m.user.id === 'me') && (
              <button 
                onClick={() => handleJoinGroup(selectedGroup.id)}
                disabled={selectedGroup.members.length >= selectedGroup.maxMembers}
                className="px-6 py-3 bg-white text-blue-600 rounded-xl font-medium hover:bg-blue-50 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
              >
                <UserPlus className="w-5 h-5 inline mr-2" />
                加入小组
              </button>
            )}
          </div>
        </div>

        {/* 内容区域 */}
        <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
          {/* 左侧内容 */}
          <div className="lg:col-span-2 space-y-6">
            {/* 近期活动 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              <div className="flex items-center justify-between mb-4">
                <h3 className="text-lg font-semibold text-gray-900 dark:text-white">近期活动</h3>
                <button className="text-blue-600 hover:text-blue-700 text-sm">查看全部</button>
              </div>
              
              {selectedGroup.activities.length === 0 ? (
                <p className="text-gray-500 text-center py-8">暂无活动</p>
              ) : (
                <div className="space-y-3">
                  {selectedGroup.activities.map(activity => (
                    <ActivityCard key={activity.id} activity={activity} />
                  ))}
                </div>
              )}
            </div>

            {/* 学习日程 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">学习日程</h3>
              
              {selectedGroup.schedule.length === 0 ? (
                <p className="text-gray-500 text-center py-8">暂无固定日程</p>
              ) : (
                <div className="space-y-3">
                  {selectedGroup.schedule.map(schedule => (
                    <div key={schedule.id} className="flex items-center gap-4 p-3 bg-gray-50 dark:bg-slate-700 rounded-lg">
                      <div className="w-12 h-12 bg-blue-100 dark:bg-blue-900/30 rounded-lg flex items-center justify-center">
                        <Clock className="w-6 h-6 text-blue-600" />
                      </div>
                      <div className="flex-1">
                        <div className="font-medium text-gray-900 dark:text-white">{schedule.topic}</div>
                        <div className="text-sm text-gray-500">
                          每周{['日', '一', '二', '三', '四', '五', '六'][schedule.dayOfWeek]} {schedule.startTime} · {schedule.duration}分钟
                          {schedule.isRecurring && <span className="ml-2 text-blue-600">循环</span>}
                        </div>
                      </div>
                    </div>
                  ))}
                </div>
              )}
            </div>
          </div>

          {/* 右侧边栏 */}
          <div className="space-y-6">
            {/* 成员列表 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              <div className="flex items-center justify-between mb-4">
                <h3 className="text-lg font-semibold text-gray-900 dark:text-white">成员</h3>
                <span className="text-sm text-gray-500">{selectedGroup.members.length}人</span>
              </div>
              
              <div className="space-y-3">
                {selectedGroup.members.slice(0, 5).map(member => (
                  <div key={member.user.id} className="flex items-center gap-3">
                    <div className="w-10 h-10 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white font-medium">
                      {member.user.name.charAt(0)}
                    </div>
                    <div className="flex-1 min-w-0">
                      <div className="font-medium text-gray-900 dark:text-white truncate">
                        {member.user.name}
                        {member.role === 'owner' && <span className="ml-2 text-xs text-orange-500">组长</span>}
                        {member.role === 'admin' && <span className="ml-2 text-xs text-blue-500">管理员</span>}
                      </div>
                      <div className="text-sm text-gray-500">
                        等级{member.user.level} · 贡献{member.contribution}
                      </div>
                    </div>
                  </div>
                ))}
              </div>
              
              {selectedGroup.members.length > 5 && (
                <button className="w-full mt-4 text-center text-blue-600 hover:text-blue-700 text-sm">
                  查看全部成员
                </button>
              )}
            </div>

            {/* 标签 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">标签</h3>
              <div className="flex flex-wrap gap-2">
                {selectedGroup.tags.map(tag => (
                  <span key={tag} className="px-3 py-1 bg-gray-100 dark:bg-slate-700 text-gray-700 dark:text-gray-300 rounded-full text-sm">
                    {tag}
                  </span>
                ))}
              </div>
            </div>

            {/* 小组统计 */}
            <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
              <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">小组统计</h3>
              <div className="space-y-3">
                <div className="flex justify-between">
                  <span className="text-gray-500">讨论主题</span>
                  <span className="font-medium text-gray-900 dark:text-white">{selectedGroup.discussionTopics.length}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-500">共享资源</span>
                  <span className="font-medium text-gray-900 dark:text-white">{selectedGroup.resources.length}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-500">已完成活动</span>
                  <span className="font-medium text-gray-900 dark:text-white">
                    {selectedGroup.activities.filter(a => a.status === 'completed').length}
                  </span>
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className={cn("space-y-6", className)}>
      {/* 头部工具栏 */}
      <div className="flex flex-col sm:flex-row gap-4 items-start sm:items-center justify-between">
        <div className="relative flex-1 max-w-md">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
          <input
            type="text"
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            placeholder="搜索学习小组..."
            className="w-full pl-10 pr-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          />
        </div>

        <button className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors">
          <Plus className="w-4 h-4" />
          创建小组
        </button>
      </div>

      {/* Tab 切换 */}
      <div className="flex gap-2 border-b border-gray-200 dark:border-slate-700">
        {[
          { key: 'all', label: '全部小组' },
          { key: 'my', label: '我的小组' },
        ].map(tab => (
          <button
            key={tab.key}
            onClick={() => setActiveTab(tab.key as any)}
            className={cn(
              "px-4 py-2 text-sm font-medium transition-colors border-b-2",
              activeTab === tab.key
                ? "text-blue-600 border-blue-600"
                : "text-gray-600 border-transparent hover:text-gray-900 dark:text-gray-400 dark:hover:text-white"
            )}
          >
            {tab.label}
          </button>
        ))}
      </div>

      {/* 分类筛选 */}
      <div className="flex flex-wrap gap-2">
        <button
          onClick={() => setSelectedCategory(null)}
          className={cn(
            "px-3 py-1.5 rounded-full text-sm font-medium transition-colors",
            !selectedCategory
              ? "bg-gray-900 text-white dark:bg-white dark:text-gray-900"
              : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
          )}
        >
          全部
        </button>
        {groupCategories.map(cat => (
          <button
            key={cat.value}
            onClick={() => setSelectedCategory(cat.value)}
            className={cn(
              "px-3 py-1.5 rounded-full text-sm font-medium transition-colors",
              selectedCategory === cat.value
                ? "bg-blue-100 text-blue-700 dark:bg-blue-900/50 dark:text-blue-300"
                : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
            )}
          >
            {cat.icon} {cat.label}
          </button>
        ))}
      </div>

      {/* 小组列表 */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
        {filteredGroups.length === 0 ? (
          <div className="col-span-full text-center py-12">
            <Users className="w-12 h-12 text-gray-300 mx-auto mb-4" />
            <p className="text-gray-500">暂无学习小组</p>
          </div>
        ) : (
          filteredGroups.map(group => (
            <div
              key={group.id}
              onClick={() => setSelectedGroup(group)}
              className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700 hover:shadow-lg transition-shadow cursor-pointer"
            >
              <div className="flex items-start gap-4">
                <div className="w-16 h-16 bg-gradient-to-br from-blue-500 to-purple-500 rounded-xl flex items-center justify-center text-3xl">
                  {groupCategories.find(c => c.value === group.category)?.icon}
                </div>
                
                <div className="flex-1 min-w-0">
                  <div className="flex items-start justify-between">
                    <h3 className="font-semibold text-gray-900 dark:text-white truncate">
                      {group.name}
                    </h3>
                    {group.isPublic ? (
                      <Globe className="w-4 h-4 text-gray-400" />
                    ) : (
                      <Lock className="w-4 h-4 text-gray-400" />
                    )}
                  </div>
                  
                  <p className="text-gray-600 dark:text-gray-400 text-sm line-clamp-2 mt-1">
                    {group.description}
                  </p>
                  
                  <div className="flex items-center gap-4 mt-3 text-sm text-gray-500">
                    <span className="flex items-center gap-1">
                      <Users className="w-4 h-4" />
                      {group.members.length}/{group.maxMembers}
                    </span>
                    <span className="flex items-center gap-1">
                      <MessageSquare className="w-4 h-4" />
                      {group.discussionTopics.length}
                    </span>
                    <span className="flex items-center gap-1">
                      <BookOpen className="w-4 h-4" />
                      {group.resources.length}
                    </span>
                  </div>

                  <div className="flex flex-wrap gap-1 mt-3">
                    {group.tags.slice(0, 3).map(tag => (
                      <span key={tag} className="text-xs px-2 py-0.5 bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-400 rounded">
                        {tag}
                      </span>
                    ))}
                  </div>
                </div>
              </div>
            </div>
          ))
        )}
      </div>
    </div>
  );
};

// 活动卡片组件
const ActivityCard: React.FC<{ activity: GroupActivity }> = ({ activity }) => {
  const typeConfig = {
    study: { icon: BookOpen, color: 'bg-blue-100 text-blue-700' },
    discussion: { icon: MessageSquare, color: 'bg-green-100 text-green-700' },
    challenge: { icon: Star, color: 'bg-purple-100 text-purple-700' },
    review: { icon: Clock, color: 'bg-orange-100 text-orange-700' },
    qanda: { icon: MessageSquare, color: 'bg-pink-100 text-pink-700' },
  };

  const config = typeConfig[activity.type];
  const Icon = config.icon;

  return (
    <div className="flex items-center gap-4 p-4 bg-gray-50 dark:bg-slate-700 rounded-lg">
      <div className={cn("w-12 h-12 rounded-lg flex items-center justify-center", config.color)}>
        <Icon className="w-6 h-6" />
      </div>
      <div className="flex-1">
        <div className="font-medium text-gray-900 dark:text-white">{activity.title}</div>
        <div className="text-sm text-gray-500">{activity.description}</div>
        <div className="text-sm text-gray-500 mt-1">
          <Clock className="w-3 h-3 inline mr-1" />
          {new Date(activity.scheduledAt).toLocaleString('zh-CN')} · {activity.duration}分钟
        </div>
      </div>
      <span className={cn(
        "px-2 py-1 text-xs rounded-full",
        activity.status === 'upcoming' ? 'bg-yellow-100 text-yellow-700' :
        activity.status === 'ongoing' ? 'bg-green-100 text-green-700' :
        activity.status === 'completed' ? 'bg-gray-100 text-gray-700' :
        'bg-red-100 text-red-700'
      )}>
        {activity.status === 'upcoming' ? '即将开始' :
         activity.status === 'ongoing' ? '进行中' :
         activity.status === 'completed' ? '已结束' : '已取消'}
      </span>
    </div>
  );
};

export default StudyGroups;
