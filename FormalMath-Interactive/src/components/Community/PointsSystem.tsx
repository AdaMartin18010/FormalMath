import React, { useState } from 'react';
import {
  Trophy,
  Star,
  Zap,
  Target,
  Calendar,
  TrendingUp,
  Award,
  Gift,
  CheckCircle2,
  Clock,
  Flame,
  Medal,
  Crown,
  Gem,
  ChevronRight,
  Lock
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { PointsRecord, PointsType, Badge, LevelDefinition } from '../../types/community';

interface PointsSystemProps {
  className?: string;
}

// 积分规则
const pointsRules: { type: PointsType; points: number; icon: React.ElementType; description: string }[] = [
  { type: 'daily_login', points: 10, icon: Calendar, description: '每日登录' },
  { type: 'post_topic', points: 20, icon: Trophy, description: '发布讨论主题' },
  { type: 'post_reply', points: 10, icon: Zap, description: '发布回复' },
  { type: 'receive_like', points: 5, icon: Star, description: '获得点赞' },
  { type: 'answer_accepted', points: 50, icon: CheckCircle2, description: '答案被采纳' },
  { type: 'share_resource', points: 30, icon: Gift, description: '分享资源' },
  { type: 'complete_challenge', points: 100, icon: Target, description: '完成挑战' },
  { type: 'help_others', points: 15, icon: Medal, description: '帮助他人' },
  { type: 'excellent_content', points: 100, icon: Crown, description: '优质内容' },
];

// 等级定义
const levelDefinitions: LevelDefinition[] = [
  { level: 1, name: '数学新手', minPoints: 0, maxPoints: 100, icon: '🌱', privileges: ['基础功能'] },
  { level: 2, name: '学习爱好者', minPoints: 100, maxPoints: 300, icon: '🌿', privileges: ['发表评论', '点赞'] },
  { level: 3, name: '探索者', minPoints: 300, maxPoints: 600, icon: '🍃', privileges: ['发布讨论', '上传资源'] },
  { level: 4, name: '学徒', minPoints: 600, maxPoints: 1000, icon: '🌾', privileges: ['创建小组'] },
  { level: 5, name: '初级学者', minPoints: 1000, maxPoints: 1500, icon: '🌲', privileges: ['悬赏提问'] },
  { level: 6, name: '进阶学者', minPoints: 1500, maxPoints: 2200, icon: '⭐', privileges: ['高级徽章'] },
  { level: 7, name: '熟练学者', minPoints: 2200, maxPoints: 3000, icon: '🌟', privileges: ['小组管理'] },
  { level: 8, name: '高级学者', minPoints: 3000, maxPoints: 4000, icon: '💫', privileges: ['专属标识'] },
  { level: 9, name: '专家', minPoints: 4000, maxPoints: 5500, icon: '🏆', privileges: ['专家认证'] },
  { level: 10, name: '大师', minPoints: 5500, maxPoints: 7500, icon: '👑', privileges: ['内容审核'] },
  { level: 11, name: '宗师', minPoints: 7500, maxPoints: 10000, icon: '🎓', privileges: ['导师权限'] },
  { level: 12, name: '传奇', minPoints: 10000, maxPoints: 999999, icon: '👑', privileges: ['所有权限'] },
];

// 徽章数据
const mockBadges: Badge[] = [
  { id: 'b1', name: '初来乍到', description: '完成首次登录', icon: '🌟', category: 'participation', earnedAt: Date.now() - 86400000 * 30, rarity: 'common' },
  { id: 'b2', name: '活跃分子', description: '连续登录7天', icon: '🔥', category: 'participation', earnedAt: Date.now() - 86400000 * 20, rarity: 'common' },
  { id: 'b3', name: '乐于助人', description: '回答被采纳10次', icon: '💡', category: 'contribution', earnedAt: Date.now() - 86400000 * 15, rarity: 'rare' },
  { id: 'b4', name: '知识分享者', description: '分享20个资源', icon: '📚', category: 'contribution', earnedAt: Date.now() - 86400000 * 10, rarity: 'rare' },
  { id: 'b5', name: '问题终结者', description: '解决50个问题', icon: '⚡', category: 'expertise', earnedAt: Date.now() - 86400000 * 5, rarity: 'epic' },
];

// 模拟积分记录
const mockRecords: PointsRecord[] = [
  { id: 'p1', userId: 'me', points: 10, type: 'daily_login', description: '每日登录', createdAt: Date.now() - 3600000 * 2 },
  { id: 'p2', userId: 'me', points: 20, type: 'post_topic', description: '发布讨论: 如何理解群论', createdAt: Date.now() - 86400000 },
  { id: 'p3', userId: 'me', points: 50, type: 'answer_accepted', description: '答案被采纳: Sylow定理解释', createdAt: Date.now() - 86400000 * 2 },
  { id: 'p4', userId: 'me', points: 5, type: 'receive_like', description: '获得3个点赞', createdAt: Date.now() - 86400000 * 3 },
  { id: 'p5', userId: 'me', points: 30, type: 'share_resource', description: '分享资源: 拓扑学笔记', createdAt: Date.now() - 86400000 * 5 },
];

// 排行榜数据
const mockLeaderboard = [
  { rank: 1, name: '数学大师', level: 12, points: 12500, avatar: '👑' },
  { rank: 2, name: '代数专家', level: 11, points: 10800, avatar: '🎓' },
  { rank: 3, name: '分析达人', level: 10, points: 9200, avatar: '🏆' },
  { rank: 4, name: '拓扑迷', level: 9, points: 7800, avatar: '⭐' },
  { rank: 5, name: '几何爱好者', level: 8, points: 6500, avatar: '🌟' },
];

export const PointsSystem: React.FC<PointsSystemProps> = ({ className }) => {
  const [activeTab, setActiveTab] = useState<'overview' | 'history' | 'badges' | 'leaderboard'>('overview');
  const [currentPoints, setCurrentPoints] = useState(2850);
  const [currentLevel, setCurrentLevel] = useState(7);
  const [streakDays, setStreakDays] = useState(12);
  const [isCheckedIn, setIsCheckedIn] = useState(false);

  const level = levelDefinitions.find(l => l.level === currentLevel) || levelDefinitions[0];
  const nextLevel = levelDefinitions.find(l => l.level === currentLevel + 1);
  const progress = nextLevel 
    ? ((currentPoints - level.minPoints) / (nextLevel.minPoints - level.minPoints)) * 100
    : 100;

  const handleCheckIn = () => {
    if (!isCheckedIn) {
      setCurrentPoints(prev => prev + 10);
      setIsCheckedIn(true);
      setStreakDays(prev => prev + 1);
    }
  };

  // 概览视图
  const OverviewView = () => (
    <div className="space-y-6">
      {/* 等级卡片 */}
      <div className="bg-gradient-to-r from-blue-600 to-purple-600 rounded-2xl p-8 text-white">
        <div className="flex items-center justify-between mb-6">
          <div>
            <div className="text-blue-100 mb-1">当前等级</div>
            <div className="text-4xl font-bold flex items-center gap-3">
              <span className="text-5xl">{level.icon}</span>
              <div>
                <div className="text-2xl">{level.name}</div>
                <div className="text-sm text-blue-100">Level {currentLevel}</div>
              </div>
            </div>
          </div>
          <div className="text-right">
            <div className="text-3xl font-bold">{currentPoints.toLocaleString()}</div>
            <div className="text-blue-100">总积分</div>
          </div>
        </div>

        {/* 进度条 */}
        {nextLevel && (
          <div>
            <div className="flex justify-between text-sm text-blue-100 mb-2">
              <span>当前: {currentPoints} 分</span>
              <span>下一等级: {nextLevel.minPoints} 分</span>
            </div>
            <div className="h-3 bg-white/20 rounded-full overflow-hidden">
              <div 
                className="h-full bg-white rounded-full transition-all duration-500"
                style={{ width: `${progress}%` }}
              />
            </div>
            <div className="text-sm text-blue-100 mt-2 text-center">
              还需 {nextLevel.minPoints - currentPoints} 分升级到 {nextLevel.name}
            </div>
          </div>
        )}
      </div>

      {/* 统计卡片 */}
      <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
        <div className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 bg-orange-100 dark:bg-orange-900/30 rounded-lg flex items-center justify-center">
              <Flame className="w-5 h-5 text-orange-600" />
            </div>
            <div>
              <div className="text-2xl font-bold text-gray-900 dark:text-white">{streakDays}</div>
              <div className="text-sm text-gray-500">连续签到</div>
            </div>
          </div>
        </div>
        
        <div className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 bg-blue-100 dark:bg-blue-900/30 rounded-lg flex items-center justify-center">
              <Trophy className="w-5 h-5 text-blue-600" />
            </div>
            <div>
              <div className="text-2xl font-bold text-gray-900 dark:text-white">{mockBadges.length}</div>
              <div className="text-sm text-gray-500">获得徽章</div>
            </div>
          </div>
        </div>
        
        <div className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 bg-green-100 dark:bg-green-900/30 rounded-lg flex items-center justify-center">
              <Target className="w-5 h-5 text-green-600" />
            </div>
            <div>
              <div className="text-2xl font-bold text-gray-900 dark:text-white">85%</div>
              <div className="text-sm text-gray-500">本周目标</div>
            </div>
          </div>
        </div>
        
        <div className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 bg-purple-100 dark:bg-purple-900/30 rounded-lg flex items-center justify-center">
              <TrendingUp className="w-5 h-5 text-purple-600" />
            </div>
            <div>
              <div className="text-2xl font-bold text-gray-900 dark:text-white">+156</div>
              <div className="text-sm text-gray-500">本周获得</div>
            </div>
          </div>
        </div>
      </div>

      {/* 签到按钮 */}
      <div className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700">
        <div className="flex items-center justify-between">
          <div>
            <h3 className="text-lg font-semibold text-gray-900 dark:text-white">每日签到</h3>
            <p className="text-gray-500">连续签到可获得额外积分奖励</p>
          </div>
          <button
            onClick={handleCheckIn}
            disabled={isCheckedIn}
            className={cn(
              "px-6 py-3 rounded-xl font-medium transition-colors",
              isCheckedIn
                ? "bg-gray-100 text-gray-400 cursor-not-allowed"
                : "bg-blue-600 text-white hover:bg-blue-700"
            )}
          >
            {isCheckedIn ? '今日已签到' : '立即签到 +10分'}
          </button>
        </div>
        
        {/* 签到日历 */}
        <div className="mt-6">
          <div className="flex justify-between">
            {['一', '二', '三', '四', '五', '六', '日'].map((day, i) => (
              <div key={day} className="flex flex-col items-center">
                <span className="text-sm text-gray-500 mb-2">{day}</span>
                <div className={cn(
                  "w-10 h-10 rounded-lg flex items-center justify-center",
                  i < 5 ? "bg-green-100 text-green-600" : "bg-gray-100 text-gray-400"
                )}>
                  {i < 5 ? <CheckCircle2 className="w-5 h-5" /> : <span className="text-sm">{15 + i}</span>}
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>

      {/* 快速获得积分 */}
      <div className="bg-white dark:bg-slate-800 rounded-xl p-6 border border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">快速获得积分</h3>
        <div className="grid grid-cols-1 sm:grid-cols-2 md:grid-cols-3 gap-4">
          {pointsRules.slice(0, 6).map(rule => (
            <div key={rule.type} className="flex items-center gap-3 p-3 bg-gray-50 dark:bg-slate-700 rounded-lg">
              <div className="w-10 h-10 bg-blue-100 dark:bg-blue-900/30 rounded-lg flex items-center justify-center">
                <rule.icon className="w-5 h-5 text-blue-600" />
              </div>
              <div className="flex-1">
                <div className="text-sm font-medium text-gray-900 dark:text-white">{rule.description}</div>
                <div className="text-sm text-green-600">+{rule.points} 分</div>
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );

  // 历史记录视图
  const HistoryView = () => (
    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700">
      <div className="p-6 border-b border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white">积分记录</h3>
      </div>
      <div className="divide-y divide-gray-200 dark:divide-slate-700">
        {mockRecords.map(record => {
          const rule = pointsRules.find(r => r.type === record.type);
          const Icon = rule?.icon || Star;
          
          return (
            <div key={record.id} className="p-4 flex items-center gap-4">
              <div className={cn(
                "w-10 h-10 rounded-lg flex items-center justify-center",
                record.points > 0 ? "bg-green-100 dark:bg-green-900/30" : "bg-red-100 dark:bg-red-900/30"
              )}>
                <Icon className={cn(
                  "w-5 h-5",
                  record.points > 0 ? "text-green-600" : "text-red-600"
                )} />
              </div>
              <div className="flex-1">
                <div className="font-medium text-gray-900 dark:text-white">{record.description}</div>
                <div className="text-sm text-gray-500">
                  {new Date(record.createdAt).toLocaleString('zh-CN')}
                </div>
              </div>
              <div className={cn(
                "font-semibold",
                record.points > 0 ? "text-green-600" : "text-red-600"
              )}>
                {record.points > 0 ? '+' : ''}{record.points}
              </div>
            </div>
          );
        })}
      </div>
    </div>
  );

  // 徽章视图
  const BadgesView = () => (
    <div className="space-y-6">
      {/* 已获得徽章 */}
      <div>
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
          已获得徽章 ({mockBadges.length})
        </h3>
        <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-5 gap-4">
          {mockBadges.map(badge => (
            <div key={badge.id} className="bg-white dark:bg-slate-800 rounded-xl p-4 border border-gray-200 dark:border-slate-700 text-center hover:shadow-md transition-shadow">
              <div className="text-4xl mb-3">{badge.icon}</div>
              <div className="font-medium text-gray-900 dark:text-white mb-1">{badge.name}</div>
              <div className="text-sm text-gray-500 mb-2">{badge.description}</div>
              <span className={cn(
                "text-xs px-2 py-1 rounded-full",
                badge.rarity === 'common' ? 'bg-gray-100 text-gray-600' :
                badge.rarity === 'rare' ? 'bg-blue-100 text-blue-600' :
                badge.rarity === 'epic' ? 'bg-purple-100 text-purple-600' :
                'bg-yellow-100 text-yellow-600'
              )}>
                {badge.rarity === 'common' ? '普通' :
                 badge.rarity === 'rare' ? '稀有' :
                 badge.rarity === 'epic' ? '史诗' : '传说'}
              </span>
            </div>
          ))}
        </div>
      </div>

      {/* 未获得徽章 */}
      <div>
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">未获得徽章</h3>
        <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-5 gap-4">
          {[
            { name: '回答大师', description: '回答100个问题', icon: '🏆', rarity: 'epic' },
            { name: '资源王', description: '分享100个资源', icon: '📚', rarity: 'legendary' },
            { name: '签到王者', description: '连续签到30天', icon: '👑', rarity: 'rare' },
            { name: '被赞达人', description: '获得1000个赞', icon: '❤️', rarity: 'rare' },
          ].map((badge, i) => (
            <div key={i} className="bg-gray-100 dark:bg-slate-700/50 rounded-xl p-4 border border-gray-200 dark:border-slate-700 text-center opacity-60">
              <div className="text-4xl mb-3 grayscale">{badge.icon}</div>
              <div className="font-medium text-gray-500 mb-1">{badge.name}</div>
              <div className="text-sm text-gray-400 mb-2">{badge.description}</div>
              <Lock className="w-4 h-4 mx-auto text-gray-400" />
            </div>
          ))}
        </div>
      </div>
    </div>
  );

  // 排行榜视图
  const LeaderboardView = () => (
    <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden">
      <div className="p-6 border-b border-gray-200 dark:border-slate-700">
        <h3 className="text-lg font-semibold text-gray-900 dark:text-white">积分排行榜</h3>
      </div>
      
      {/* 前三名 */}
      <div className="p-6 bg-gradient-to-b from-yellow-50 to-white dark:from-yellow-900/10 dark:to-slate-800">
        <div className="flex justify-center items-end gap-4">
          {mockLeaderboard.slice(0, 3).map((user, index) => (
            <div key={user.rank} className={cn(
              "text-center",
              index === 1 ? "order-1" : index === 0 ? "order-2" : "order-3"
            )}>
              <div className={cn(
                "w-16 h-16 rounded-full flex items-center justify-center text-2xl mx-auto mb-2",
                index === 0 ? "bg-yellow-400 text-yellow-900" :
                index === 1 ? "bg-gray-300 text-gray-700" :
                "bg-orange-400 text-orange-900"
              )}>
                {user.avatar}
              </div>
              <div className="font-semibold text-gray-900 dark:text-white">{user.name}</div>
              <div className="text-sm text-gray-500">Lv.{user.level}</div>
              <div className="text-lg font-bold text-blue-600">{user.points.toLocaleString()}</div>
            </div>
          ))}
        </div>
      </div>

      {/* 其他排名 */}
      <div className="divide-y divide-gray-200 dark:divide-slate-700">
        {mockLeaderboard.slice(3).map(user => (
          <div key={user.rank} className="p-4 flex items-center gap-4">
            <div className="w-8 text-center font-bold text-gray-400">{user.rank}</div>
            <div className="w-10 h-10 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white">
              {user.avatar}
            </div>
            <div className="flex-1">
              <div className="font-medium text-gray-900 dark:text-white">{user.name}</div>
              <div className="text-sm text-gray-500">等级 {user.level}</div>
            </div>
            <div className="font-semibold text-blue-600">{user.points.toLocaleString()} 分</div>
          </div>
        ))}
      </div>
    </div>
  );

  return (
    <div className={cn("space-y-6", className)}>
      {/* Tab 切换 */}
      <div className="flex gap-2 border-b border-gray-200 dark:border-slate-700">
        {[
          { key: 'overview', label: '概览', icon: Trophy },
          { key: 'history', label: '记录', icon: Clock },
          { key: 'badges', label: '徽章', icon: Award },
          { key: 'leaderboard', label: '排行榜', icon: TrendingUp },
        ].map(tab => (
          <button
            key={tab.key}
            onClick={() => setActiveTab(tab.key as any)}
            className={cn(
              "flex items-center gap-2 px-4 py-3 text-sm font-medium transition-colors border-b-2",
              activeTab === tab.key
                ? "text-blue-600 border-blue-600"
                : "text-gray-600 border-transparent hover:text-gray-900 dark:text-gray-400 dark:hover:text-white"
            )}
          >
            <tab.icon className="w-4 h-4" />
            {tab.label}
          </button>
        ))}
      </div>

      {/* 内容区域 */}
      {activeTab === 'overview' && <OverviewView />}
      {activeTab === 'history' && <HistoryView />}
      {activeTab === 'badges' && <BadgesView />}
      {activeTab === 'leaderboard' && <LeaderboardView />}
    </div>
  );
};

export default PointsSystem;
