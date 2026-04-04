import React, { useState } from 'react';
import { Trophy, Medal, Crown, Flame, Target, Clock, TrendingUp, ChevronDown, ChevronUp } from 'lucide-react';

type LeaderboardType = 'weekly' | 'monthly' | 'all-time' | 'streak' | 'problems';
type LeaderboardScope = 'global' | 'friends' | 'group';

interface LeaderboardEntry {
  rank: number;
  userId: string;
  name: string;
  avatar?: string;
  score: number;
  stats: {
    studyTime: number;
    problemsSolved: number;
    streak: number;
    accuracy: number;
  };
  trend: 'up' | 'down' | 'stable';
  rankChange: number;
  isCurrentUser?: boolean;
}

interface LeaderboardProps {
  type?: LeaderboardType;
  scope?: LeaderboardScope;
  entries: LeaderboardEntry[];
  currentUserId?: string;
  onViewProfile?: (userId: string) => void;
  className?: string;
}

const typeLabels: Record<LeaderboardType, string> = {
  weekly: '本周排行',
  monthly: '本月排行',
  'all-time': '总排行',
  streak: '连续学习',
  problems: '解题达人',
};

const scopeLabels: Record<LeaderboardScope, string> = {
  global: '全站',
  friends: '好友',
  group: '学习组',
};

export const Leaderboard: React.FC<LeaderboardProps> = ({
  type = 'weekly',
  scope = 'global',
  entries,
  currentUserId,
  onViewProfile,
  className = '',
}) => {
  const [selectedType, setSelectedType] = useState<LeaderboardType>(type);
  const [selectedScope, setSelectedScope] = useState<LeaderboardScope>(scope);
  const [showAll, setShowAll] = useState(false);

  // 过滤和排序条目
  const filteredEntries = entries
    .filter(e => {
      if (selectedScope === 'friends') return true; // 假设 entries 已经过滤
      if (selectedScope === 'group') return true;
      return true;
    })
    .sort((a, b) => a.rank - b.rank);

  // 显示前10或全部
  const displayEntries = showAll ? filteredEntries : filteredEntries.slice(0, 10);

  // 当前用户条目
  const currentUserEntry = filteredEntries.find(e => e.isCurrentUser);

  const getRankIcon = (rank: number) => {
    switch (rank) {
      case 1:
        return <Crown size={24} className="text-yellow-500" />;
      case 2:
        return <Medal size={24} className="text-gray-400" />;
      case 3:
        return <Medal size={24} className="text-orange-500" />;
      default:
        return <span className="text-gray-400 font-medium">{rank}</span>;
    }
  };

  const getTrendIcon = (trend: LeaderboardEntry['trend'], change: number) => {
    if (trend === 'up') {
      return (
        <span className="flex items-center gap-1 text-green-500 text-xs">
          <ChevronUp size={14} />
          {change > 0 && change}
        </span>
      );
    }
    if (trend === 'down') {
      return (
        <span className="flex items-center gap-1 text-red-500 text-xs">
          <ChevronDown size={14} />
          {change > 0 && change}
        </span>
      );
    }
    return <span className="text-gray-400 text-xs">-</span>;
  };

  const formatScore = (score: number, type: LeaderboardType): string => {
    switch (type) {
      case 'streak':
        return `${score} 天`;
      case 'problems':
        return `${score} 题`;
      default:
        if (score >= 60) {
          return `${Math.floor(score / 60)}h ${score % 60}m`;
        }
        return `${score} 分`;
    }
  };

  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 头部 */}
      <div className="p-4 border-b border-gray-200">
        <div className="flex items-center justify-between mb-4">
          <div className="flex items-center gap-2">
            <Trophy className="text-yellow-500" size={24} />
            <h2 className="text-lg font-bold text-gray-800">排行榜</h2>
          </div>
          
          {/* 范围选择 */}
          <div className="flex bg-gray-100 rounded-lg p-1">
            {(Object.keys(scopeLabels) as LeaderboardScope[]).map((s) => (
              <button
                key={s}
                onClick={() => setSelectedScope(s)}
                className={`px-3 py-1 text-sm rounded-md transition-colors ${
                  selectedScope === s
                    ? 'bg-white text-gray-800 shadow-sm'
                    : 'text-gray-500 hover:text-gray-700'
                }`}
              >
                {scopeLabels[s]}
              </button>
            ))}
          </div>
        </div>

        {/* 类型选择 */}
        <div className="flex gap-2 overflow-x-auto pb-2 scrollbar-hide">
          {(Object.keys(typeLabels) as LeaderboardType[]).map((t) => (
            <button
              key={t}
              onClick={() => setSelectedType(t)}
              className={`px-4 py-2 rounded-full text-sm whitespace-nowrap transition-colors ${
                selectedType === t
                  ? 'bg-blue-500 text-white'
                  : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
              }`}
            >
              {typeLabels[t]}
            </button>
          ))}
        </div>
      </div>

      {/* 前三名展示 */}
      {filteredEntries.length >= 3 && (
        <div className="py-6 px-4 bg-gradient-to-b from-yellow-50 to-white">
          <div className="flex items-end justify-center gap-4">
            {/* 第二名 */}
            <div className="text-center">
              <div className="relative mb-2">
                {filteredEntries[1]?.avatar ? (
                  <img
                    src={filteredEntries[1].avatar}
                    alt={filteredEntries[1].name}
                    className="w-16 h-16 rounded-full border-4 border-gray-300 object-cover"
                  />
                ) : (
                  <div className="w-16 h-16 rounded-full border-4 border-gray-300 bg-gray-200 flex items-center justify-center text-xl">
                    {filteredEntries[1]?.name[0]}
                  </div>
                )}
                <div className="absolute -bottom-1 -right-1 w-6 h-6 bg-gray-400 rounded-full flex items-center justify-center text-white text-xs font-bold">
                  2
                </div>
              </div>
              <p className="font-medium text-gray-800 text-sm">{filteredEntries[1]?.name}</p>
              <p className="text-gray-500 text-xs">
                {formatScore(filteredEntries[1]?.score || 0, selectedType)}
              </p>
            </div>

            {/* 第一名 */}
            <div className="text-center -mt-4">
              <Crown className="mx-auto mb-1 text-yellow-500" size={28} />
              <div className="relative mb-2">
                {filteredEntries[0]?.avatar ? (
                  <img
                    src={filteredEntries[0].avatar}
                    alt={filteredEntries[0].name}
                    className="w-20 h-20 rounded-full border-4 border-yellow-400 object-cover"
                  />
                ) : (
                  <div className="w-20 h-20 rounded-full border-4 border-yellow-400 bg-yellow-100 flex items-center justify-center text-2xl">
                    {filteredEntries[0]?.name[0]}
                  </div>
                )}
                <div className="absolute -bottom-1 -right-1 w-7 h-7 bg-yellow-500 rounded-full flex items-center justify-center text-white text-sm font-bold">
                  1
                </div>
              </div>
              <p className="font-bold text-gray-800">{filteredEntries[0]?.name}</p>
              <p className="text-yellow-600 font-medium">
                {formatScore(filteredEntries[0]?.score || 0, selectedType)}
              </p>
            </div>

            {/* 第三名 */}
            <div className="text-center">
              <div className="relative mb-2">
                {filteredEntries[2]?.avatar ? (
                  <img
                    src={filteredEntries[2].avatar}
                    alt={filteredEntries[2].name}
                    className="w-16 h-16 rounded-full border-4 border-orange-400 object-cover"
                  />
                ) : (
                  <div className="w-16 h-16 rounded-full border-4 border-orange-400 bg-orange-100 flex items-center justify-center text-xl">
                    {filteredEntries[2]?.name[0]}
                  </div>
                )}
                <div className="absolute -bottom-1 -right-1 w-6 h-6 bg-orange-500 rounded-full flex items-center justify-center text-white text-xs font-bold">
                  3
                </div>
              </div>
              <p className="font-medium text-gray-800 text-sm">{filteredEntries[2]?.name}</p>
              <p className="text-gray-500 text-xs">
                {formatScore(filteredEntries[2]?.score || 0, selectedType)}
              </p>
            </div>
          </div>
        </div>
      )}

      {/* 排行榜列表 */}
      <div className="divide-y divide-gray-100">
        {displayEntries.map((entry) => (
          <div
            key={entry.userId}
            onClick={() => onViewProfile?.(entry.userId)}
            className={`
              flex items-center gap-3 p-4 hover:bg-gray-50 transition-colors cursor-pointer
              ${entry.isCurrentUser ? 'bg-blue-50 hover:bg-blue-100' : ''}
            `}
          >
            {/* 排名 */}
            <div className="w-10 flex justify-center">
              {getRankIcon(entry.rank)}
            </div>

            {/* 头像 */}
            <div className="relative">
              {entry.avatar ? (
                <img
                  src={entry.avatar}
                  alt={entry.name}
                  className="w-10 h-10 rounded-full object-cover"
                />
              ) : (
                <div className="w-10 h-10 rounded-full bg-gray-200 flex items-center justify-center text-gray-600">
                  {entry.name[0]}
                </div>
              )}
              {entry.stats.streak >= 7 && (
                <Flame size={14} className="absolute -top-1 -right-1 text-orange-500" />
              )}
            </div>

            {/* 用户信息 */}
            <div className="flex-1 min-w-0">
              <div className="flex items-center gap-2">
                <span className="font-medium text-gray-800 truncate">{entry.name}</span>
                {entry.isCurrentUser && (
                  <span className="px-2 py-0.5 bg-blue-100 text-blue-600 text-xs rounded">
                    我
                  </span>
                )}
              </div>
              <div className="flex items-center gap-3 text-xs text-gray-500 mt-0.5">
                <span className="flex items-center gap-1">
                  <Target size={12} />
                  {entry.stats.problemsSolved} 题
                </span>
                <span className="flex items-center gap-1">
                  <Clock size={12} />
                  {Math.floor(entry.stats.studyTime / 60)}h
                </span>
                <span className="flex items-center gap-1">
                  <Flame size={12} />
                  {entry.stats.streak} 天
                </span>
              </div>
            </div>

            {/* 趋势 */}
            <div className="w-12 text-right">
              {getTrendIcon(entry.trend, entry.rankChange)}
            </div>

            {/* 分数 */}
            <div className="text-right">
              <p className="font-bold text-gray-800">
                {formatScore(entry.score, selectedType)}
              </p>
            </div>
          </div>
        ))}
      </div>

      {/* 显示更多/收起 */}
      {filteredEntries.length > 10 && (
        <button
          onClick={() => setShowAll(!showAll)}
          className="w-full py-3 text-blue-500 hover:bg-blue-50 transition-colors text-sm font-medium"
        >
          {showAll ? '收起' : `查看全部 ${filteredEntries.length} 人`}
        </button>
      )}

      {/* 当前用户排名（如果不在前10） */}
      {currentUserEntry && !displayEntries.find(e => e.isCurrentUser) && (
        <div className="border-t-2 border-blue-200 bg-blue-50 p-4">
          <div className="flex items-center gap-3">
            <span className="w-10 text-center font-medium text-gray-600">
              {currentUserEntry.rank}
            </span>
            {currentUserEntry.avatar ? (
              <img
                src={currentUserEntry.avatar}
                alt={currentUserEntry.name}
                className="w-10 h-10 rounded-full object-cover"
              />
            ) : (
              <div className="w-10 h-10 rounded-full bg-blue-200 flex items-center justify-center text-blue-600">
                {currentUserEntry.name[0]}
              </div>
            )}
            <div className="flex-1">
              <p className="font-medium text-gray-800">{currentUserEntry.name}</p>
              <p className="text-xs text-gray-500">你的排名</p>
            </div>
            <p className="font-bold text-blue-600">
              {formatScore(currentUserEntry.score, selectedType)}
            </p>
          </div>
        </div>
      )}
    </div>
  );
};

// 小型排行榜卡片
interface MiniLeaderboardProps {
  title: string;
  entries: LeaderboardEntry[];
  onViewAll?: () => void;
  className?: string;
}

export const MiniLeaderboard: React.FC<MiniLeaderboardProps> = ({
  title,
  entries,
  onViewAll,
  className = '',
}) => {
  return (
    <div className={`bg-white rounded-lg shadow p-4 ${className}`}>
      <div className="flex items-center justify-between mb-4">
        <h3 className="font-bold text-gray-800">{title}</h3>
        <button
          onClick={onViewAll}
          className="text-sm text-blue-500 hover:text-blue-600"
        >
          查看全部
        </button>
      </div>

      <div className="space-y-3">
        {entries.slice(0, 5).map((entry, index) => (
          <div key={entry.userId} className="flex items-center gap-3">
            <span className={`
              w-6 h-6 rounded-full flex items-center justify-center text-xs font-bold
              ${index === 0 ? 'bg-yellow-100 text-yellow-600' :
                index === 1 ? 'bg-gray-100 text-gray-600' :
                index === 2 ? 'bg-orange-100 text-orange-600' :
                'bg-gray-50 text-gray-400'}
            `}>
              {entry.rank}
            </span>
            {entry.avatar ? (
              <img src={entry.avatar} alt={entry.name} className="w-8 h-8 rounded-full object-cover" />
            ) : (
              <div className="w-8 h-8 rounded-full bg-gray-200 flex items-center justify-center text-xs">
                {entry.name[0]}
              </div>
            )}
            <span className="flex-1 text-sm truncate">{entry.name}</span>
            <span className="text-sm font-medium text-gray-600">
              {entry.score >= 60 ? `${Math.floor(entry.score / 60)}h` : `${entry.score}分`}
            </span>
          </div>
        ))}
      </div>
    </div>
  );
};

export default Leaderboard;
