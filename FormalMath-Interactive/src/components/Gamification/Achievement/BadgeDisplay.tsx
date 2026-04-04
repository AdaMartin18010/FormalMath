/**
 * 徽章展示组件
 * 展示用户获得的徽章和成就
 */

import React, { useState } from 'react';
import { Award, Lock, Star, Sparkles, Trophy, Gem, Crown } from 'lucide-react';
import type { Badge, BadgeRarity, BadgeCategory, UserBadge } from '../../../types/gamification';

interface BadgeDisplayProps {
  allBadges: Badge[];
  userBadges: UserBadge[];
  onBadgeClick?: (badge: Badge) => void;
}

const rarityConfig: Record<BadgeRarity, { 
  color: string; 
  bg: string; 
  border: string;
  icon: React.ReactNode;
  label: string;
}> = {
  common: {
    color: 'text-gray-600',
    bg: 'bg-gray-100',
    border: 'border-gray-300',
    icon: <Award className="w-4 h-4" />,
    label: '普通',
  },
  uncommon: {
    color: 'text-green-600',
    bg: 'bg-green-100',
    border: 'border-green-300',
    icon: <Star className="w-4 h-4" />,
    label: '优秀',
  },
  rare: {
    color: 'text-blue-600',
    bg: 'bg-blue-100',
    border: 'border-blue-300',
    icon: <Gem className="w-4 h-4" />,
    label: '稀有',
  },
  epic: {
    color: 'text-purple-600',
    bg: 'bg-purple-100',
    border: 'border-purple-300',
    icon: <Sparkles className="w-4 h-4" />,
    label: '史诗',
  },
  legendary: {
    color: 'text-yellow-600',
    bg: 'bg-yellow-100',
    border: 'border-yellow-300',
    icon: <Crown className="w-4 h-4" />,
    label: '传说',
  },
};

const categoryLabels: Record<BadgeCategory, string> = {
  learning: '学习成就',
  puzzle: '解谜成就',
  battle: '对战成就',
  exploration: '探索成就',
  social: '社交成就',
  special: '特殊成就',
};

export const BadgeDisplay: React.FC<BadgeDisplayProps> = ({
  allBadges,
  userBadges,
  onBadgeClick,
}) => {
  const [selectedCategory, setSelectedCategory] = useState<BadgeCategory | 'all'>('all');
  const [selectedRarity, setSelectedRarity] = useState<BadgeRarity | 'all'>('all');

  const userBadgeIds = new Set(userBadges.map((ub) => ub.badgeId));

  // 筛选徽章
  const filteredBadges = allBadges.filter((badge) => {
    if (selectedCategory !== 'all' && badge.category !== selectedCategory) return false;
    if (selectedRarity !== 'all' && badge.rarity !== selectedRarity) return false;
    return true;
  });

  // 统计
  const stats = {
    total: allBadges.length,
    unlocked: userBadges.length,
    percentage: Math.round((userBadges.length / allBadges.length) * 100),
  };

  return (
    <div className="space-y-6">
      {/* 统计概览 */}
      <div className="grid grid-cols-3 gap-4">
        <div className="bg-gradient-to-br from-blue-500 to-blue-600 rounded-xl p-4 text-white">
          <div className="text-3xl font-bold">{stats.unlocked}</div>
          <div className="text-blue-100">已解锁徽章</div>
        </div>
        <div className="bg-gradient-to-br from-purple-500 to-purple-600 rounded-xl p-4 text-white">
          <div className="text-3xl font-bold">{stats.total}</div>
          <div className="text-purple-100">总徽章数</div>
        </div>
        <div className="bg-gradient-to-br from-green-500 to-green-600 rounded-xl p-4 text-white">
          <div className="text-3xl font-bold">{stats.percentage}%</div>
          <div className="text-green-100">完成度</div>
        </div>
      </div>

      {/* 筛选器 */}
      <div className="flex flex-wrap gap-3">
        <select
          value={selectedCategory}
          onChange={(e) => setSelectedCategory(e.target.value as BadgeCategory | 'all')}
          className="px-4 py-2 border rounded-lg focus:ring-2 focus:ring-blue-500"
        >
          <option value="all">全部分类</option>
          {Object.entries(categoryLabels).map(([key, label]) => (
            <option key={key} value={key}>{label}</option>
          ))}
        </select>

        <select
          value={selectedRarity}
          onChange={(e) => setSelectedRarity(e.target.value as BadgeRarity | 'all')}
          className="px-4 py-2 border rounded-lg focus:ring-2 focus:ring-blue-500"
        >
          <option value="all">全部稀有度</option>
          {Object.entries(rarityConfig).map(([key, config]) => (
            <option key={key} value={key}>{config.label}</option>
          ))}
        </select>
      </div>

      {/* 徽章网格 */}
      <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-4">
        {filteredBadges.map((badge) => {
          const isUnlocked = userBadgeIds.has(badge.id);
          const userBadge = userBadges.find((ub) => ub.badgeId === badge.id);
          const isNew = userBadge?.isNew;
          const rarity = rarityConfig[badge.rarity];

          return (
            <div
              key={badge.id}
              onClick={() => onBadgeClick?.(badge)}
              className={`
                relative p-4 rounded-xl border-2 transition-all duration-300 cursor-pointer
                ${isUnlocked
                  ? `${rarity.bg} ${rarity.border} hover:shadow-lg hover:scale-105`
                  : 'bg-gray-50 border-gray-200 opacity-60 grayscale'
                }
              `}
            >
              {/* 新徽章标记 */}
              {isNew && (
                <div className="absolute -top-2 -right-2 w-6 h-6 bg-red-500 text-white rounded-full flex items-center justify-center text-xs font-bold animate-pulse">
                  新
                </div>
              )}

              {/* 徽章图标 */}
              <div className="text-center mb-3">
                <div className={`
                  w-16 h-16 mx-auto rounded-full flex items-center justify-center text-3xl
                  ${isUnlocked ? 'bg-white shadow-md' : 'bg-gray-200'}
                `}>
                  {badge.icon}
                </div>
              </div>

              {/* 徽章信息 */}
              <div className="text-center">
                <h4 className={`font-bold text-sm mb-1 ${isUnlocked ? 'text-gray-900' : 'text-gray-500'}`}>
                  {badge.name}
                </h4>
                <p className="text-xs text-gray-500 line-clamp-2 mb-2">
                  {badge.description}
                </p>
                
                {/* 稀有度标签 */}
                <div className={`
                  inline-flex items-center gap-1 px-2 py-0.5 rounded-full text-xs
                  ${rarity.bg} ${rarity.color}
                `}>
                  {rarity.icon}
                  {rarity.label}
                </div>
              </div>

              {/* 锁定遮罩 */}
              {!isUnlocked && (
                <div className="absolute inset-0 flex items-center justify-center bg-gray-100/50 rounded-xl">
                  <Lock className="w-8 h-8 text-gray-400" />
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* 空状态 */}
      {filteredBadges.length === 0 && (
        <div className="text-center py-12 text-gray-500">
          <Trophy className="w-16 h-16 mx-auto mb-4 text-gray-300" />
          <p>没有找到符合条件的徽章</p>
        </div>
      )}
    </div>
  );
};

export default BadgeDisplay;
