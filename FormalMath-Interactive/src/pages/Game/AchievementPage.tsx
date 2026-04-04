/**
 * 成就系统页面
 * 展示徽章、成就、技能树和排行榜
 */

import React, { useState } from 'react';
import { Award, Trophy, Target, TrendingUp, Star, Zap, Crown } from 'lucide-react';
import { useAchievements } from '../../hooks/game';
import { BadgeDisplay, SkillTree as SkillTreeComponent } from '../../components/Gamification';

export const AchievementPage: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'badges' | 'skills' | 'leaderboard'>('badges');

  const {
    level,
    progressToNextLevel,
    allBadges,
    userBadges,
    skillTree,
    unlockedSkills,
    leaderboard,
    unlockSkill,
    upgradeSkill,
    addXP,
  } = useAchievements();

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部 */}
      <div className="bg-gradient-to-r from-purple-600 to-pink-600 text-white">
        <div className="max-w-6xl mx-auto px-4 py-8">
          <h1 className="text-3xl font-bold mb-6">成就与成长</h1>
          
          {/* 等级信息 */}
          <div className="bg-white/10 rounded-2xl p-6 backdrop-blur-sm">
            <div className="flex items-center gap-6">
              <div className="w-20 h-20 bg-white/20 rounded-2xl flex items-center justify-center text-4xl">
                {level.levelIcon}
              </div>
              <div className="flex-1">
                <div className="flex items-center gap-3 mb-2">
                  <span className="text-3xl font-bold">Lv.{level.currentLevel}</span>
                  <span className="text-xl text-purple-100">{level.levelTitle}</span>
                </div>
                <div className="flex items-center gap-4 text-sm text-purple-100">
                  <span>总经验: {level.totalXP.toLocaleString()}</span>
                  <span>升级还需: {level.xpToNextLevel.toLocaleString()} XP</span>
                </div>
                {/* 经验条 */}
                <div className="mt-3 bg-white/20 rounded-full h-3 overflow-hidden">
                  <div
                    className="bg-white h-full rounded-full transition-all duration-500"
                    style={{ width: `${progressToNextLevel}%` }}
                  />
                </div>
              </div>
            </div>
          </div>
        </div>
      </div>

      {/* 主内容 */}
      <div className="max-w-6xl mx-auto px-4 py-8">
        {/* 标签切换 */}
        <div className="flex gap-4 mb-8">
          <button
            onClick={() => setActiveTab('badges')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'badges'
                ? 'bg-purple-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <Award className="w-5 h-5" />
            徽章成就
          </button>
          <button
            onClick={() => setActiveTab('skills')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'skills'
                ? 'bg-purple-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <Zap className="w-5 h-5" />
            技能树
          </button>
          <button
            onClick={() => setActiveTab('leaderboard')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'leaderboard'
                ? 'bg-purple-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <TrendingUp className="w-5 h-5" />
            排行榜
          </button>
        </div>

        {/* 徽章成就 */}
        {activeTab === 'badges' && (
          <BadgeDisplay
            allBadges={allBadges}
            userBadges={userBadges}
            onBadgeClick={(badge) => console.log('Badge clicked:', badge)}
          />
        )}

        {/* 技能树 */}
        {activeTab === 'skills' && skillTree && (
          <SkillTreeComponent
            skillTree={skillTree}
            unlockedSkills={unlockedSkills}
            userXP={level.currentXP}
            onUnlockSkill={unlockSkill}
            onUpgradeSkill={upgradeSkill}
          />
        )}

        {/* 排行榜 */}
        {activeTab === 'leaderboard' && leaderboard && (
          <div className="bg-white rounded-2xl shadow-sm overflow-hidden">
            <div className="p-6 border-b">
              <h2 className="text-xl font-bold flex items-center gap-2">
                <Trophy className="w-6 h-6 text-yellow-500" />
                {leaderboard.name}
              </h2>
            </div>
            <div className="divide-y">
              {leaderboard.entries.map((entry) => (
                <div
                  key={entry.userId}
                  className={`
                    flex items-center justify-between p-4
                    ${entry.isCurrentUser ? 'bg-purple-50' : ''}
                  `}
                >
                  <div className="flex items-center gap-4">
                    <div className={`
                      w-10 h-10 rounded-full flex items-center justify-center font-bold
                      ${entry.rank === 1 ? 'bg-yellow-100 text-yellow-700' :
                        entry.rank === 2 ? 'bg-gray-100 text-gray-700' :
                        entry.rank === 3 ? 'bg-orange-100 text-orange-700' :
                        'bg-gray-50 text-gray-500'}
                    `}>
                      {entry.rank}
                    </div>
                    <div>
                      <div className="font-medium text-gray-900">
                        {entry.name}
                        {entry.isCurrentUser && (
                          <span className="ml-2 text-xs bg-purple-100 text-purple-700 px-2 py-0.5 rounded-full">
                            你
                          </span>
                        )}
                      </div>
                      <div className="text-sm text-gray-500">等级 {entry.level}</div>
                    </div>
                  </div>
                  <div className="text-right">
                    <div className="font-bold text-lg">{entry.score.toLocaleString()}</div>
                    <div className="flex items-center gap-1 text-sm">
                      {entry.trend === 'up' && <TrendingUp className="w-4 h-4 text-green-500" />}
                      {entry.trend === 'down' && <TrendingUp className="w-4 h-4 text-red-500 rotate-180" />}
                      {entry.trend === 'stable' && <Target className="w-4 h-4 text-gray-400" />}
                    </div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default AchievementPage;
