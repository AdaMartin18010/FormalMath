// @ts-nocheck
/**
 * 游戏化主页面
 * 整合所有游戏模式的入口
 */

import React, { useEffect } from 'react';
import { useNavigate } from 'react-router-dom';
import { 
  Brain, 
  Swords, 
  Compass, 
  Award, 
  Bot,
  ChevronRight,
  Star,
  Trophy,
  Zap,
  Target
} from 'lucide-react';
import { useGameStore } from '../../stores/gameStore';
import { useAchievements, useTutor } from '../../hooks/game';
import { TutorWidget } from '../../components/Gamification';

export const GameHome: React.FC = () => {
  const navigate = useNavigate();
  const store = useGameStore();
  const { level, unlockedBadges, inProgressAchievements } = useAchievements();
  const tutor = useTutor();

  // 初始化
  useEffect(() => {
    store.initialize();
  }, []);

  const gameModes = [
    {
      id: 'puzzle',
      name: '解谜挑战',
      description: '挑战各种数学谜题，从逻辑推理到证明构造',
      icon: <Brain className="w-8 h-8" />,
      color: 'from-blue-500 to-blue-600',
      path: '/game/puzzle',
      stats: `${store.userGameData.stats.totalPuzzlesSolved} 已解决`,
    },
    {
      id: 'battle',
      name: '对战模式',
      description: '与其他玩家实时对战，一决高下',
      icon: <Swords className="w-8 h-8" />,
      color: 'from-red-500 to-red-600',
      path: '/game/battle',
      stats: `${store.userGameData.stats.totalBattlesWon} 胜 / ${store.userGameData.stats.totalBattlesPlayed} 场`,
    },
    {
      id: 'exploration',
      name: '数学世界',
      description: '探索数学历史，收集概念卡片',
      icon: <Compass className="w-8 h-8" />,
      color: 'from-green-500 to-green-600',
      path: '/game/exploration',
      stats: '探索中',
    },
    {
      id: 'achievements',
      name: '成就系统',
      description: '查看徽章、升级技能、冲击排行榜',
      icon: <Award className="w-8 h-8" />,
      color: 'from-purple-500 to-purple-600',
      path: '/game/achievements',
      stats: `${unlockedBadges.length} 徽章解锁`,
    },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部欢迎区 */}
      <div className="bg-gradient-to-br from-indigo-600 via-purple-600 to-pink-600 text-white">
        <div className="max-w-6xl mx-auto px-4 py-12">
          <div className="flex items-center justify-between">
            <div>
              <h1 className="text-4xl font-bold mb-3">
                欢迎回来，数学探索者！
              </h1>
              <p className="text-indigo-100 text-lg">
                今天想挑战什么？继续你的数学冒险之旅吧！
              </p>
            </div>
            <div className="flex items-center gap-6">
              <div className="text-center">
                <div className="w-16 h-16 bg-white/20 rounded-2xl flex items-center justify-center text-3xl mb-2">
                  {level.levelIcon}
                </div>
                <div className="font-bold">Lv.{level.currentLevel}</div>
                <div className="text-sm text-indigo-200">{level.levelTitle}</div>
              </div>
            </div>
          </div>

          {/* 快捷统计 */}
          <div className="grid grid-cols-4 gap-4 mt-8">
            <div className="bg-white/10 backdrop-blur-sm rounded-xl p-4">
              <div className="flex items-center gap-2 text-indigo-200 mb-1">
                <Star className="w-4 h-4" />
                <span className="text-sm">总经验</span>
              </div>
              <div className="text-2xl font-bold">{level.totalXP.toLocaleString()}</div>
            </div>
            <div className="bg-white/10 backdrop-blur-sm rounded-xl p-4">
              <div className="flex items-center gap-2 text-indigo-200 mb-1">
                <Trophy className="w-4 h-4" />
                <span className="text-sm">徽章</span>
              </div>
              <div className="text-2xl font-bold">{unlockedBadges.length}</div>
            </div>
            <div className="bg-white/10 backdrop-blur-sm rounded-xl p-4">
              <div className="flex items-center gap-2 text-indigo-200 mb-1">
                <Zap className="w-4 h-4" />
                <span className="text-sm">连胜</span>
              </div>
              <div className="text-2xl font-bold">{store.userGameData.stats.currentStreak}</div>
            </div>
            <div className="bg-white/10 backdrop-blur-sm rounded-xl p-4">
              <div className="flex items-center gap-2 text-indigo-200 mb-1">
                <Target className="w-4 h-4" />
                <span className="text-sm">准确率</span>
              </div>
              <div className="text-2xl font-bold">
                {store.userGameData.stats.totalPuzzlesSolved > 0
                  ? Math.round(
                      (store.userGameData.stats.totalPuzzlesSolved /
                        (store.userGameData.stats.totalPuzzlesSolved +
                          store.userGameData.stats.puzzleSolveStreak)) *
                        100
                    )
                  : 0}
                %
              </div>
            </div>
          </div>
        </div>
      </div>

      {/* 主内容区 */}
      <div className="max-w-6xl mx-auto px-4 py-12">
        {/* 游戏模式卡片 */}
        <h2 className="text-2xl font-bold text-gray-900 mb-6">选择游戏模式</h2>
        <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
          {gameModes.map((mode) => (
            <button
              key={mode.id}
              onClick={() => navigate(mode.path)}
              className="group relative bg-white rounded-2xl p-6 shadow-sm hover:shadow-xl transition-all duration-300 text-left overflow-hidden"
            >
              {/* 背景渐变装饰 */}
              <div className={`absolute top-0 right-0 w-32 h-32 bg-gradient-to-br ${mode.color} opacity-10 rounded-bl-full group-hover:opacity-20 transition-opacity`} />
              
              <div className="relative flex items-start gap-4">
                <div className={`p-4 rounded-xl bg-gradient-to-br ${mode.color} text-white shadow-lg`}>
                  {mode.icon}
                </div>
                <div className="flex-1">
                  <h3 className="text-xl font-bold text-gray-900 mb-1 group-hover:text-indigo-600 transition-colors">
                    {mode.name}
                  </h3>
                  <p className="text-gray-500 mb-3">{mode.description}</p>
                  <div className="flex items-center justify-between">
                    <span className="text-sm font-medium text-indigo-600 bg-indigo-50 px-3 py-1 rounded-full">
                      {mode.stats}
                    </span>
                    <ChevronRight className="w-5 h-5 text-gray-400 group-hover:text-indigo-600 group-hover:translate-x-1 transition-all" />
                  </div>
                </div>
              </div>
            </button>
          ))}
        </div>

        {/* 待完成成就 */}
        {inProgressAchievements.length > 0 && (
          <div className="mt-12">
            <h2 className="text-2xl font-bold text-gray-900 mb-6">正在进行的挑战</h2>
            <div className="space-y-4">
              {inProgressAchievements.slice(0, 3).map((achievement) => (
                <div
                  key={achievement.id}
                  className="bg-white rounded-xl p-4 shadow-sm flex items-center gap-4"
                >
                  <div className="w-12 h-12 bg-yellow-100 rounded-xl flex items-center justify-center">
                    <Target className="w-6 h-6 text-yellow-600" />
                  </div>
                  <div className="flex-1">
                    <h4 className="font-bold text-gray-900">{achievement.title}</h4>
                    <p className="text-sm text-gray-500">{achievement.description}</p>
                    <div className="mt-2 bg-gray-100 rounded-full h-2 overflow-hidden">
                      <div
                        className="bg-gradient-to-r from-yellow-400 to-orange-500 h-full rounded-full transition-all"
                        style={{
                          width: `${(achievement.currentValue / achievement.targetValue) * 100}%`,
                        }}
                      />
                    </div>
                  </div>
                  <div className="text-right">
                    <div className="text-2xl font-bold text-gray-900">
                      {Math.round((achievement.currentValue / achievement.targetValue) * 100)}%
                    </div>
                    <div className="text-sm text-gray-500">
                      {achievement.currentValue}/{achievement.targetValue}
                    </div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* 每日推荐 */}
        <div className="mt-12 bg-gradient-to-r from-indigo-500 to-purple-600 rounded-2xl p-6 text-white">
          <div className="flex items-center gap-3 mb-4">
            <Bot className="w-6 h-6" />
            <h2 className="text-xl font-bold">今日推荐</h2>
          </div>
          <p className="text-indigo-100 mb-4">
            基于你的学习进度，我们推荐你尝试"证明构造"类型的谜题。
            你已经掌握了基础概念，现在是时候挑战更高难度的证明了！
          </p>
          <button
            onClick={() => navigate('/game/puzzle')}
            className="bg-white text-indigo-600 px-6 py-2 rounded-xl font-medium hover:bg-indigo-50 transition-colors"
          >
            开始挑战
          </button>
        </div>
      </div>

      {/* 虚拟导师 */}
      <TutorWidget
        isEnabled={tutor.isEnabled}
        personality={tutor.personality}
        messages={tutor.messages}
        onToggle={tutor.toggleTutor}
        onSetPersonality={tutor.setPersonality}
        onGetHint={tutor.getHint}
        onGetExplanation={tutor.getExplanation}
        onGetMotivation={tutor.getMotivation}
        onAskQuestion={tutor.askQuestion}
        onClearMessages={tutor.clearMessages}
      />
    </div>
  );
};

export default GameHome;
