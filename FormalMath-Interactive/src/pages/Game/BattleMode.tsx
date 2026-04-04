/**
 * 对战模式页面
 * 实时解题对战和知识问答PK
 */

import React, { useState, useEffect } from 'react';
import { Swords, Users, Clock, Trophy, Zap, Target, ChevronRight, User } from 'lucide-react';
import { useBattle, useAchievements } from '../../hooks/game';
import type { BattleType } from '../../types/gamification';

export const BattleMode: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'lobby' | 'create' | 'active'>('lobby');
  const [selectedType, setSelectedType] = useState<BattleType>('speed_challenge');
  const [waitingForOpponent, setWaitingForOpponent] = useState(false);

  const {
    battle,
    isWaiting,
    isPlaying,
    isFinished,
    currentRound,
    totalRounds,
    timeLeft,
    player,
    opponent,
    scores,
    winner,
    createBattle,
    joinBattle,
    leaveBattle,
    setReady,
    submitAnswer,
    availableBattles,
  } = useBattle({
    onBattleStart: () => console.log('Battle started!'),
    onBattleEnd: (result) => console.log('Battle ended:', result),
  });

  const { level } = useAchievements();

  const battleTypes = [
    {
      id: 'speed_challenge' as BattleType,
      name: '速度挑战',
      description: '限时答题，答对越多得分越高',
      icon: <Zap className="w-6 h-6" />,
      color: 'from-yellow-400 to-orange-500',
    },
    {
      id: 'proof_race' as BattleType,
      name: '证明竞速',
      description: '抢先完成数学证明',
      icon: <Target className="w-6 h-6" />,
      color: 'from-blue-400 to-indigo-500',
    },
    {
      id: 'quiz_duel' as BattleType,
      name: '知识问答',
      description: '多轮知识PK，争夺冠军',
      icon: <Trophy className="w-6 h-6" />,
      color: 'from-purple-400 to-pink-500',
    },
  ];

  // 创建对战
  const handleCreateBattle = async () => {
    await createBattle(selectedType, {
      difficulty: 'medium',
      timePerQuestion: 30,
      questionCount: 5,
      allowHelpers: false,
      isPrivate: false,
    });
    setActiveTab('active');
    setWaitingForOpponent(true);
  };

  // 快速匹配
  const handleQuickMatch = async () => {
    setWaitingForOpponent(true);
    // 模拟匹配
    setTimeout(() => {
      joinBattle('battle_001');
      setActiveTab('active');
      setWaitingForOpponent(false);
    }, 2000);
  };

  // 离开对战
  const handleLeave = () => {
    leaveBattle();
    setActiveTab('lobby');
    setWaitingForOpponent(false);
  };

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部 */}
      <div className="bg-gradient-to-r from-red-600 to-orange-600 text-white">
        <div className="max-w-6xl mx-auto px-4 py-8">
          <h1 className="text-3xl font-bold mb-2">对战模式</h1>
          <p className="text-red-100">与其他玩家一决高下，展示你的数学实力</p>
        </div>
      </div>

      {/* 主内容 */}
      <div className="max-w-6xl mx-auto px-4 py-8">
        {activeTab === 'lobby' && (
          <>
            {/* 快速操作 */}
            <div className="grid grid-cols-1 md:grid-cols-2 gap-6 mb-8">
              <button
                onClick={handleQuickMatch}
                className="bg-gradient-to-r from-red-500 to-orange-500 text-white rounded-2xl p-6 text-left hover:shadow-lg transition-shadow"
              >
                <div className="flex items-center justify-between mb-4">
                  <Zap className="w-10 h-10" />
                  <ChevronRight className="w-6 h-6" />
                </div>
                <h3 className="text-xl font-bold mb-1">快速匹配</h3>
                <p className="text-red-100">立即寻找对手开始对战</p>
              </button>

              <button
                onClick={() => setActiveTab('create')}
                className="bg-white rounded-2xl p-6 text-left hover:shadow-lg transition-shadow border-2 border-gray-100"
              >
                <div className="flex items-center justify-between mb-4">
                  <Swords className="w-10 h-10 text-red-500" />
                  <ChevronRight className="w-6 h-6 text-gray-400" />
                </div>
                <h3 className="text-xl font-bold text-gray-900 mb-1">创建房间</h3>
                <p className="text-gray-500">自定义对战设置，邀请好友</p>
              </button>
            </div>

            {/* 对战类型介绍 */}
            <h2 className="text-xl font-bold text-gray-900 mb-4">对战模式</h2>
            <div className="grid grid-cols-1 md:grid-cols-3 gap-6 mb-8">
              {battleTypes.map((type) => (
                <div
                  key={type.id}
                  className="bg-white rounded-2xl p-6 shadow-sm hover:shadow-md transition-shadow"
                >
                  <div className={`w-14 h-14 rounded-xl bg-gradient-to-br ${type.color} flex items-center justify-center text-white mb-4`}>
                    {type.icon}
                  </div>
                  <h3 className="text-lg font-bold text-gray-900 mb-2">{type.name}</h3>
                  <p className="text-gray-500 text-sm">{type.description}</p>
                </div>
              ))}
            </div>

            {/* 可用房间 */}
            <h2 className="text-xl font-bold text-gray-900 mb-4">可用房间</h2>
            <div className="bg-white rounded-2xl shadow-sm overflow-hidden">
              {availableBattles.length > 0 ? (
                availableBattles.map((battle) => (
                  <div
                    key={battle.id}
                    className="flex items-center justify-between p-4 border-b hover:bg-gray-50"
                  >
                    <div className="flex items-center gap-4">
                      <div className="w-10 h-10 bg-red-100 rounded-full flex items-center justify-center">
                        <User className="w-5 h-5 text-red-600" />
                      </div>
                      <div>
                        <div className="font-medium text-gray-900">
                          {battle.host.name}的房间
                        </div>
                        <div className="text-sm text-gray-500">
                          {battle.settings.questionCount}题 • {battle.settings.timePerQuestion}秒/题
                        </div>
                      </div>
                    </div>
                    <button
                      onClick={() => joinBattle(battle.id)}
                      className="px-4 py-2 bg-red-600 text-white rounded-lg hover:bg-red-700"
                    >
                      加入
                    </button>
                  </div>
                ))
              ) : (
                <div className="p-8 text-center text-gray-500">
                  <Users className="w-12 h-12 mx-auto mb-3 text-gray-300" />
                  <p>暂无可用房间</p>
                  <p className="text-sm">创建一个新房间或快速匹配</p>
                </div>
              )}
            </div>
          </>
        )}

        {activeTab === 'create' && (
          <div className="max-w-md mx-auto bg-white rounded-2xl shadow-sm p-6">
            <h2 className="text-xl font-bold text-gray-900 mb-6">创建对战房间</h2>

            {/* 对战类型 */}
            <div className="space-y-3 mb-6">
              <label className="block text-sm font-medium text-gray-700">选择模式</label>
              {battleTypes.map((type) => (
                <button
                  key={type.id}
                  onClick={() => setSelectedType(type.id)}
                  className={`
                    w-full flex items-center gap-4 p-4 rounded-xl border-2 transition-all
                    ${selectedType === type.id
                      ? 'border-red-500 bg-red-50'
                      : 'border-gray-200 hover:border-red-300'
                    }
                  `}
                >
                  <div className={`p-2 rounded-lg bg-gradient-to-br ${type.color} text-white`}>
                    {type.icon}
                  </div>
                  <div className="text-left">
                    <div className="font-medium text-gray-900">{type.name}</div>
                    <div className="text-sm text-gray-500">{type.description}</div>
                  </div>
                </button>
              ))}
            </div>

            {/* 设置选项 */}
            <div className="space-y-4 mb-6">
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-1">
                  题目数量
                </label>
                <select className="w-full px-4 py-2 border rounded-lg">
                  <option>3 题</option>
                  <option selected>5 题</option>
                  <option>10 题</option>
                </select>
              </div>
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-1">
                  每题时间限制
                </label>
                <select className="w-full px-4 py-2 border rounded-lg">
                  <option>15 秒</option>
                  <option selected>30 秒</option>
                  <option>60 秒</option>
                </select>
              </div>
            </div>

            {/* 按钮 */}
            <div className="flex gap-3">
              <button
                onClick={() => setActiveTab('lobby')}
                className="flex-1 px-4 py-3 border rounded-xl hover:bg-gray-50"
              >
                返回
              </button>
              <button
                onClick={handleCreateBattle}
                className="flex-1 px-4 py-3 bg-red-600 text-white rounded-xl hover:bg-red-700"
              >
                创建房间
              </button>
            </div>
          </div>
        )}

        {activeTab === 'active' && battle && (
          <div className="max-w-3xl mx-auto">
            {/* 等待对手 */}
            {waitingForOpponent && (
              <div className="bg-white rounded-2xl shadow-sm p-12 text-center">
                <div className="w-20 h-20 bg-red-100 rounded-full flex items-center justify-center mx-auto mb-4 animate-pulse">
                  <Users className="w-10 h-10 text-red-600" />
                </div>
                <h2 className="text-2xl font-bold text-gray-900 mb-2">等待对手...</h2>
                <p className="text-gray-500 mb-6">正在为你匹配实力相近的对手</p>
                <button
                  onClick={handleLeave}
                  className="px-6 py-2 border rounded-lg hover:bg-gray-50"
                >
                  取消匹配
                </button>
              </div>
            )}

            {/* 对战界面 */}
            {!waitingForOpponent && (
              <>
                {/* 对战头部 */}
                <div className="bg-white rounded-2xl shadow-sm p-6 mb-6">
                  <div className="flex items-center justify-between">
                    {/* 玩家1 */}
                    <div className="text-center">
                      <div className="w-16 h-16 bg-blue-100 rounded-full flex items-center justify-center mx-auto mb-2">
                        <User className="w-8 h-8 text-blue-600" />
                      </div>
                      <div className="font-bold text-gray-900">{player?.name || '你'}</div>
                      <div className="text-sm text-gray-500">Lv.{player?.level || level.currentLevel}</div>
                      {player?.ready && (
                        <span className="text-xs text-green-600 bg-green-100 px-2 py-0.5 rounded-full">
                          已准备
                        </span>
                      )}
                    </div>

                    {/* 中间信息 */}
                    <div className="text-center">
                      <div className="text-3xl font-bold text-gray-400">VS</div>
                      <div className="text-sm text-gray-500 mt-2">
                        第 {currentRound}/{totalRounds} 轮
                      </div>
                      {isPlaying && (
                        <div className="mt-4 w-24 h-24 rounded-full border-4 border-red-500 flex items-center justify-center">
                          <span className="text-2xl font-bold text-red-500">{timeLeft}</span>
                        </div>
                      )}
                    </div>

                    {/* 玩家2 */}
                    <div className="text-center">
                      {opponent ? (
                        <>
                          <div className="w-16 h-16 bg-red-100 rounded-full flex items-center justify-center mx-auto mb-2">
                            <User className="w-8 h-8 text-red-600" />
                          </div>
                          <div className="font-bold text-gray-900">{opponent.name}</div>
                          <div className="text-sm text-gray-500">Lv.{opponent.level}</div>
                          {opponent.ready && (
                            <span className="text-xs text-green-600 bg-green-100 px-2 py-0.5 rounded-full">
                              已准备
                            </span>
                          )}
                        </>
                      ) : (
                        <>
                          <div className="w-16 h-16 bg-gray-100 rounded-full flex items-center justify-center mx-auto mb-2">
                            <Clock className="w-8 h-8 text-gray-400 animate-pulse" />
                          </div>
                          <div className="text-gray-400">等待加入...</div>
                        </>
                      )}
                    </div>
                  </div>

                  {/* 准备按钮 */}
                  {!isPlaying && !isFinished && (
                    <div className="mt-6 text-center">
                      <button
                        onClick={() => setReady(!player?.ready)}
                        className={`px-8 py-3 rounded-xl font-medium transition-colors
                          ${player?.ready
                            ? 'bg-green-100 text-green-700'
                            : 'bg-red-600 text-white hover:bg-red-700'
                          }
                        `}
                      >
                        {player?.ready ? '已准备' : '准备'}
                      </button>
                    </div>
                  )}
                </div>

                {/* 答题区域 */}
                {isPlaying && (
                  <div className="bg-white rounded-2xl shadow-sm p-6">
                    <div className="text-center mb-6">
                      <h3 className="text-xl font-bold text-gray-900 mb-2">题目内容</h3>
                      <p className="text-gray-600">这里显示具体的题目...</p>
                    </div>

                    <div className="grid grid-cols-2 gap-4">
                      {['A', 'B', 'C', 'D'].map((option) => (
                        <button
                          key={option}
                          onClick={() => submitAnswer(option)}
                          className="p-4 border-2 border-gray-200 rounded-xl hover:border-red-300 hover:bg-red-50 transition-colors text-left"
                        >
                          <span className="font-bold text-red-600 mr-2">{option}.</span>
                          <span className="text-gray-700">选项内容</span>
                        </button>
                      ))}
                    </div>
                  </div>
                )}

                {/* 对战结果 */}
                {isFinished && winner && (
                  <div className="bg-white rounded-2xl shadow-sm p-8 text-center">
                    <div className={`w-24 h-24 rounded-full flex items-center justify-center mx-auto mb-4
                      ${winner === player?.userId ? 'bg-green-100' : 'bg-red-100'}
                    `}>
                      <Trophy className={`w-12 h-12
                        ${winner === player?.userId ? 'text-green-600' : 'text-red-600'}
                      `} />
                    </div>
                    <h2 className="text-2xl font-bold text-gray-900 mb-2">
                      {winner === player?.userId ? '你赢了！' : '你输了'}
                    </h2>
                    <p className="text-gray-500 mb-6">
                      最终比分: {scores[player?.userId || '']} - {scores[opponent?.userId || '']}
                    </p>
                    <div className="flex gap-3 justify-center">
                      <button
                        onClick={handleLeave}
                        className="px-6 py-3 border rounded-xl hover:bg-gray-50"
                      >
                        返回大厅
                      </button>
                      <button
                        onClick={() => {
                          handleLeave();
                          handleQuickMatch();
                        }}
                        className="px-6 py-3 bg-red-600 text-white rounded-xl hover:bg-red-700"
                      >
                        再来一局
                      </button>
                    </div>
                  </div>
                )}

                {/* 离开按钮 */}
                {!isFinished && (
                  <div className="mt-6 text-center">
                    <button
                      onClick={handleLeave}
                      className="text-gray-500 hover:text-gray-700"
                    >
                      退出对战
                    </button>
                  </div>
                )}
              </>
            )}
          </div>
        )}
      </div>
    </div>
  );
};

export default BattleMode;
