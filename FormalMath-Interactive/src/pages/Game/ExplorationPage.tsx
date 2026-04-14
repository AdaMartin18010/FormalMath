// @ts-nocheck
/**
 * 探索模式页面
 * 数学世界探索和历史时间线
 */

import React, { useState } from 'react';
import { Compass, Map, Clock, BookOpen, Lock, Check, Star, ChevronRight } from 'lucide-react';
import { useExploration } from '../../hooks/game';

export const ExplorationPage: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'worlds' | 'timeline' | 'collection'>('worlds');
  
  const {
    worlds,
    currentWorld,
    timeline,
    collection,
    collectedCount,
    totalCollectibles,
    isExploring,
    explorationProgress,
    startExploration,
    endExploration,
    exploreNode,
  } = useExploration();

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部 */}
      <div className="bg-gradient-to-r from-green-600 to-teal-600 text-white">
        <div className="max-w-6xl mx-auto px-4 py-8">
          <h1 className="text-3xl font-bold mb-2">数学世界</h1>
          <p className="text-green-100">探索数学的历史长河，收集珍贵的概念卡片</p>
        </div>
      </div>

      {/* 主内容 */}
      <div className="max-w-6xl mx-auto px-4 py-8">
        {/* 标签切换 */}
        <div className="flex gap-4 mb-8">
          <button
            onClick={() => setActiveTab('worlds')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'worlds'
                ? 'bg-green-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <Map className="w-5 h-5" />
            世界探索
          </button>
          <button
            onClick={() => setActiveTab('timeline')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'timeline'
                ? 'bg-green-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <Clock className="w-5 h-5" />
            历史时间线
          </button>
          <button
            onClick={() => setActiveTab('collection')}
            className={`flex items-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'collection'
                ? 'bg-green-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <BookOpen className="w-5 h-5" />
            概念收集
            <span className="bg-white/20 px-2 py-0.5 rounded-full text-sm">
              {collectedCount}/{totalCollectibles}
            </span>
          </button>
        </div>

        {/* 世界探索 */}
        {activeTab === 'worlds' && (
          <div className="space-y-6">
            {isExploring && currentWorld ? (
              <div className="bg-white rounded-2xl shadow-sm overflow-hidden">
                <div className="p-6 border-b">
                  <div className="flex items-center justify-between">
                    <div>
                      <h2 className="text-2xl font-bold text-gray-900">{currentWorld.name}</h2>
                      <p className="text-gray-500">{currentWorld.description}</p>
                    </div>
                    <button
                      onClick={endExploration}
                      className="px-4 py-2 border rounded-lg hover:bg-gray-50"
                    >
                      结束探索
                    </button>
                  </div>
                  
                  {/* 进度条 */}
                  <div className="mt-4">
                    <div className="flex items-center justify-between text-sm text-gray-500 mb-2">
                      <span>探索进度</span>
                      <span>{explorationProgress.completionRate}%</span>
                    </div>
                    <div className="bg-gray-100 rounded-full h-3 overflow-hidden">
                      <div
                        className="bg-green-500 h-full rounded-full transition-all"
                        style={{ width: `${explorationProgress.completionRate}%` }}
                      />
                    </div>
                  </div>
                </div>

                {/* 地图区域 */}
                <div className="p-6 min-h-[400px] relative bg-gradient-to-br from-green-50 to-blue-50">
                  {currentWorld.regions.map((region, index) => (
                    <button
                      key={region.id}
                      onClick={() => exploreNode(region.id)}
                      className={`
                        absolute w-32 h-32 rounded-2xl flex flex-col items-center justify-center transition-all
                        ${region.isVisited
                          ? 'bg-green-500 text-white shadow-lg'
                          : region.isLocked
                            ? 'bg-gray-300 text-gray-500 cursor-not-allowed'
                            : 'bg-white text-gray-700 hover:shadow-xl hover:scale-105 cursor-pointer'
                        }
                      `}
                      style={{
                        left: `${region.position.x}px`,
                        top: `${region.position.y}px`,
                      }}
                    >
                      {region.isVisited ? (
                        <Check className="w-8 h-8 mb-2" />
                      ) : region.isLocked ? (
                        <Lock className="w-8 h-8 mb-2" />
                      ) : (
                        <Compass className="w-8 h-8 mb-2" />
                      )}
                      <span className="text-sm font-medium text-center px-2">{region.name}</span>
                    </button>
                  ))}

                  {/* 连接线（简化版） */}
                  <svg className="absolute inset-0 w-full h-full pointer-events-none">
                    {currentWorld.connections.map((conn, i) => {
                      const from = currentWorld.regions.find((r) => r.id === conn.from);
                      const to = currentWorld.regions.find((r) => r.id === conn.to);
                      if (!from || !to) return null;
                      return (
                        <line
                          key={i}
                          x1={from.position.x + 64}
                          y1={from.position.y + 64}
                          x2={to.position.x + 64}
                          y2={to.position.y + 64}
                          stroke="#CBD5E1"
                          strokeWidth="2"
                          strokeDasharray="5,5"
                        />
                      );
                    })}
                  </svg>
                </div>
              </div>
            ) : (
              <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
                {worlds.map((world) => (
                  <div
                    key={world.id}
                    className="bg-white rounded-2xl p-6 shadow-sm hover:shadow-lg transition-shadow"
                  >
                    <div className="flex items-start gap-4 mb-4">
                      <div className="w-16 h-16 rounded-xl bg-gradient-to-br from-green-400 to-teal-500 flex items-center justify-center text-3xl">
                        🌍
                      </div>
                      <div className="flex-1">
                        <h3 className="text-xl font-bold text-gray-900">{world.name}</h3>
                        <p className="text-gray-500">{world.description}</p>
                      </div>
                    </div>
                    
                    <div className="flex items-center gap-4 text-sm text-gray-500 mb-4">
                      <span>{world.regions.length} 个区域</span>
                      <span>•</span>
                      <span>{world.completionRewards.length} 种奖励</span>
                    </div>

                    <button
                      onClick={() => startExploration('world', world.id)}
                      className="w-full py-3 bg-green-600 text-white rounded-xl font-medium hover:bg-green-700 transition-colors"
                    >
                      开始探索
                    </button>
                  </div>
                ))}

                {/* 更多世界预告 */}
                <div className="bg-gray-100 rounded-2xl p-6 border-2 border-dashed border-gray-300 flex flex-col items-center justify-center text-gray-500 min-h-[200px]">
                  <Lock className="w-12 h-12 mb-3" />
                  <p>更多数学世界即将解锁</p>
                  <p className="text-sm">继续提升等级以解锁新区域</p>
                </div>
              </div>
            )}
          </div>
        )}

        {/* 历史时间线 */}
        {activeTab === 'timeline' && timeline && (
          <div className="bg-white rounded-2xl shadow-sm p-6">
            <h2 className="text-xl font-bold mb-6">{timeline.name}</h2>
            
            <div className="relative">
              {/* 时间线轴线 */}
              <div className="absolute left-8 top-0 bottom-0 w-1 bg-gray-200" />

              {/* 时代 */}
              <div className="space-y-8">
                {timeline.eras.map((era) => (
                  <div key={era.id}>
                    {/* 时代标题 */}
                    <div
                      className="flex items-center gap-4 mb-4"
                      style={{ backgroundColor: `${era.color}20` }}
                    >
                      <div
                        className="w-16 h-16 rounded-full flex items-center justify-center text-white font-bold z-10"
                        style={{ backgroundColor: era.color }}
                      >
                        {era.period.start < 0 ? `${Math.abs(era.period.start)}BC` : `${era.period.start}AD`}
                      </div>
                      <div>
                        <h3 className="text-lg font-bold" style={{ color: era.color }}>
                          {era.name}
                        </h3>
                        <p className="text-sm text-gray-500">{era.description}</p>
                      </div>
                    </div>

                    {/* 事件 */}
                    <div className="ml-16 space-y-4">
                      {timeline.events
                        .filter((e) => e.eraId === era.id)
                        .map((event) => (
                          <div
                            key={event.id}
                            className={`
                              p-4 rounded-xl border-2 transition-all cursor-pointer
                              ${event.isVisited
                                ? 'bg-green-50 border-green-300'
                                : 'bg-white border-gray-200 hover:border-green-300'
                              }
                            `}
                          >
                            <div className="flex items-start justify-between">
                              <div>
                                <h4 className="font-bold text-gray-900">{event.title}</h4>
                                <p className="text-sm text-gray-500">{event.description}</p>
                                <div className="flex items-center gap-2 mt-2 text-xs text-gray-400">
                                  <Clock className="w-3 h-3" />
                                  {Math.abs(event.date)} {event.date < 0 ? 'BC' : 'AD'}
                                </div>
                              </div>
                              {event.isVisited && (
                                <Check className="w-5 h-5 text-green-500" />
                              )}
                            </div>
                          </div>
                        ))}
                    </div>
                  </div>
                ))}
              </div>
            </div>
          </div>
        )}

        {/* 概念收集 */}
        {activeTab === 'collection' && (
          <div>
            {/* 收集统计 */}
            <div className="grid grid-cols-5 gap-4 mb-8">
              {['common', 'uncommon', 'rare', 'epic', 'legendary'].map((rarity) => {
                const count = collection.filter(
                  (item) => item.rarity === rarity && item.isUnlocked
                ).length;
                const total = collection.filter((item) => item.rarity === rarity).length;
                const colors: Record<string, string> = {
                  common: 'from-gray-400 to-gray-500',
                  uncommon: 'from-green-400 to-green-500',
                  rare: 'from-blue-400 to-blue-500',
                  epic: 'from-purple-400 to-purple-500',
                  legendary: 'from-yellow-400 to-yellow-500',
                };
                return (
                  <div
                    key={rarity}
                    className={`bg-gradient-to-br ${colors[rarity]} rounded-xl p-4 text-white text-center`}
                  >
                    <div className="text-2xl font-bold">{count}/{total}</div>
                    <div className="text-sm opacity-80 capitalize">{rarity}</div>
                  </div>
                );
              })}
            </div>

            {/* 收集卡片 */}
            <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-6">
              {collection.map((item) => (
                <div
                  key={item.id}
                  className={`
                    bg-white rounded-2xl p-4 shadow-sm transition-all
                    ${item.isUnlocked ? '' : 'opacity-50 grayscale'}
                  `}
                >
                  <div className="aspect-square bg-gradient-to-br from-indigo-100 to-purple-100 rounded-xl mb-4 flex items-center justify-center text-4xl">
                    {item.isUnlocked ? item.icon || '📐' : '❓'}
                  </div>
                  <h4 className="font-bold text-gray-900 mb-1">{item.name}</h4>
                  <p className="text-sm text-gray-500 mb-3">{item.description}</p>
                  
                  {item.isUnlocked && item.funFact && (
                    <div className="bg-yellow-50 p-3 rounded-lg text-xs text-yellow-700">
                      <Star className="w-3 h-3 inline mr-1" />
                      {item.funFact}
                    </div>
                  )}

                  {!item.isUnlocked && (
                    <div className="text-xs text-gray-400">
                      <Lock className="w-3 h-3 inline mr-1" />
                      {item.unlockCondition}
                    </div>
                  )}
                </div>
              ))}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default ExplorationPage;
