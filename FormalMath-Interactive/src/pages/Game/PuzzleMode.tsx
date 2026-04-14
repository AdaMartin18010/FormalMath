// @ts-nocheck
/**
 * 解谜游戏模式页面
 * 展示谜题关卡和解答界面
 */

import React, { useState, useEffect } from 'react';
import { useNavigate } from 'react-router-dom';
import { Brain, Trophy, ChevronRight, Sparkles, Target, Puzzle, Calculator, Search, Zap } from 'lucide-react';
import { usePuzzle, useAchievements, useTutor } from '../../hooks/game';
import { PuzzleCard, PuzzleSolver } from '../../components/Gamification';
import type { Puzzle, GameReward } from '../../types/gamification';

export const PuzzleMode: React.FC = () => {
  const navigate = useNavigate();
  const [activeTab, setActiveTab] = useState<'levels' | 'puzzles'>('levels');
  const [selectedPuzzle, setSelectedPuzzle] = useState<Puzzle | null>(null);
  const [showResult, setShowResult] = useState(false);

  const {
    puzzles,
    puzzleLevels,
    loadPuzzles,
    loadPuzzleLevels,
    startPuzzle,
    submitAnswer,
    useHint,
    resetPuzzle,
    timeSpent,
    hintsUsed,
    result,
    isCompleted,
    isPlaying,
  } = usePuzzle({
    onComplete: () => setShowResult(true),
  });

  const { level, unlockedBadges } = useAchievements();
  const { isEnabled: tutorEnabled, personality: tutorPersonality, getHint, getFeedback } = useTutor();

  // 初始化加载
  useEffect(() => {
    loadPuzzles();
    loadPuzzleLevels();
  }, []);

  // 开始谜题
  const handleStartPuzzle = async (puzzle: Puzzle) => {
    setSelectedPuzzle(puzzle);
    await startPuzzle(puzzle.id);
  };

  // 提交答案
  const handleSubmit = async (answer: unknown) => {
    await submitAnswer(answer);
    if (result?.correct) {
      await getFeedback('success');
    } else {
      await getFeedback('failure');
    }
  };

  // 返回列表
  const handleBack = () => {
    resetPuzzle();
    setSelectedPuzzle(null);
    setShowResult(false);
  };

  // 渲染结果弹窗
  const renderResultModal = () => {
    if (!result) return null;

    return (
      <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4">
        <div className="bg-white rounded-2xl max-w-md w-full p-8 text-center">
          <div className={`
            w-20 h-20 mx-auto rounded-full flex items-center justify-center mb-4
            ${result.correct ? 'bg-green-100' : 'bg-red-100'}
          `}>
            {result.correct ? (
              <Trophy className="w-10 h-10 text-green-600" />
            ) : (
              <Target className="w-10 h-10 text-red-600" />
            )}
          </div>

          <h2 className="text-2xl font-bold mb-2">
            {result.correct ? '恭喜你！' : '再接再厉'}
          </h2>
          <p className="text-gray-600 mb-6">{result.feedback}</p>

          {result.correct && (
            <div className="bg-gray-50 rounded-xl p-4 mb-6">
              <div className="text-sm text-gray-500 mb-2">获得奖励</div>
              <div className="flex justify-center gap-4">
                <div className="text-center">
                  <div className="text-2xl font-bold text-blue-600">+{result.score}</div>
                  <div className="text-xs text-gray-500">分数</div>
                </div>
                {result.rewards.map((reward, index) => (
                  <div key={index} className="text-center">
                    {reward.type === 'xp' && (
                      <>
                        <div className="text-2xl font-bold text-purple-600">+{reward.amount}</div>
                        <div className="text-xs text-gray-500">经验</div>
                      </>
                    )}
                    {reward.type === 'coin' && (
                      <>
                        <div className="text-2xl font-bold text-yellow-600">+{reward.amount}</div>
                        <div className="text-xs text-gray-500">金币</div>
                      </>
                    )}
                  </div>
                ))}
              </div>
            </div>
          )}

          <div className="flex gap-3">
            <button
              onClick={handleBack}
              className="flex-1 px-6 py-3 border rounded-xl hover:bg-gray-50"
            >
              返回列表
            </button>
            <button
              onClick={() => {
                resetPuzzle();
                setShowResult(false);
              }}
              className="flex-1 px-6 py-3 bg-blue-600 text-white rounded-xl hover:bg-blue-700"
            >
              再试一次
            </button>
          </div>
        </div>
      </div>
    );
  };

  // 如果在玩谜题，显示解答界面
  if (isPlaying && selectedPuzzle) {
    return (
      <div className="min-h-screen bg-gray-50 py-8">
        <div className="max-w-6xl mx-auto px-4">
          <button
            onClick={handleBack}
            className="mb-6 flex items-center gap-2 text-gray-600 hover:text-gray-900"
          >
            <ChevronRight className="w-5 h-5 rotate-180" />
            返回谜题列表
          </button>

          <PuzzleSolver
            puzzle={selectedPuzzle}
            timeSpent={timeSpent}
            hintsUsed={hintsUsed}
            onSubmit={handleSubmit}
            onUseHint={useHint}
            onQuit={handleBack}
            feedback={result?.feedback}
            isCorrect={result?.correct}
          />

          {showResult && renderResultModal()}
        </div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部 */}
      <div className="bg-gradient-to-r from-blue-600 to-purple-600 text-white">
        <div className="max-w-6xl mx-auto px-4 py-8">
          <div className="flex items-center justify-between">
            <div>
              <h1 className="text-3xl font-bold mb-2">解谜挑战</h1>
              <p className="text-blue-100">通过解谜提升你的数学能力</p>
            </div>
            <div className="flex items-center gap-4">
              <div className="bg-white/20 px-4 py-2 rounded-xl text-center">
                <div className="text-2xl font-bold">{level.currentLevel}</div>
                <div className="text-xs text-blue-100">等级</div>
              </div>
              <div className="bg-white/20 px-4 py-2 rounded-xl text-center">
                <div className="text-2xl font-bold">{unlockedBadges.length}</div>
                <div className="text-xs text-blue-100">徽章</div>
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
            onClick={() => setActiveTab('levels')}
            className={`px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'levels'
                ? 'bg-blue-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            关卡模式
          </button>
          <button
            onClick={() => setActiveTab('puzzles')}
            className={`px-6 py-3 rounded-xl font-medium transition-colors
              ${activeTab === 'puzzles'
                ? 'bg-blue-600 text-white'
                : 'bg-white text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            全部谜题
          </button>
        </div>

        {/* 关卡模式 */}
        {activeTab === 'levels' && (
          <div className="space-y-6">
            {puzzleLevels.map((level, index) => (
              <div
                key={level.id}
                className="bg-white rounded-2xl p-6 shadow-sm hover:shadow-md transition-shadow"
              >
                <div className="flex items-start justify-between mb-4">
                  <div className="flex items-center gap-4">
                    <div className={`
                      w-12 h-12 rounded-xl flex items-center justify-center text-xl
                      ${index === 0 ? 'bg-green-100' : index === 1 ? 'bg-yellow-100' : 'bg-red-100'}
                    `}>
                      {index === 0 ? '🌱' : index === 1 ? '📚' : '👑'}
                    </div>
                    <div>
                      <h3 className="text-xl font-bold text-gray-900">{level.name}</h3>
                      <p className="text-gray-500">{level.description}</p>
                    </div>
                  </div>
                  <div className="text-right">
                    <div className="text-sm text-gray-500">需要分数</div>
                    <div className="font-bold text-blue-600">{level.requiredScore}</div>
                  </div>
                </div>

                <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
                  {level.puzzles.map((puzzleId) => {
                    const puzzle = puzzles.find((p) => p.id === puzzleId);
                    if (!puzzle) return null;
                    return (
                      <PuzzleCard
                        key={puzzle.id}
                        puzzle={puzzle}
                        onClick={handleStartPuzzle}
                      />
                    );
                  })}
                </div>

                <div className="mt-4 pt-4 border-t flex items-center justify-between">
                  <div className="flex items-center gap-2 text-sm text-gray-500">
                    <Sparkles className="w-4 h-4" />
                    通关奖励
                  </div>
                  <div className="flex gap-2">
                    {level.rewards.map((reward, i) => (
                      <span
                        key={i}
                        className="px-3 py-1 bg-blue-50 text-blue-600 rounded-full text-sm"
                      >
                        {reward.type === 'xp' && `+${reward.amount} 经验`}
                        {reward.type === 'badge' && '🏆 徽章'}
                      </span>
                    ))}
                  </div>
                </div>
              </div>
            ))}
          </div>
        )}

        {/* 全部谜题 */}
        {activeTab === 'puzzles' && (
          <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
            {puzzles.map((puzzle) => (
              <PuzzleCard
                key={puzzle.id}
                puzzle={puzzle}
                onClick={handleStartPuzzle}
              />
            ))}
          </div>
        )}
      </div>
    </div>
  );
};

export default PuzzleMode;
