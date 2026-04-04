/**
 * 谜题卡片组件
 * 展示单个谜题的信息和状态
 */

import React from 'react';
import { Clock, Star, Zap, Brain, Puzzle, Target, Calculator, Search } from 'lucide-react';
import type { Puzzle, GameDifficulty } from '../../../types/gamification';

interface PuzzleCardProps {
  puzzle: Puzzle;
  onClick?: (puzzle: Puzzle) => void;
  isLocked?: boolean;
  isCompleted?: boolean;
  highScore?: number;
}

const difficultyConfig: Record<GameDifficulty, { color: string; bg: string; label: string }> = {
  easy: { color: 'text-green-600', bg: 'bg-green-100', label: '简单' },
  medium: { color: 'text-yellow-600', bg: 'bg-yellow-100', label: '中等' },
  hard: { color: 'text-orange-600', bg: 'bg-orange-100', label: '困难' },
  expert: { color: 'text-red-600', bg: 'bg-red-100', label: '专家' },
};

const typeIcons: Record<Puzzle['type'], React.ReactNode> = {
  math_riddle: <Brain className="w-5 h-5" />,
  proof_construct: <Target className="w-5 h-5" />,
  concept_match: <Puzzle className="w-5 h-5" />,
  equation_solve: <Calculator className="w-5 h-5" />,
  pattern_recognize: <Search className="w-5 h-5" />,
  logic_deduction: <Zap className="w-5 h-5" />,
};

const typeLabels: Record<Puzzle['type'], string> = {
  math_riddle: '数学谜题',
  proof_construct: '证明构造',
  concept_match: '概念连线',
  equation_solve: '方程求解',
  pattern_recognize: '模式识别',
  logic_deduction: '逻辑推导',
};

export const PuzzleCard: React.FC<PuzzleCardProps> = ({
  puzzle,
  onClick,
  isLocked = false,
  isCompleted = false,
  highScore = 0,
}) => {
  const difficulty = difficultyConfig[puzzle.difficulty];

  const handleClick = () => {
    if (!isLocked && onClick) {
      onClick(puzzle);
    }
  };

  return (
    <div
      onClick={handleClick}
      className={`
        relative p-5 rounded-xl border-2 transition-all duration-300
        ${isLocked 
          ? 'bg-gray-100 border-gray-200 cursor-not-allowed opacity-60' 
          : isCompleted
            ? 'bg-green-50 border-green-300 cursor-pointer hover:shadow-lg hover:border-green-400'
            : 'bg-white border-gray-200 cursor-pointer hover:shadow-lg hover:border-blue-300'
        }
      `}
    >
      {/* 锁定遮罩 */}
      {isLocked && (
        <div className="absolute inset-0 flex items-center justify-center bg-gray-100/80 rounded-xl">
          <div className="text-gray-400">
            <svg className="w-10 h-10 mx-auto mb-2" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 15v2m-6 4h12a2 2 0 002-2v-6a2 2 0 00-2-2H6a2 2 0 00-2 2v6a2 2 0 002 2zm10-10V7a4 4 0 00-8 0v4h8z" />
            </svg>
            <span className="text-sm font-medium">未解锁</span>
          </div>
        </div>
      )}

      {/* 完成标记 */}
      {isCompleted && (
        <div className="absolute top-3 right-3">
          <div className="w-8 h-8 bg-green-500 rounded-full flex items-center justify-center">
            <svg className="w-5 h-5 text-white" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
          </div>
        </div>
      )}

      {/* 类型图标 */}
      <div className="flex items-start justify-between mb-3">
        <div className="flex items-center gap-2">
          <div className={`p-2 rounded-lg ${difficulty.bg} ${difficulty.color}`}>
            {typeIcons[puzzle.type]}
          </div>
          <span className="text-xs font-medium text-gray-500">{typeLabels[puzzle.type]}</span>
        </div>
        <span className={`text-xs font-semibold px-2 py-1 rounded-full ${difficulty.bg} ${difficulty.color}`}>
          {difficulty.label}
        </span>
      </div>

      {/* 标题和描述 */}
      <h3 className="font-bold text-gray-900 mb-2 line-clamp-1">{puzzle.title}</h3>
      <p className="text-sm text-gray-600 mb-4 line-clamp-2">{puzzle.description}</p>

      {/* 元信息 */}
      <div className="flex items-center justify-between text-sm text-gray-500">
        <div className="flex items-center gap-4">
          <span className="flex items-center gap-1">
            <Clock className="w-4 h-4" />
            {puzzle.estimatedTime}分钟
          </span>
          <span className="flex items-center gap-1">
            <Star className="w-4 h-4" />
            {Math.round(puzzle.passRate * 100)}%通过率
          </span>
        </div>
        {highScore > 0 && (
          <span className="font-medium text-blue-600">最高分: {highScore}</span>
        )}
      </div>

      {/* 概念标签 */}
      <div className="flex flex-wrap gap-1 mt-3">
        {puzzle.conceptIds.slice(0, 3).map((conceptId) => (
          <span
            key={conceptId}
            className="text-xs px-2 py-0.5 bg-gray-100 text-gray-600 rounded"
          >
            {conceptId}
          </span>
        ))}
      </div>
    </div>
  );
};

export default PuzzleCard;
