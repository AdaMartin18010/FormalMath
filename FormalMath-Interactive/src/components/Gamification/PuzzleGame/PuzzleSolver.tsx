/**
 * 谜题解答组件
 * 提供谜题的交互式解答界面
 */

import React, { useState, useEffect } from 'react';
import { Clock, Lightbulb, X, Check, AlertCircle, ArrowRight } from 'lucide-react';
import type { Puzzle, Hint } from '../../../types/gamification';

interface PuzzleSolverProps {
  puzzle: Puzzle;
  timeSpent: number;
  hintsUsed: string[];
  onSubmit: (answer: unknown) => void;
  onUseHint: (hintId: string) => Promise<boolean>;
  onQuit: () => void;
  feedback?: string | null;
  isCorrect?: boolean | null;
}

export const PuzzleSolver: React.FC<PuzzleSolverProps> = ({
  puzzle,
  timeSpent,
  hintsUsed,
  onSubmit,
  onUseHint,
  onQuit,
  feedback,
  isCorrect,
}) => {
  const [answer, setAnswer] = useState<unknown>('');
  const [selectedHints, setSelectedHints] = useState<Hint[]>([]);
  const [showHint, setShowHint] = useState<Hint | null>(null);
  const [proofSteps, setProofSteps] = useState<string[]>([]);
  const [matches, setMatches] = useState<Record<string, string>>({});

  // 格式化时间
  const formatTime = (seconds: number) => {
    const mins = Math.floor(seconds / 60);
    const secs = seconds % 60;
    return `${mins}:${secs.toString().padStart(2, '0')}`;
  };

  // 使用提示
  const handleUseHint = async (hint: Hint) => {
    if (hintsUsed.includes(hint.id)) {
      setShowHint(hint);
      return;
    }

    const success = await onUseHint(hint.id);
    if (success) {
      setSelectedHints([...selectedHints, hint]);
      setShowHint(hint);
    }
  };

  // 提交答案
  const handleSubmit = () => {
    if (puzzle.type === 'proof_construct') {
      onSubmit(proofSteps);
    } else if (puzzle.type === 'concept_match') {
      onSubmit(matches);
    } else {
      onSubmit(answer);
    }
  };

  // 渲染谜题内容
  const renderPuzzleContent = () => {
    switch (puzzle.type) {
      case 'math_riddle':
        return (
          <div className="space-y-4">
            <p className="text-lg text-gray-800 leading-relaxed">
              {(puzzle.content as { problem: string }).problem}
            </p>
            <div className="bg-blue-50 p-4 rounded-lg">
              <label className="block text-sm font-medium text-gray-700 mb-2">
                你的答案
              </label>
              <input
                type="text"
                value={answer as string}
                onChange={(e) => setAnswer(e.target.value)}
                className="w-full px-4 py-2 border rounded-lg focus:ring-2 focus:ring-blue-500"
                placeholder="输入你的答案..."
              />
            </div>
          </div>
        );

      case 'proof_construct':
        const proofContent = puzzle.content as {
          theorem: string;
          given: string[];
          availableSteps: { id: string; content: string }[];
        };
        return (
          <div className="space-y-4">
            <div className="bg-purple-50 p-4 rounded-lg">
              <h4 className="font-semibold text-purple-900 mb-2">定理</h4>
              <p className="text-purple-800">{proofContent.theorem}</p>
            </div>
            <div className="bg-gray-50 p-4 rounded-lg">
              <h4 className="font-semibold text-gray-700 mb-2">已知</h4>
              <ul className="list-disc list-inside text-gray-600">
                {proofContent.given.map((g, i) => (
                  <li key={i}>{g}</li>
                ))}
              </ul>
            </div>
            <div className="space-y-2">
              <h4 className="font-semibold text-gray-700">证明步骤</h4>
              <p className="text-sm text-gray-500">点击下方步骤，按正确顺序构建证明：</p>
              <div className="flex flex-wrap gap-2">
                {proofContent.availableSteps.map((step) => (
                  <button
                    key={step.id}
                    onClick={() => {
                      if (!proofSteps.includes(step.id)) {
                        setProofSteps([...proofSteps, step.id]);
                      }
                    }}
                    disabled={proofSteps.includes(step.id)}
                    className={`px-3 py-2 rounded-lg text-sm transition-colors
                      ${proofSteps.includes(step.id)
                        ? 'bg-gray-200 text-gray-400 cursor-not-allowed'
                        : 'bg-blue-100 text-blue-700 hover:bg-blue-200'
                      }
                    `}
                  >
                    {step.content}
                  </button>
                ))}
              </div>
              {proofSteps.length > 0 && (
                <div className="mt-4 p-4 bg-green-50 rounded-lg">
                  <h5 className="font-medium text-green-800 mb-2">当前证明序列：</h5>
                  <ol className="list-decimal list-inside space-y-1">
                    {proofSteps.map((stepId, index) => {
                      const step = proofContent.availableSteps.find((s) => s.id === stepId);
                      return (
                        <li key={index} className="text-green-700 flex items-center gap-2">
                          {step?.content}
                          <button
                            onClick={() => setProofSteps(proofSteps.filter((_, i) => i !== index))}
                            className="text-red-500 hover:text-red-700"
                          >
                            <X className="w-4 h-4" />
                          </button>
                        </li>
                      );
                    })}
                  </ol>
                </div>
              )}
            </div>
          </div>
        );

      case 'concept_match':
        const matchContent = puzzle.content as {
          concepts: { id: string; content: string }[];
          definitions: { id: string; content: string }[];
        };
        return (
          <div className="space-y-4">
            <p className="text-gray-600">将概念与正确的定义连线：</p>
            <div className="grid grid-cols-2 gap-6">
              <div className="space-y-3">
                <h4 className="font-semibold text-gray-700">概念</h4>
                {matchContent.concepts.map((concept) => (
                  <div
                    key={concept.id}
                    className={`p-3 rounded-lg border-2 cursor-pointer transition-colors
                      ${matches[concept.id] ? 'border-green-400 bg-green-50' : 'border-gray-200 hover:border-blue-300'}
                    `}
                    onClick={() => {
                      // 选择概念，等待匹配
                    }}
                  >
                    {concept.content}
                  </div>
                ))}
              </div>
              <div className="space-y-3">
                <h4 className="font-semibold text-gray-700">定义</h4>
                {matchContent.definitions.map((def) => (
                  <div
                    key={def.id}
                    className="p-3 rounded-lg border-2 border-gray-200 hover:border-blue-300 cursor-pointer"
                    onClick={() => {
                      // 匹配到选中的概念
                    }}
                  >
                    {def.content}
                  </div>
                ))}
              </div>
            </div>
          </div>
        );

      case 'equation_solve':
        const equationContent = puzzle.content as { equation: string };
        return (
          <div className="space-y-4">
            <div className="bg-gray-900 text-white p-6 rounded-lg text-center text-xl font-mono">
              {equationContent.equation}
            </div>
            <div className="bg-blue-50 p-4 rounded-lg">
              <label className="block text-sm font-medium text-gray-700 mb-2">
                输入解（用逗号分隔多个变量）
              </label>
              <input
                type="text"
                value={answer as string}
                onChange={(e) => setAnswer(e.target.value)}
                className="w-full px-4 py-2 border rounded-lg focus:ring-2 focus:ring-blue-500"
                placeholder="例如: x=3, y=2"
              />
            </div>
          </div>
        );

      case 'pattern_recognize':
        const patternContent = puzzle.content as { sequence: (string | number)[] };
        return (
          <div className="space-y-4">
            <div className="flex justify-center gap-2">
              {patternContent.sequence.map((item, i) => (
                <div
                  key={i}
                  className="w-12 h-12 bg-blue-500 text-white rounded-lg flex items-center justify-center text-lg font-bold"
                >
                  {item}
                </div>
              ))}
              <div className="w-12 h-12 border-2 border-dashed border-gray-300 rounded-lg flex items-center justify-center">
                <span className="text-gray-400">?</span>
              </div>
            </div>
            <div className="bg-blue-50 p-4 rounded-lg">
              <label className="block text-sm font-medium text-gray-700 mb-2">
                接下来的数字（用逗号分隔）
              </label>
              <input
                type="text"
                value={answer as string}
                onChange={(e) => setAnswer(e.target.value)}
                className="w-full px-4 py-2 border rounded-lg focus:ring-2 focus:ring-blue-500"
                placeholder="例如: 21, 34"
              />
            </div>
          </div>
        );

      default:
        return <div>不支持的谜题类型</div>;
    }
  };

  return (
    <div className="bg-white rounded-2xl shadow-xl overflow-hidden max-w-3xl mx-auto">
      {/* 头部 */}
      <div className="bg-gradient-to-r from-blue-600 to-purple-600 px-6 py-4">
        <div className="flex items-center justify-between text-white">
          <h2 className="text-xl font-bold">{puzzle.title}</h2>
          <button
            onClick={onQuit}
            className="p-2 hover:bg-white/20 rounded-lg transition-colors"
          >
            <X className="w-5 h-5" />
          </button>
        </div>
      </div>

      <div className="p-6">
        {/* 计时和提示 */}
        <div className="flex items-center justify-between mb-6">
          <div className="flex items-center gap-2 text-gray-600">
            <Clock className="w-5 h-5" />
            <span className="font-mono text-lg">{formatTime(timeSpent)}</span>
          </div>
          <div className="flex items-center gap-2">
            {puzzle.hints.map((hint) => (
              <button
                key={hint.id}
                onClick={() => handleUseHint(hint)}
                disabled={selectedHints.includes(hint) && !hintsUsed.includes(hint.id)}
                className={`flex items-center gap-1 px-3 py-1.5 rounded-lg text-sm transition-colors
                  ${hintsUsed.includes(hint.id) || selectedHints.includes(hint)
                    ? 'bg-yellow-100 text-yellow-700'
                    : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
                  }
                `}
              >
                <Lightbulb className="w-4 h-4" />
                提示 {hint.level}
                {!hintsUsed.includes(hint.id) && `(-${hint.cost}币)`}
              </button>
            ))}
          </div>
        </div>

        {/* 提示显示 */}
        {showHint && (
          <div className="mb-6 p-4 bg-yellow-50 border border-yellow-200 rounded-lg">
            <div className="flex items-start gap-2">
              <Lightbulb className="w-5 h-5 text-yellow-600 mt-0.5" />
              <div>
                <h4 className="font-medium text-yellow-800">提示 {showHint.level}</h4>
                <p className="text-yellow-700 mt-1">{showHint.content}</p>
              </div>
              <button
                onClick={() => setShowHint(null)}
                className="ml-auto text-yellow-600 hover:text-yellow-800"
              >
                <X className="w-4 h-4" />
              </button>
            </div>
          </div>
        )}

        {/* 谜题内容 */}
        <div className="mb-6">{renderPuzzleContent()}</div>

        {/* 反馈 */}
        {feedback && (
          <div
            className={`mb-6 p-4 rounded-lg flex items-center gap-3
              ${isCorrect === true
                ? 'bg-green-50 text-green-800'
                : isCorrect === false
                  ? 'bg-red-50 text-red-800'
                  : 'bg-blue-50 text-blue-800'
              }
            `}
          >
            {isCorrect === true ? (
              <Check className="w-5 h-5" />
            ) : isCorrect === false ? (
              <AlertCircle className="w-5 h-5" />
            ) : (
              <Lightbulb className="w-5 h-5" />
            )}
            <span>{feedback}</span>
          </div>
        )}

        {/* 操作按钮 */}
        <div className="flex items-center justify-end gap-3">
          <button
            onClick={onQuit}
            className="px-6 py-2 text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
          >
            放弃
          </button>
          <button
            onClick={handleSubmit}
            className="flex items-center gap-2 px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
          >
            提交答案
            <ArrowRight className="w-4 h-4" />
          </button>
        </div>
      </div>
    </div>
  );
};

export default PuzzleSolver;
