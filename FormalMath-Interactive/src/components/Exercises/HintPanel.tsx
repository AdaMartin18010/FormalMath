import React from 'react';
import type { StepHint } from '../../types/exercise';
import { cn } from '../../utils/classNames';

interface HintPanelProps {
  hints: StepHint[];
  revealedCount: number;
  maxHints: number;
  onRequestHint: () => void;
  disabled?: boolean;
}

/**
 * 提示面板组件
 */
export const HintPanel: React.FC<HintPanelProps> = ({
  hints,
  revealedCount,
  maxHints,
  onRequestHint,
  disabled = false,
}) => {
  const hasMoreHints = revealedCount < maxHints;

  return (
    <div className="space-y-4">
      {/* 提示标题 */}
      <div className="flex items-center justify-between">
        <h4 className="text-sm font-medium text-gray-700 dark:text-gray-300 flex items-center gap-2">
          <svg className="w-4 h-4 text-yellow-500" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9.663 17h4.673M12 3v1m6.364 1.636l-.707.707M21 12h-1M4 12H3m3.343-5.657l-.707-.707m2.828 9.9a5 5 0 117.072 0l-.548.547A3.374 3.374 0 0014 18.469V19a2 2 0 11-4 0v-.531c0-.895-.356-1.754-.988-2.386l-.548-.547z" />
          </svg>
          提示 ({revealedCount}/{maxHints})
        </h4>
        {hasMoreHints && (
          <button
            onClick={onRequestHint}
            disabled={disabled}
            className={cn(
              "text-sm px-3 py-1 rounded-full",
              "bg-yellow-100 dark:bg-yellow-900/30 text-yellow-700 dark:text-yellow-400",
              "hover:bg-yellow-200 dark:hover:bg-yellow-900/50",
              "transition-colors",
              disabled && "opacity-50 cursor-not-allowed"
            )}
          >
            获取提示
          </button>
        )}
      </div>

      {/* 已揭示的提示列表 */}
      {hints.length > 0 && (
        <div className="space-y-3">
          {hints.map((hint, index) => (
            <div
              key={hint.step}
              className={cn(
                "p-4 rounded-lg border-l-4",
                "bg-yellow-50 dark:bg-yellow-900/10",
                "border-yellow-400 dark:border-yellow-600",
                "animate-in fade-in slide-in-from-left-2"
              )}
              style={{ animationDelay: `${index * 100}ms` }}
            >
              <div className="flex items-start gap-3">
                <span className="flex-shrink-0 w-6 h-6 rounded-full bg-yellow-200 dark:bg-yellow-800 text-yellow-800 dark:text-yellow-200 text-xs font-bold flex items-center justify-center">
                  {hint.step + 1}
                </span>
                <div className="flex-1">
                  <h5 className="font-medium text-yellow-900 dark:text-yellow-300 mb-1">
                    {hint.title}
                  </h5>
                  <p className="text-sm text-yellow-800 dark:text-yellow-400">
                    {hint.content}
                  </p>
                </div>
              </div>
            </div>
          ))}
        </div>
      )}

      {/* 无提示状态 */}
      {hints.length === 0 && (
        <div className="text-center py-6 text-gray-500 dark:text-gray-400">
          <svg className="w-12 h-12 mx-auto mb-2 opacity-50" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M9.663 17h4.673M12 3v1m6.364 1.636l-.707.707M21 12h-1M4 12H3m3.343-5.657l-.707-.707m2.828 9.9a5 5 0 117.072 0l-.548.547A3.374 3.374 0 0014 18.469V19a2 2 0 11-4 0v-.531c0-.895-.356-1.754-.988-2.386l-.548-.547z" />
          </svg>
          <p className="text-sm">还没有提示</p>
          {hasMoreHints && !disabled && (
            <p className="text-xs mt-1">点击上方按钮获取第一个提示</p>
          )}
        </div>
      )}

      {/* 提示使用建议 */}
      {hasMoreHints && (
        <p className="text-xs text-gray-500 dark:text-gray-500">
          💡 建议先独立思考，遇到困难时再使用提示
        </p>
      )}

      {/* 无更多提示 */}
      {!hasMoreHints && hints.length > 0 && (
        <p className="text-xs text-gray-500 dark:text-gray-500 text-center">
          已显示所有提示
        </p>
      )}
    </div>
  );
};

export default HintPanel;
