import React from 'react';
import type { ValidationResult } from '../../types/exercise';
import { cn } from '../../utils/classNames';

interface ExerciseFeedbackProps {
  result: ValidationResult;
  onShowSolution: () => void;
  onContinue: () => void;
  showDetailed?: boolean;
}

/**
 * 练习反馈组件
 */
export const ExerciseFeedback: React.FC<ExerciseFeedbackProps> = ({
  result,
  onShowSolution,
  onContinue,
  showDetailed = true,
}) => {
  const isCorrect = result.isCorrect;
  const isPartial = !isCorrect && result.score && result.score > 0;

  return (
    <div className={cn(
      "rounded-xl p-6 mb-6 animate-in fade-in slide-in-from-bottom-4",
      isCorrect 
        ? "bg-green-50 dark:bg-green-900/20 border-2 border-green-200 dark:border-green-800"
        : isPartial
          ? "bg-yellow-50 dark:bg-yellow-900/20 border-2 border-yellow-200 dark:border-yellow-800"
          : "bg-red-50 dark:bg-red-900/20 border-2 border-red-200 dark:border-red-800"
    )}>
      {/* 结果图标和标题 */}
      <div className="flex items-center gap-3 mb-4">
        <div className={cn(
          "w-12 h-12 rounded-full flex items-center justify-center",
          isCorrect 
            ? "bg-green-500"
            : isPartial
              ? "bg-yellow-500"
              : "bg-red-500"
        )}>
          {isCorrect ? (
            <svg className="w-7 h-7 text-white" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
          ) : (
            <svg className="w-7 h-7 text-white" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
            </svg>
          )}
        </div>
        <div>
          <h3 className={cn(
            "text-xl font-bold",
            isCorrect 
              ? "text-green-800 dark:text-green-300"
              : isPartial
                ? "text-yellow-800 dark:text-yellow-300"
                : "text-red-800 dark:text-red-300"
          )}>
            {isCorrect ? '回答正确！' : isPartial ? '部分正确' : '回答错误'}
          </h3>
          <p className={cn(
            "text-sm",
            isCorrect 
              ? "text-green-600 dark:text-green-400"
              : isPartial
                ? "text-yellow-600 dark:text-yellow-400"
                : "text-red-600 dark:text-red-400"
          )}>
            得分：{result.score}/100
            {result.partialCredit && `（部分得分 ${result.partialCredit} 分）`}
          </p>
        </div>
      </div>

      {/* 反馈信息 */}
      <div className="space-y-3">
        <p className={cn(
          "text-base",
          isCorrect 
            ? "text-green-700 dark:text-green-300"
            : "text-gray-700 dark:text-gray-300"
        )}>
          {result.feedback}
        </p>

        {result.detailedFeedback && showDetailed && (
          <div className="mt-3 p-3 bg-white/50 dark:bg-black/20 rounded-lg">
            <p className="text-sm text-gray-600 dark:text-gray-400">
              {result.detailedFeedback}
            </p>
          </div>
        )}

        {/* 正确答案 */}
        {result.correctAnswer !== undefined && (
          <div className="mt-4 p-3 bg-white dark:bg-slate-800 rounded-lg border border-gray-200 dark:border-gray-700">
            <p className="text-sm font-medium text-gray-600 dark:text-gray-400 mb-1">
              正确答案：
            </p>
            <p className="text-base text-gray-900 dark:text-gray-100">
              {formatCorrectAnswer(result.correctAnswer)}
            </p>
          </div>
        )}

        {/* 相关提示 */}
        {result.hints && result.hints.length > 0 && (
          <div className="mt-4">
            <p className="text-sm font-medium text-gray-600 dark:text-gray-400 mb-2">
              相关提示：
            </p>
            <ul className="list-disc list-inside text-sm text-gray-600 dark:text-gray-400 space-y-1">
              {result.hints.map((hint, index) => (
                <li key={index}>{hint}</li>
              ))}
            </ul>
          </div>
        )}
      </div>

      {/* 操作按钮 */}
      <div className="flex gap-3 mt-6">
        <button
          onClick={onContinue}
          className={cn(
            "px-6 py-2 rounded-lg font-medium transition-colors",
            isCorrect
              ? "bg-green-600 text-white hover:bg-green-700"
              : "bg-blue-600 text-white hover:bg-blue-700"
          )}
        >
          {isCorrect ? '下一题' : '再试一次'}
        </button>
        {!isCorrect && (
          <button
            onClick={onShowSolution}
            className="px-6 py-2 rounded-lg font-medium border-2 border-gray-300 dark:border-gray-600 text-gray-700 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-slate-800 transition-colors"
          >
            查看解析
          </button>
        )}
      </div>
    </div>
  );
};

/**
 * 格式化正确答案显示
 */
function formatCorrectAnswer(answer: unknown): string {
  if (typeof answer === 'string') {
    return answer;
  }
  if (typeof answer === 'number') {
    return answer.toString();
  }
  if (typeof answer === 'boolean') {
    return answer ? '正确' : '错误';
  }
  if (Array.isArray(answer)) {
    return answer.join('、');
  }
  if (typeof answer === 'object' && answer !== null) {
    return Object.entries(answer)
      .map(([key, value]) => `${key}: ${value}`)
      .join('; ');
  }
  return String(answer);
}

export default ExerciseFeedback;
