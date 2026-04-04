import React from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 判断题组件
 */
export const TrueFalse: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const selectedValue = userAnswer as boolean | undefined;

  return (
    <div className="space-y-4">
      {/* 题目内容 */}
      <div 
        className="text-gray-800 dark:text-gray-200 text-lg leading-relaxed prose dark:prose-invert"
        dangerouslySetInnerHTML={{ __html: exercise.content }}
      />

      {/* 判断选项 */}
      <div className="flex gap-4 pt-4">
        <button
          onClick={() => !disabled && onAnswer(true)}
          disabled={disabled}
          className={cn(
            "flex-1 p-6 rounded-xl border-2 transition-all duration-200",
            "flex flex-col items-center gap-3",
            "hover:shadow-lg focus:outline-none focus:ring-2 focus:ring-green-500",
            selectedValue === true
              ? "border-green-500 bg-green-50 dark:bg-green-900/20"
              : "border-gray-200 dark:border-gray-700 hover:border-green-300",
            disabled && "opacity-60 cursor-not-allowed"
          )}
        >
          <div className={cn(
            "w-16 h-16 rounded-full flex items-center justify-center",
            selectedValue === true
              ? "bg-green-500 text-white"
              : "bg-gray-100 dark:bg-gray-800 text-gray-600 dark:text-gray-400"
          )}>
            <svg className="w-8 h-8" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M5 13l4 4L19 7" />
            </svg>
          </div>
          <span className={cn(
            "text-lg font-semibold",
            selectedValue === true
              ? "text-green-700 dark:text-green-400"
              : "text-gray-700 dark:text-gray-300"
          )}>
            正确
          </span>
        </button>

        <button
          onClick={() => !disabled && onAnswer(false)}
          disabled={disabled}
          className={cn(
            "flex-1 p-6 rounded-xl border-2 transition-all duration-200",
            "flex flex-col items-center gap-3",
            "hover:shadow-lg focus:outline-none focus:ring-2 focus:ring-red-500",
            selectedValue === false
              ? "border-red-500 bg-red-50 dark:bg-red-900/20"
              : "border-gray-200 dark:border-gray-700 hover:border-red-300",
            disabled && "opacity-60 cursor-not-allowed"
          )}
        >
          <div className={cn(
            "w-16 h-16 rounded-full flex items-center justify-center",
            selectedValue === false
              ? "bg-red-500 text-white"
              : "bg-gray-100 dark:bg-gray-800 text-gray-600 dark:text-gray-400"
          )}>
            <svg className="w-8 h-8" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M6 18L18 6M6 6l12 12" />
            </svg>
          </div>
          <span className={cn(
            "text-lg font-semibold",
            selectedValue === false
              ? "text-red-700 dark:text-red-400"
              : "text-gray-700 dark:text-gray-300"
          )}>
            错误
          </span>
        </button>
      </div>
    </div>
  );
};

export default TrueFalse;
