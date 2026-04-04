import React from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 单选题组件
 */
export const SingleChoice: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const selectedOption = userAnswer as string | undefined;
  const options = exercise.options || [];

  return (
    <div className="space-y-3">
      {options.map((option, index) => {
        const letter = String.fromCharCode(65 + index); // A, B, C, D...
        const isSelected = selectedOption === option.id;

        return (
          <button
            key={option.id}
            onClick={() => !disabled && onAnswer(option.id)}
            disabled={disabled}
            className={cn(
              "w-full text-left p-4 rounded-xl border-2 transition-all duration-200",
              "hover:shadow-md focus:outline-none focus:ring-2 focus:ring-blue-500",
              isSelected
                ? "border-blue-500 bg-blue-50 dark:bg-blue-900/20"
                : "border-gray-200 dark:border-gray-700 hover:border-blue-300",
              disabled && "opacity-60 cursor-not-allowed"
            )}
          >
            <div className="flex items-start gap-3">
              <span
                className={cn(
                  "flex-shrink-0 w-8 h-8 rounded-full flex items-center justify-center text-sm font-semibold",
                  isSelected
                    ? "bg-blue-500 text-white"
                    : "bg-gray-100 dark:bg-gray-800 text-gray-600 dark:text-gray-400"
                )}
              >
                {letter}
              </span>
              <div className="flex-1">
                <div 
                  className="text-gray-800 dark:text-gray-200 prose dark:prose-invert max-w-none"
                  dangerouslySetInnerHTML={{ __html: option.content }}
                />
              </div>
              {isSelected && (
                <svg
                  className="w-6 h-6 text-blue-500 flex-shrink-0"
                  fill="none"
                  viewBox="0 0 24 24"
                  stroke="currentColor"
                >
                  <path
                    strokeLinecap="round"
                    strokeLinejoin="round"
                    strokeWidth={2}
                    d="M5 13l4 4L19 7"
                  />
                </svg>
              )}
            </div>
          </button>
        );
      })}
    </div>
  );
};

export default SingleChoice;
