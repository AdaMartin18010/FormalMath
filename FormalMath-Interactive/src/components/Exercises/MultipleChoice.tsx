import React, { useCallback } from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 多选题组件
 */
export const MultipleChoice: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const selectedOptions = (userAnswer as string[] | undefined) || [];
  const options = exercise.options || [];

  const toggleOption = useCallback((optionId: string) => {
    if (disabled) return;
    
    const newSelection = selectedOptions.includes(optionId)
      ? selectedOptions.filter(id => id !== optionId)
      : [...selectedOptions, optionId];
    
    onAnswer(newSelection);
  }, [selectedOptions, onAnswer, disabled]);

  return (
    <div className="space-y-3">
      <p className="text-sm text-gray-500 dark:text-gray-400 mb-2">
        请选择所有正确的选项（可多选）
      </p>
      {options.map((option, index) => {
        const letter = String.fromCharCode(65 + index);
        const isSelected = selectedOptions.includes(option.id);

        return (
          <button
            key={option.id}
            onClick={() => toggleOption(option.id)}
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
                  "flex-shrink-0 w-8 h-8 rounded-lg flex items-center justify-center text-sm font-semibold transition-colors",
                  isSelected
                    ? "bg-blue-500 text-white"
                    : "bg-gray-100 dark:bg-gray-800 text-gray-600 dark:text-gray-400"
                )}
              >
                {isSelected ? (
                  <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                  </svg>
                ) : (
                  letter
                )}
              </span>
              <div className="flex-1">
                <div 
                  className="text-gray-800 dark:text-gray-200 prose dark:prose-invert max-w-none"
                  dangerouslySetInnerHTML={{ __html: option.content }}
                />
              </div>
            </div>
          </button>
        );
      })}
    </div>
  );
};

export default MultipleChoice;
