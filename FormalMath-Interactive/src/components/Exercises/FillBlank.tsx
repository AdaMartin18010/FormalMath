import React from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 填空题组件
 */
export const FillBlank: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const answers = (userAnswer as Record<string, string> | undefined) || {};
  const blanks = exercise.blanks || [];

  const handleChange = (blankId: string, value: string) => {
    const newAnswers = { ...answers, [blankId]: value };
    onAnswer(newAnswers);
  };

  return (
    <div className="space-y-4">
      <div className="text-gray-800 dark:text-gray-200 text-lg leading-relaxed">
        {blanks.length > 0 ? (
          // 使用带有输入框的渲染方式
          <FillBlankContent 
            content={exercise.content}
            blanks={blanks}
            answers={answers}
            onChange={handleChange}
            disabled={disabled}
          />
        ) : (
          // 简单文本渲染
          <div dangerouslySetInnerHTML={{ __html: exercise.content }} />
        )}
      </div>

      {blanks.length > 0 && (
        <div className="mt-6 space-y-3">
          {blanks.map((blank, index) => (
            <div key={blank.id} className="flex items-center gap-3">
              <span className="text-gray-500 dark:text-gray-400 w-16">
                空 {index + 1}:
              </span>
              <input
                type="text"
                value={answers[blank.id] || ''}
                onChange={(e) => handleChange(blank.id, e.target.value)}
                disabled={disabled}
                placeholder={`请输入第 ${index + 1} 个答案`}
                className={cn(
                  "flex-1 px-4 py-2 rounded-lg border-2 transition-colors",
                  "focus:outline-none focus:ring-2 focus:ring-blue-500",
                  "dark:bg-slate-800 dark:text-white",
                  disabled && "opacity-60 cursor-not-allowed"
                )}
              />
            </div>
          ))}
        </div>
      )}
    </div>
  );
};

/**
 * 填空题内容渲染组件
 */
interface FillBlankContentProps {
  content: string;
  blanks: Array<{ id: string; position: number }>;
  answers: Record<string, string>;
  onChange: (blankId: string, value: string) => void;
  disabled: boolean;
}

const FillBlankContent: React.FC<FillBlankContentProps> = ({
  content,
  blanks,
  answers,
  onChange,
  disabled,
}) => {
  // 将内容分割为段落和输入框
  const parts: React.ReactNode[] = [];
  let lastIndex = 0;

  // 查找所有空白标记
  const blankRegex = /_{3,}\((\d+)\)_{3,}/g;
  let match;

  while ((match = blankRegex.exec(content)) !== null) {
    // 添加空白前的文本
    if (match.index > lastIndex) {
      parts.push(
        <span 
          key={`text-${lastIndex}`}
          dangerouslySetInnerHTML={{ 
            __html: content.slice(lastIndex, match.index) 
          }} 
        />
      );
    }

    const blankIndex = parseInt(match[1]) - 1;
    const blank = blanks[blankIndex];

    if (blank) {
      parts.push(
        <input
          key={blank.id}
          type="text"
          value={answers[blank.id] || ''}
          onChange={(e) => onChange(blank.id, e.target.value)}
          disabled={disabled}
          placeholder={`${blankIndex + 1}`}
          className={cn(
            "inline-block mx-1 px-2 py-1 w-24 text-center",
            "border-b-2 border-gray-400 dark:border-gray-600",
            "bg-transparent focus:outline-none focus:border-blue-500",
            "transition-colors",
            disabled && "opacity-60 cursor-not-allowed"
          )}
        />
      );
    }

    lastIndex = match.index + match[0].length;
  }

  // 添加剩余文本
  if (lastIndex < content.length) {
    parts.push(
      <span 
        key={`text-${lastIndex}`}
        dangerouslySetInnerHTML={{ 
          __html: content.slice(lastIndex) 
        }} 
      />
    );
  }

  return <>{parts}</>;
};

export default FillBlank;
