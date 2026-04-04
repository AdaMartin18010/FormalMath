import React, { useState, useCallback } from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 计算题组件
 */
export const Calculation: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const [showSteps, setShowSteps] = useState(false);

  const handleChange = useCallback((e: React.ChangeEvent<HTMLInputElement>) => {
    onAnswer(e.target.value);
  }, [onAnswer]);

  // 解析可能的解题步骤输入
  const handleStepChange = useCallback((stepIndex: number, value: string) => {
    const steps = (userAnswer as { value: string; steps: string[] } | undefined)?.steps || [];
    const newSteps = [...steps];
    newSteps[stepIndex] = value;
    onAnswer({ 
      value: (userAnswer as any)?.value || '', 
      steps: newSteps 
    });
  }, [userAnswer, onAnswer]);

  return (
    <div className="space-y-4">
      {/* 题目内容 */}
      <div 
        className="text-gray-800 dark:text-gray-200 text-lg leading-relaxed prose dark:prose-invert"
        dangerouslySetInnerHTML={{ __html: exercise.content }}
      />

      {/* 分步解答切换 */}
      <div className="flex items-center gap-2">
        <button
          onClick={() => setShowSteps(!showSteps)}
          className="text-sm text-blue-600 dark:text-blue-400 hover:underline"
          type="button"
        >
          {showSteps ? '隐藏解题步骤' : '显示解题步骤'}
        </button>
      </div>

      {/* 分步输入 */}
      {showSteps && (
        <div className="space-y-3 p-4 bg-gray-50 dark:bg-slate-800 rounded-lg">
          <p className="text-sm text-gray-600 dark:text-gray-400">解题步骤（可选）：</p>
          {[0, 1, 2].map((stepIndex) => (
            <div key={stepIndex} className="flex items-center gap-2">
              <span className="text-gray-500 w-16">步骤 {stepIndex + 1}:</span>
              <input
                type="text"
                value={((userAnswer as any)?.steps?.[stepIndex]) || ''}
                onChange={(e) => handleStepChange(stepIndex, e.target.value)}
                disabled={disabled}
                placeholder={`输入第 ${stepIndex + 1} 步`}
                className={cn(
                  "flex-1 px-3 py-2 rounded-lg border",
                  "focus:outline-none focus:ring-2 focus:ring-blue-500",
                  "dark:bg-slate-700 dark:text-white dark:border-slate-600",
                  disabled && "opacity-60 cursor-not-allowed"
                )}
              />
            </div>
          ))}
        </div>
      )}

      {/* 最终答案输入 */}
      <div className="flex items-center gap-4 pt-4">
        <span className="text-gray-700 dark:text-gray-300 font-medium">
          最终答案：
        </span>
        <input
          type="text"
          inputMode="decimal"
          value={typeof userAnswer === 'string' ? userAnswer : (userAnswer as any)?.value || ''}
          onChange={handleChange}
          disabled={disabled}
          placeholder="请输入计算结果"
          className={cn(
            "flex-1 max-w-xs px-4 py-3 text-lg",
            "border-2 rounded-xl",
            "focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-blue-500",
            "dark:bg-slate-800 dark:text-white dark:border-slate-600",
            "transition-colors",
            disabled && "opacity-60 cursor-not-allowed"
          )}
        />
      </div>

      {/* 提示信息 */}
      <p className="text-sm text-gray-500 dark:text-gray-400">
        提示：数值计算请保留适当精度，可以使用科学计数法（如 1.23e-4）
      </p>
    </div>
  );
};

export default Calculation;
