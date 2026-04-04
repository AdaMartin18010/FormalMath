import React from 'react';
import type { ExerciseComponentProps } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 证明题组件
 */
export const Proof: React.FC<ExerciseComponentProps> = ({
  exercise,
  userAnswer,
  onAnswer,
  disabled = false,
}) => {
  const value = (userAnswer as string | undefined) || '';

  return (
    <div className="space-y-4">
      {/* 题目内容 */}
      <div 
        className="text-gray-800 dark:text-gray-200 text-lg leading-relaxed prose dark:prose-invert"
        dangerouslySetInnerHTML={{ __html: exercise.content }}
      />

      {/* 证明输入区 */}
      <div className="space-y-2">
        <label className="block text-sm font-medium text-gray-700 dark:text-gray-300">
          证明过程：
        </label>
        <textarea
          value={value}
          onChange={(e) => onAnswer(e.target.value)}
          disabled={disabled}
          placeholder="请在此处输入您的证明过程...&#10;建议使用以下结构：&#10;1. 明确已知条件和待证结论&#10;2. 列出关键步骤&#10;3. 给出最终结论"
          rows={10}
          className={cn(
            "w-full px-4 py-3 rounded-xl border-2 resize-y",
            "focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-blue-500",
            "dark:bg-slate-800 dark:text-white dark:border-slate-600",
            "font-mono text-sm leading-relaxed",
            "transition-colors",
            disabled && "opacity-60 cursor-not-allowed"
          )}
        />
      </div>

      {/* 字数统计 */}
      <div className="flex justify-between text-sm text-gray-500 dark:text-gray-400">
        <span>字数：{value.length}</span>
        <span>建议最少 50 字</span>
      </div>

      {/* 证明提示 */}
      <div className="p-4 bg-blue-50 dark:bg-blue-900/20 rounded-lg">
        <h4 className="font-medium text-blue-800 dark:text-blue-300 mb-2">
          证明写作提示
        </h4>
        <ul className="text-sm text-blue-700 dark:text-blue-400 space-y-1 list-disc list-inside">
          <li>清晰列出已知条件和需要证明的结论</li>
          <li>每一步推理都要有明确的依据</li>
          <li>可以使用反证法、数学归纳法等经典方法</li>
          <li>最后明确写出&quot;证毕&quot;或类似结束语</li>
        </ul>
      </div>
    </div>
  );
};

export default Proof;
