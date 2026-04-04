import React from 'react';
import { cn } from '../../utils/classNames';

interface ProgressTrackerProps {
  current: number;
  total: number;
  correct: number;
  timeSpent: string;
  streak?: number;
  className?: string;
}

/**
 * 进度追踪组件
 */
export const ProgressTracker: React.FC<ProgressTrackerProps> = ({
  current,
  total,
  correct,
  timeSpent,
  streak = 0,
  className,
}) => {
  const progress = Math.round((current / total) * 100);
  const accuracy = current > 0 ? Math.round((correct / current) * 100) : 0;

  return (
    <div className={cn("bg-white dark:bg-slate-800 rounded-xl p-4 shadow-sm border border-gray-200 dark:border-gray-700", className)}>
      {/* 进度条 */}
      <div className="mb-4">
        <div className="flex justify-between text-sm text-gray-600 dark:text-gray-400 mb-2">
          <span>进度</span>
          <span>{current}/{total} 题</span>
        </div>
        <div className="h-2 bg-gray-200 dark:bg-gray-700 rounded-full overflow-hidden">
          <div
            className="h-full bg-blue-500 rounded-full transition-all duration-500 ease-out"
            style={{ width: `${progress}%` }}
          />
        </div>
      </div>

      {/* 统计信息 */}
      <div className="grid grid-cols-3 gap-4">
        {/* 正确率 */}
        <div className="text-center">
          <div className={cn(
            "text-2xl font-bold",
            accuracy >= 80 ? "text-green-500" : accuracy >= 60 ? "text-yellow-500" : "text-red-500"
          )}>
            {accuracy}%
          </div>
          <div className="text-xs text-gray-500 dark:text-gray-400">正确率</div>
        </div>

        {/* 用时 */}
        <div className="text-center">
          <div className="text-2xl font-bold text-blue-600 dark:text-blue-400">
            {timeSpent}
          </div>
          <div className="text-xs text-gray-500 dark:text-gray-400">用时</div>
        </div>

        {/* 连对 */}
        <div className="text-center">
          <div className="flex items-center justify-center gap-1">
            <span className="text-2xl font-bold text-orange-500">
              {streak}
            </span>
            {streak > 0 && (
              <svg className="w-5 h-5 text-orange-500" fill="currentColor" viewBox="0 0 20 20">
                <path fillRule="evenodd" d="M12.395 2.553a1 1 0 00-1.45-.385c-.345.23-.614.558-.822.88-.214.33-.403.713-.57 1.116-.334.804-.614 1.768-.84 2.734a31.365 31.365 0 00-.613 3.58 2.64 2.64 0 01-.945-1.067c-.328-.68-.398-1.534-.398-2.654A1 1 0 005.05 6.05 6.981 6.981 0 003 11a7 7 0 1011.95-4.95c-.592-.591-.98-.985-1.348-1.467-.363-.476-.724-1.063-1.207-2.03zM12.12 15.12A3 3 0 017 13s.879.5 2.5.5c0-1 .5-4 1.25-4.5.5 1 .786 1.293 1.371 1.879A2.99 2.99 0 0113 13a2.99 2.99 0 01-.879 2.121z" clipRule="evenodd" />
              </svg>
            )}
          </div>
          <div className="text-xs text-gray-500 dark:text-gray-400">连对</div>
        </div>
      </div>

      {/* 进度点 */}
      <div className="flex gap-1 mt-4 justify-center">
        {Array.from({ length: Math.min(total, 20) }).map((_, index) => {
          const isCompleted = index < current;
          const isCorrect = index < correct;
          
          return (
            <div
              key={index}
              className={cn(
                "w-2 h-2 rounded-full transition-colors",
                isCompleted
                  ? isCorrect
                    ? "bg-green-500"
                    : "bg-red-500"
                  : "bg-gray-200 dark:bg-gray-700"
              )}
            />
          );
        })}
        {total > 20 && (
          <span className="text-xs text-gray-400 ml-1">...</span>
        )}
      </div>
    </div>
  );
};

/**
 * 紧凑版进度追踪
 */
export const CompactProgressTracker: React.FC<{
  current: number;
  total: number;
  className?: string;
}> = ({ current, total, className }) => {
  const progress = Math.round((current / total) * 100);

  return (
    <div className={cn("flex items-center gap-3", className)}>
      <div className="flex-1 h-2 bg-gray-200 dark:bg-gray-700 rounded-full overflow-hidden">
        <div
          className="h-full bg-blue-500 rounded-full transition-all duration-300"
          style={{ width: `${progress}%` }}
        />
      </div>
      <span className="text-sm text-gray-600 dark:text-gray-400 whitespace-nowrap">
        {current}/{total}
      </span>
    </div>
  );
};

export default ProgressTracker;
