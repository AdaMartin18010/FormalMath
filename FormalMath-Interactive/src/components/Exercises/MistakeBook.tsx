import React, { useState } from 'react';
import type { MistakeRecord, ErrorType, MasteryLevel } from '../../types/exercise';
import { 
  ERROR_TYPE_LABELS, 
  MASTERY_LEVEL_LABELS, 
  MASTERY_LEVEL_COLORS 
} from '../../services/mistakeBookService';
import { cn } from '../../utils/classNames';

interface MistakeBookProps {
  mistakes: MistakeRecord[];
  onReview: (mistake: MistakeRecord) => void;
  onDelete?: (mistakeId: string) => void;
  className?: string;
}

/**
 * 错题本组件
 */
export const MistakeBook: React.FC<MistakeBookProps> = ({
  mistakes,
  onReview,
  onDelete,
  className,
}) => {
  const [filter, setFilter] = useState<'all' | 'pending' | 'resolved'>('all');
  const [sortBy, setSortBy] = useState<'date' | 'mastery' | 'errorType'>('date');

  // 过滤错题
  const filteredMistakes = mistakes.filter(mistake => {
    switch (filter) {
      case 'pending':
        return !mistake.isResolved;
      case 'resolved':
        return mistake.isResolved;
      default:
        return true;
    }
  });

  // 排序错题
  const sortedMistakes = [...filteredMistakes].sort((a, b) => {
    switch (sortBy) {
      case 'date':
        return new Date(b.lastWrongAt).getTime() - new Date(a.lastWrongAt).getTime();
      case 'mastery':
        return getMasteryOrder(a.masteryLevel) - getMasteryOrder(b.masteryLevel);
      case 'errorType':
        return a.errorType.localeCompare(b.errorType);
      default:
        return 0;
    }
  });

  return (
    <div className={cn("space-y-4", className)}>
      {/* 过滤器 */}
      <div className="flex flex-wrap gap-3 items-center justify-between">
        <div className="flex gap-2">
          {(['all', 'pending', 'resolved'] as const).map((type) => (
            <button
              key={type}
              onClick={() => setFilter(type)}
              className={cn(
                "px-3 py-1.5 text-sm rounded-full transition-colors",
                filter === type
                  ? "bg-blue-600 text-white"
                  : "bg-gray-100 dark:bg-slate-700 text-gray-700 dark:text-gray-300 hover:bg-gray-200"
              )}
            >
              {type === 'all' ? '全部' : type === 'pending' ? '待复习' : '已解决'}
              <span className="ml-1 opacity-70">
                ({type === 'all' ? mistakes.length : type === 'pending' 
                  ? mistakes.filter(m => !m.isResolved).length 
                  : mistakes.filter(m => m.isResolved).length})
              </span>
            </button>
          ))}
        </div>

        <select
          value={sortBy}
          onChange={(e) => setSortBy(e.target.value as typeof sortBy)}
          className="px-3 py-1.5 text-sm rounded-lg border border-gray-300 dark:border-gray-600 bg-white dark:bg-slate-800"
        >
          <option value="date">按时间</option>
          <option value="mastery">按掌握度</option>
          <option value="errorType">按错误类型</option>
        </select>
      </div>

      {/* 错题列表 */}
      <div className="space-y-3">
        {sortedMistakes.length === 0 ? (
          <div className="text-center py-12 text-gray-500 dark:text-gray-400">
            <svg className="w-16 h-16 mx-auto mb-4 opacity-50" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={1.5} d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
            </svg>
            <p>暂无错题记录</p>
          </div>
        ) : (
          sortedMistakes.map((mistake) => (
            <MistakeCard
              key={mistake.id}
              mistake={mistake}
              onReview={() => onReview(mistake)}
              onDelete={onDelete ? () => onDelete(mistake.id) : undefined}
            />
          ))
        )}
      </div>
    </div>
  );
};

/**
 * 错题卡片
 */
const MistakeCard: React.FC<{
  mistake: MistakeRecord;
  onReview: () => void;
  onDelete?: () => void;
}> = ({ mistake, onReview, onDelete }) => {
  const lastReviewDate = mistake.reviewHistory[mistake.reviewHistory.length - 1]?.timestamp;
  
  return (
    <div className={cn(
      "p-4 rounded-xl border-2 transition-all",
      "bg-white dark:bg-slate-800",
      mistake.isResolved 
        ? "border-green-200 dark:border-green-800" 
        : "border-gray-200 dark:border-gray-700 hover:border-blue-300"
    )}>
      <div className="flex items-start justify-between gap-4">
        <div className="flex-1 min-w-0">
          {/* 头部信息 */}
          <div className="flex flex-wrap items-center gap-2 mb-2">
            <span className={cn(
              "px-2 py-0.5 text-xs rounded-full",
              MASTERY_LEVEL_COLORS[mistake.masteryLevel]
            )}>
              {MASTERY_LEVEL_LABELS[mistake.masteryLevel]}
            </span>
            <span className="px-2 py-0.5 text-xs bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-400 rounded-full">
              {ERROR_TYPE_LABELS[mistake.errorType]}
            </span>
            {mistake.isResolved && (
              <span className="px-2 py-0.5 text-xs bg-green-100 dark:bg-green-900 text-green-700 dark:text-green-300 rounded-full">
                已解决
              </span>
            )}
          </div>

          {/* 错题内容 */}
          <p className="text-gray-800 dark:text-gray-200 text-sm mb-2 truncate">
            题目ID: {mistake.exerciseId}
          </p>

          {/* 错误答案 */}
          <div className="text-sm text-red-600 dark:text-red-400 mb-2">
            错误答案: {formatAnswer(mistake.wrongAnswer)}
          </div>

          {/* 统计信息 */}
          <div className="flex flex-wrap gap-3 text-xs text-gray-500 dark:text-gray-400">
            <span>复习 {mistake.reviewCount} 次</span>
            <span>•</span>
            <span>首次错误: {formatDate(mistake.firstWrongAt)}</span>
            {lastReviewDate && (
              <>
                <span>•</span>
                <span>最近复习: {formatDate(lastReviewDate)}</span>
              </>
            )}
          </div>
        </div>

        {/* 操作按钮 */}
        <div className="flex flex-col gap-2">
          <button
            onClick={onReview}
            className={cn(
              "px-4 py-2 rounded-lg text-sm font-medium transition-colors",
              mistake.isResolved
                ? "bg-gray-100 dark:bg-slate-700 text-gray-700 dark:text-gray-300 hover:bg-gray-200"
                : "bg-blue-600 text-white hover:bg-blue-700"
            )}
          >
            {mistake.isResolved ? '再次复习' : '去复习'}
          </button>
          {onDelete && (
            <button
              onClick={onDelete}
              className="px-4 py-2 rounded-lg text-sm text-red-600 dark:text-red-400 hover:bg-red-50 dark:hover:bg-red-900/20 transition-colors"
            >
              删除
            </button>
          )}
        </div>
      </div>

      {/* 下次复习时间 */}
      {!mistake.isResolved && (
        <div className="mt-3 pt-3 border-t border-gray-100 dark:border-gray-700">
          <p className="text-xs text-gray-500 dark:text-gray-400">
            建议复习时间: {formatDate(mistake.nextReviewDate)}
          </p>
        </div>
      )}
    </div>
  );
};

/**
 * 错题统计概览
 */
export const MistakeOverview: React.FC<{
  totalMistakes: number;
  resolvedMistakes: number;
  pendingReviews: number;
  resolutionRate: number;
  byErrorType: Record<ErrorType, number>;
  byMastery: Record<MasteryLevel, number>;
}> = ({
  totalMistakes,
  resolvedMistakes,
  pendingReviews,
  resolutionRate,
  byMastery,
}) => {
  return (
    <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
      <StatCard
        title="总错题数"
        value={totalMistakes}
        icon="📝"
        color="blue"
      />
      <StatCard
        title="已解决"
        value={resolvedMistakes}
        subtitle={`${resolutionRate}%`}
        icon="✅"
        color="green"
      />
      <StatCard
        title="待复习"
        value={pendingReviews}
        icon="⏰"
        color="orange"
      />
      <StatCard
        title="薄弱项"
        value={byMastery.weak}
        icon="📚"
        color="red"
      />
    </div>
  );
};

/**
 * 统计卡片
 */
const StatCard: React.FC<{
  title: string;
  value: number;
  subtitle?: string;
  icon: string;
  color: 'blue' | 'green' | 'orange' | 'red';
}> = ({ title, value, subtitle, icon, color }) => {
  const colors = {
    blue: 'bg-blue-50 dark:bg-blue-900/20 text-blue-600 dark:text-blue-400',
    green: 'bg-green-50 dark:bg-green-900/20 text-green-600 dark:text-green-400',
    orange: 'bg-orange-50 dark:bg-orange-900/20 text-orange-600 dark:text-orange-400',
    red: 'bg-red-50 dark:bg-red-900/20 text-red-600 dark:text-red-400',
  };

  return (
    <div className="bg-white dark:bg-slate-800 p-4 rounded-xl border border-gray-200 dark:border-gray-700">
      <div className="flex items-center gap-2 mb-2">
        <span className="text-xl">{icon}</span>
        <span className="text-sm text-gray-600 dark:text-gray-400">{title}</span>
      </div>
      <div className={cn("text-2xl font-bold", colors[color])}>
        {value}
        {subtitle && <span className="text-sm ml-1">{subtitle}</span>}
      </div>
    </div>
  );
};

// 辅助函数
function formatAnswer(answer: unknown): string {
  if (typeof answer === 'string') return answer;
  if (typeof answer === 'number') return answer.toString();
  if (typeof answer === 'boolean') return answer ? '是' : '否';
  if (Array.isArray(answer)) return answer.join('、');
  return JSON.stringify(answer);
}

function formatDate(dateString: string): string {
  const date = new Date(dateString);
  const now = new Date();
  const diffDays = Math.floor((now.getTime() - date.getTime()) / (1000 * 60 * 60 * 24));
  
  if (diffDays === 0) return '今天';
  if (diffDays === 1) return '昨天';
  if (diffDays < 7) return `${diffDays}天前`;
  if (diffDays < 30) return `${Math.floor(diffDays / 7)}周前`;
  
  return date.toLocaleDateString('zh-CN');
}

function getMasteryOrder(level: MasteryLevel): number {
  const order: Record<MasteryLevel, number> = {
    weak: 0,
    developing: 1,
    mastered: 2,
    forgotten: 3,
  };
  return order[level];
}

export default MistakeBook;
