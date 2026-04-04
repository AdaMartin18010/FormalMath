import React, { useState } from 'react';
import { useMistakeBook } from '../../hooks/useExercise';
import { MistakeBook, MistakeOverview } from '../../components/Exercises';
import type { MistakeRecord } from '../../types/exercise';

/**
 * 错题本页面
 */
const MistakeBookPage: React.FC = () => {
  const userId = 'demo-user';
  const {
    mistakes,
    overview,
    loading,
    recordReview,
    deleteMistake,
    errorTypeLabels,
    masteryLabels,
  } = useMistakeBook(userId);

  const [selectedMistake, setSelectedMistake] = useState<MistakeRecord | null>(null);

  // 处理复习
  const handleReview = (mistake: MistakeRecord) => {
    setSelectedMistake(mistake);
    // 这里可以导航到练习页面进行复习
    console.log('开始复习错题:', mistake.id);
  };

  // 处理删除
  const handleDelete = (mistakeId: string) => {
    if (confirm('确定要删除这条错题记录吗？')) {
      deleteMistake(mistakeId);
    }
  };

  // 模拟复习结果
  const handleSimulateReview = (isCorrect: boolean) => {
    if (selectedMistake) {
      recordReview(selectedMistake.id, isCorrect, 120, 1);
      setSelectedMistake(null);
    }
  };

  if (loading) {
    return (
      <div className="min-h-screen flex items-center justify-center">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-500"></div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-slate-900 py-8 px-4">
      <div className="max-w-6xl mx-auto">
        {/* 页面标题 */}
        <div className="mb-6">
          <h1 className="text-3xl font-bold text-gray-900 dark:text-white mb-2">
            错题本
          </h1>
          <p className="text-gray-600 dark:text-gray-400">
            管理您的错题，定期复习巩固知识
          </p>
        </div>

        {/* 统计概览 */}
        {overview && (
          <div className="mb-6">
            <MistakeOverview {...overview} />
          </div>
        )}

        {/* 错误类型分布 */}
        {overview && (
          <div className="mb-6 bg-white dark:bg-slate-800 rounded-2xl p-6 border border-gray-200 dark:border-gray-700">
            <h2 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
              错误类型分布
            </h2>
            <div className="grid grid-cols-2 md:grid-cols-4 lg:grid-cols-7 gap-3">
              {Object.entries(overview.byErrorType).map(([type, count]) => (
                <div
                  key={type}
                  className="text-center p-3 bg-gray-50 dark:bg-slate-700 rounded-lg"
                >
                  <div className="text-2xl font-bold text-gray-800 dark:text-white">
                    {count}
                  </div>
                  <div className="text-xs text-gray-500 dark:text-gray-400 mt-1">
                    {errorTypeLabels[type as keyof typeof errorTypeLabels]}
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* 掌握度分布 */}
        {overview && (
          <div className="mb-6 bg-white dark:bg-slate-800 rounded-2xl p-6 border border-gray-200 dark:border-gray-700">
            <h2 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
              掌握度分布
            </h2>
            <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
              {Object.entries(overview.byMastery).map(([level, count]) => (
                <div
                  key={level}
                  className="text-center p-4 bg-gray-50 dark:bg-slate-700 rounded-lg"
                >
                  <div className="text-3xl font-bold text-gray-800 dark:text-white">
                    {count}
                  </div>
                  <div className="text-sm text-gray-500 dark:text-gray-400 mt-1">
                    {masteryLabels[level as keyof typeof masteryLabels]}
                  </div>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* 错题列表 */}
        <div className="bg-white dark:bg-slate-800 rounded-2xl p-6 border border-gray-200 dark:border-gray-700">
          <div className="flex items-center justify-between mb-4">
            <h2 className="text-lg font-semibold text-gray-900 dark:text-white">
              错题列表
            </h2>
            {mistakes.length > 0 && (
              <button
                onClick={() => {
                  if (confirm('确定要清空所有错题记录吗？此操作不可撤销。')) {
                    // 清空所有错题
                    mistakes.forEach(m => deleteMistake(m.id));
                  }
                }}
                className="text-sm text-red-600 dark:text-red-400 hover:text-red-800"
              >
                清空所有记录
              </button>
            )}
          </div>

          <MistakeBook
            mistakes={mistakes}
            onReview={handleReview}
            onDelete={handleDelete}
          />
        </div>

        {/* 复习模拟弹窗（仅用于演示） */}
        {selectedMistake && (
          <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50 p-4">
            <div className="bg-white dark:bg-slate-800 rounded-2xl p-6 max-w-md w-full">
              <h3 className="text-xl font-bold text-gray-900 dark:text-white mb-4">
                模拟复习
              </h3>
              <p className="text-gray-600 dark:text-gray-400 mb-4">
                练习ID: {selectedMistake.exerciseId}
              </p>
              <p className="text-sm text-gray-500 dark:text-gray-500 mb-6">
                这次复习结果如何？
              </p>
              <div className="flex gap-3">
                <button
                  onClick={() => handleSimulateReview(true)}
                  className="flex-1 px-4 py-2 bg-green-600 text-white rounded-lg hover:bg-green-700"
                >
                  答对了
                </button>
                <button
                  onClick={() => handleSimulateReview(false)}
                  className="flex-1 px-4 py-2 bg-red-600 text-white rounded-lg hover:bg-red-700"
                >
                  答错了
                </button>
                <button
                  onClick={() => setSelectedMistake(null)}
                  className="px-4 py-2 border border-gray-300 dark:border-gray-600 rounded-lg"
                >
                  取消
                </button>
              </div>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default MistakeBookPage;
