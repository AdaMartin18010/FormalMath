import React, { useState, useCallback } from 'react';
import { useExercise } from '../../hooks/useExercise';
import {
  ExerciseComponent,
  ExerciseTypeLabel,
  DifficultyLabel,
  ExerciseFeedback,
  HintPanel,
  SolutionPanel,
  ProgressTracker,
} from '../../components/Exercises';
import { sampleExercises } from './sampleData';
import type { ValidationResult } from '../../types/exercise';
import { cn } from '../../utils/classNames';

/**
 * 练习页面
 */
const ExercisePage: React.FC = () => {
  const userId = 'demo-user'; // 实际应用中从认证系统获取
  const [currentIndex, setCurrentIndex] = useState(0);
  const [completedResults, setCompletedResults] = useState<ValidationResult[]>([]);
  const [sessionStartTime] = useState(Date.now());

  const {
    exercise,
    userAnswer,
    validationResult,
    hints,
    revealedHintsCount,
    isSubmitting,
    showSolution,
    formattedTime,
    attempts,
    hasMoreHints,
    loadExercise,
    setAnswer,
    submitAnswer,
    requestHint,
    showSolution: handleShowSolution,
    skipExercise,
    resetExercise,
    settings,
  } = useExercise({
    userId,
    settings: {
      immediateFeedback: true,
      showHintButton: true,
      showSolutionButton: true,
    },
  });

  // 加载当前题目
  React.useEffect(() => {
    if (!exercise && sampleExercises.length > 0) {
      loadExercise(sampleExercises[currentIndex]);
    }
  }, [exercise, currentIndex, loadExercise]);

  // 处理答案提交完成
  const handleComplete = useCallback((result: ValidationResult, timeSpent: number) => {
    setCompletedResults(prev => [...prev, result]);
  }, []);

  // 下一题
  const handleNext = useCallback(() => {
    if (currentIndex < sampleExercises.length - 1) {
      setCurrentIndex(prev => prev + 1);
      loadExercise(sampleExercises[currentIndex + 1]);
    } else {
      // 练习完成
      alert('恭喜完成所有练习！');
    }
  }, [currentIndex, loadExercise]);

  // 如果题目未加载，显示加载状态
  if (!exercise) {
    return (
      <div className="min-h-screen flex items-center justify-center">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-500"></div>
      </div>
    );
  }

  const isAnswered = validationResult !== null;
  const correctCount = completedResults.filter(r => r.isCorrect).length;

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-slate-900 py-8 px-4">
      <div className="max-w-6xl mx-auto">
        {/* 页面标题 */}
        <div className="mb-6">
          <h1 className="text-3xl font-bold text-gray-900 dark:text-white mb-2">
            交互式练习
          </h1>
          <p className="text-gray-600 dark:text-gray-400">
            通过练习巩固数学知识，提升解题能力
          </p>
        </div>

        {/* 进度追踪 */}
        <div className="mb-6">
          <ProgressTracker
            current={currentIndex}
            total={sampleExercises.length}
            correct={correctCount}
            timeSpent={formattedTime}
            streak={0}
          />
        </div>

        <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
          {/* 左侧：题目区域 */}
          <div className="lg:col-span-2 space-y-6">
            {/* 题目卡片 */}
            <div className="bg-white dark:bg-slate-800 rounded-2xl shadow-sm border border-gray-200 dark:border-gray-700 overflow-hidden">
              {/* 题目头部 */}
              <div className="px-6 py-4 border-b border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-slate-800/50">
                <div className="flex items-center justify-between flex-wrap gap-2">
                  <div className="flex items-center gap-3">
                    <ExerciseTypeLabel type={exercise.type} />
                    <DifficultyLabel level={exercise.difficulty} />
                  </div>
                  <div className="flex items-center gap-4 text-sm text-gray-500 dark:text-gray-400">
                    <span>分值: {exercise.points}分</span>
                    <span>预计: {exercise.estimatedTime}分钟</span>
                  </div>
                </div>
              </div>

              {/* 题目内容 */}
              <div className="p-6">
                <h2 className="text-xl font-semibold text-gray-900 dark:text-white mb-4">
                  {exercise.title}
                </h2>

                {/* 反馈区域 */}
                {validationResult && (
                  <ExerciseFeedback
                    result={validationResult}
                    onShowSolution={handleShowSolution}
                    onContinue={validationResult.isCorrect ? handleNext : resetExercise}
                  />
                )}

                {/* 题目主体 */}
                <ExerciseComponent
                  exercise={exercise}
                  userAnswer={userAnswer}
                  onAnswer={setAnswer}
                  onRequestHint={requestHint}
                  onShowSolution={handleShowSolution}
                  onSkip={skipExercise}
                  disabled={isAnswered}
                  settings={settings}
                />

                {/* 解答面板 */}
                <SolutionPanel
                  exercise={exercise}
                  isVisible={showSolution}
                />
              </div>

              {/* 操作按钮 */}
              <div className="px-6 py-4 border-t border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-slate-800/50">
                <div className="flex justify-between items-center">
                  <button
                    onClick={skipExercise}
                    disabled={isAnswered}
                    className={cn(
                      "px-4 py-2 text-gray-600 dark:text-gray-400 hover:text-gray-800 transition-colors",
                      isAnswered && "opacity-50 cursor-not-allowed"
                    )}
                  >
                    跳过
                  </button>

                  <div className="flex gap-3">
                    {!isAnswered ? (
                      <button
                        onClick={submitAnswer}
                        disabled={userAnswer === undefined || isSubmitting}
                        className={cn(
                          "px-6 py-2.5 rounded-xl font-medium transition-colors",
                          "bg-blue-600 text-white hover:bg-blue-700",
                          (userAnswer === undefined || isSubmitting) && "opacity-50 cursor-not-allowed"
                        )}
                      >
                        {isSubmitting ? '提交中...' : '提交答案'}
                      </button>
                    ) : (
                      <button
                        onClick={handleNext}
                        className="px-6 py-2.5 rounded-xl font-medium bg-green-600 text-white hover:bg-green-700 transition-colors"
                      >
                        下一题
                      </button>
                    )}
                  </div>
                </div>
              </div>
            </div>
          </div>

          {/* 右侧：侧边栏 */}
          <div className="space-y-6">
            {/* 提示面板 */}
            <div className="bg-white dark:bg-slate-800 rounded-2xl shadow-sm border border-gray-200 dark:border-gray-700 p-6">
              <HintPanel
                hints={hints}
                revealedCount={revealedHintsCount}
                maxHints={exercise.maxHints}
                onRequestHint={requestHint}
                disabled={isAnswered}
              />
            </div>

            {/* 题目信息 */}
            <div className="bg-white dark:bg-slate-800 rounded-2xl shadow-sm border border-gray-200 dark:border-gray-700 p-6">
              <h3 className="font-semibold text-gray-900 dark:text-white mb-4">
                题目信息
              </h3>
              <div className="space-y-3 text-sm">
                <div className="flex justify-between">
                  <span className="text-gray-500 dark:text-gray-400">学科</span>
                  <span className="text-gray-900 dark:text-white">{exercise.subject}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-500 dark:text-gray-400">主题</span>
                  <span className="text-gray-900 dark:text-white">{exercise.topic}</span>
                </div>
                {exercise.subtopic && (
                  <div className="flex justify-between">
                    <span className="text-gray-500 dark:text-gray-400">子主题</span>
                    <span className="text-gray-900 dark:text-white">{exercise.subtopic}</span>
                  </div>
                )}
                <div className="pt-3 border-t border-gray-200 dark:border-gray-700">
                  <span className="text-gray-500 dark:text-gray-400 block mb-2">标签</span>
                  <div className="flex flex-wrap gap-2">
                    {exercise.tags.map((tag, index) => (
                      <span
                        key={index}
                        className="px-2 py-1 bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-300 rounded text-xs"
                      >
                        {tag}
                      </span>
                    ))}
                  </div>
                </div>
              </div>
            </div>

            {/* 尝试次数 */}
            {attempts > 0 && (
              <div className="bg-yellow-50 dark:bg-yellow-900/20 rounded-2xl p-4 border border-yellow-200 dark:border-yellow-800">
                <p className="text-sm text-yellow-800 dark:text-yellow-300">
                  尝试次数: {attempts}
                </p>
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

export default ExercisePage;
