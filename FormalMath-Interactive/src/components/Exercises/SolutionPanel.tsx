import React from 'react';
import type { Exercise } from '../../types/exercise';

interface SolutionPanelProps {
  exercise: Exercise;
  isVisible: boolean;
  onClose?: () => void;
}

/**
 * 解答面板组件
 */
export const SolutionPanel: React.FC<SolutionPanelProps> = ({
  exercise,
  isVisible,
  onClose,
}) => {
  if (!isVisible) return null;

  return (
    <div className="mt-6 animate-in fade-in slide-in-from-bottom-4">
      <div className="bg-blue-50 dark:bg-blue-900/20 rounded-xl p-6 border-2 border-blue-200 dark:border-blue-800">
        {/* 标题 */}
        <div className="flex items-center justify-between mb-4">
          <div className="flex items-center gap-2">
            <svg className="w-5 h-5 text-blue-600 dark:text-blue-400" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12h6m-6 4h6m2 5H7a2 2 0 01-2-2V5a2 2 0 012-2h5.586a1 1 0 01.707.293l5.414 5.414a1 1 0 01.293.707V19a2 2 0 01-2 2z" />
            </svg>
            <h3 className="text-lg font-bold text-blue-900 dark:text-blue-300">
              详细解析
            </h3>
          </div>
          {onClose && (
            <button
              onClick={onClose}
              className="text-blue-600 dark:text-blue-400 hover:text-blue-800 dark:hover:text-blue-200"
            >
              <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          )}
        </div>

        {/* 解答内容 */}
        <div 
          className="prose dark:prose-invert max-w-none text-gray-800 dark:text-gray-200"
          dangerouslySetInnerHTML={{ __html: exercise.solution }}
        />

        {/* 关键知识点 */}
        {exercise.keyPoints.length > 0 && (
          <div className="mt-6 pt-4 border-t border-blue-200 dark:border-blue-800">
            <h4 className="text-sm font-semibold text-blue-800 dark:text-blue-400 mb-2">
              关键知识点
            </h4>
            <div className="flex flex-wrap gap-2">
              {exercise.keyPoints.map((point, index) => (
                <span
                  key={index}
                  className="px-3 py-1 bg-blue-100 dark:bg-blue-800 text-blue-800 dark:text-blue-200 text-sm rounded-full"
                >
                  {point}
                </span>
              ))}
            </div>
          </div>
        )}

        {/* 常见错误 */}
        {exercise.commonMistakes.length > 0 && (
          <div className="mt-4 pt-4 border-t border-blue-200 dark:border-blue-800">
            <h4 className="text-sm font-semibold text-red-700 dark:text-red-400 mb-2 flex items-center gap-1">
              <svg className="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
              </svg>
              常见错误
            </h4>
            <ul className="list-disc list-inside text-sm text-red-600 dark:text-red-400 space-y-1">
              {exercise.commonMistakes.map((mistake, index) => (
                <li key={index}>{mistake}</li>
              ))}
            </ul>
          </div>
        )}

        {/* 相关概念 */}
        {exercise.relatedConcepts.length > 0 && (
          <div className="mt-4 pt-4 border-t border-blue-200 dark:border-blue-800">
            <h4 className="text-sm font-semibold text-blue-800 dark:text-blue-400 mb-2">
              相关概念
            </h4>
            <div className="flex flex-wrap gap-2">
              {exercise.relatedConcepts.map((concept, index) => (
                <a
                  key={index}
                  href={`#/concept/${encodeURIComponent(concept)}`}
                  className="text-sm text-blue-600 dark:text-blue-400 hover:underline"
                >
                  {concept}
                </a>
              ))}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default SolutionPanel;
