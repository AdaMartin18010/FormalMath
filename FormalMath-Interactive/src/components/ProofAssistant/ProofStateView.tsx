/**
 * 证明状态可视化组件
 * Proof State Visualization Component
 */

import React from 'react';
import type { ProofState, ProofGoal, Hypothesis, VisualizationConfig } from '../../types/proofAssistant';

interface ProofStateViewProps {
  proofState: ProofState;
  onGoalSelect?: (goalId: string) => void;
  onHypothesisClick?: (hypothesis: Hypothesis) => void;
  config?: Partial<VisualizationConfig>;
  className?: string;
}

const defaultConfig: VisualizationConfig = {
  layout: 'tree',
  direction: 'vertical',
  showHypotheses: true,
  showTactics: true,
  colorScheme: 'default',
  nodeSpacing: 20,
  levelSpacing: 40,
};

export const ProofStateView: React.FC<ProofStateViewProps> = ({
  proofState,
  onGoalSelect,
  onHypothesisClick,
  config: userConfig,
  className = '',
}) => {
  const config = { ...defaultConfig, ...userConfig };
  const currentGoal = proofState.goals.find(g => g.id === proofState.currentGoalId);

  const getThemeColors = () => {
    switch (config.colorScheme) {
      case 'dark':
        return {
          bg: 'bg-slate-800',
          text: 'text-slate-200',
          border: 'border-slate-600',
          currentBg: 'bg-blue-900',
          completedBg: 'bg-green-900',
          pendingBg: 'bg-slate-700',
          hypothesisBg: 'bg-slate-700',
        };
      case 'colorful':
        return {
          bg: 'bg-white',
          text: 'text-gray-800',
          border: 'border-indigo-300',
          currentBg: 'bg-gradient-to-r from-blue-500 to-indigo-600',
          completedBg: 'bg-gradient-to-r from-green-400 to-emerald-500',
          pendingBg: 'bg-gradient-to-r from-amber-400 to-orange-500',
          hypothesisBg: 'bg-indigo-50',
        };
      default:
        return {
          bg: 'bg-white',
          text: 'text-gray-800',
          border: 'border-gray-200',
          currentBg: 'bg-blue-50',
          completedBg: 'bg-green-50',
          pendingBg: 'bg-amber-50',
          hypothesisBg: 'bg-gray-50',
        };
    }
  };

  const colors = getThemeColors();

  const renderGoal = (goal: ProofGoal, isCurrent: boolean) => {
    const goalClasses = `
      relative p-4 rounded-lg border-2 transition-all duration-200 cursor-pointer
      ${isCurrent ? `${colors.currentBg} border-blue-500 shadow-lg ring-2 ring-blue-200` : 
        goal.isCompleted ? `${colors.completedBg} border-green-400` : 
        `${colors.pendingBg} ${colors.border} hover:shadow-md`}
    `;

    return (
      <div
        key={goal.id}
        className={goalClasses}
        onClick={() => onGoalSelect?.(goal.id)}
      >
        {/* 目标头部 */}
        <div className="flex items-center justify-between mb-2">
          <span className={`text-xs font-medium px-2 py-1 rounded ${
            isCurrent ? 'bg-blue-200 text-blue-800' :
            goal.isCompleted ? 'bg-green-200 text-green-800' :
            'bg-amber-200 text-amber-800'
          }`}>
            {isCurrent ? '当前目标' : goal.isCompleted ? '已完成' : '待证明'}
          </span>
          {goal.hypotheses.length > 0 && (
            <span className="text-xs text-gray-500">
              {goal.hypotheses.length} 个假设
            </span>
          )}
        </div>

        {/* 假设列表 */}
        {config.showHypotheses && goal.hypotheses.length > 0 && (
          <div className={`mb-3 p-2 rounded ${colors.hypothesisBg}`}>
            <div className="text-xs font-semibold text-gray-500 mb-1">假设</div>
            <div className="space-y-1">
              {goal.hypotheses.map(hyp => (
                <div
                  key={hyp.id}
                  className="text-sm font-mono cursor-pointer hover:bg-white/50 rounded px-1 transition-colors"
                  onClick={(e) => {
                    e.stopPropagation();
                    onHypothesisClick?.(hyp);
                  }}
                >
                  <span className="text-indigo-600 font-semibold">{hyp.name}</span>
                  <span className="text-gray-400 mx-1">:</span>
                  <span className="text-gray-700">{hyp.type}</span>
                </div>
              ))}
            </div>
          </div>
        )}

        {/* 分隔线 */}
        {config.showHypotheses && goal.hypotheses.length > 0 && (
          <div className="border-t border-gray-300 my-2" />
        )}

        {/* 结论 */}
        <div className="text-sm font-mono">
          <span className="text-gray-400">⊢ </span>
          <span className={isCurrent ? 'text-blue-900 font-medium' : colors.text}>
            {goal.conclusion}
          </span>
        </div>
      </div>
    );
  };

  const renderGoalTree = () => {
    const pendingGoals = proofState.goals.filter(g => !g.isCompleted);
    const completedGoals = proofState.goals.filter(g => g.isCompleted);

    return (
      <div className="space-y-4">
        {/* 当前目标 */}
        {currentGoal && (
          <div className="space-y-2">
            <h3 className="text-sm font-semibold text-gray-600">当前目标</h3>
            {renderGoal(currentGoal, true)}
          </div>
        )}

        {/* 待证明目标 */}
        {pendingGoals.length > 1 && (
          <div className="space-y-2">
            <h3 className="text-sm font-semibold text-gray-600">
              其他待证明目标 ({pendingGoals.length - 1})
            </h3>
            <div className="grid gap-2">
              {pendingGoals.filter(g => g.id !== currentGoal?.id).map(goal => 
                renderGoal(goal, false)
              )}
            </div>
          </div>
        )}

        {/* 已完成目标 */}
        {completedGoals.length > 0 && (
          <div className="space-y-2">
            <h3 className="text-sm font-semibold text-gray-600">
              已完成目标 ({completedGoals.length})
            </h3>
            <div className="grid gap-2 opacity-60">
              {completedGoals.map(goal => renderGoal(goal, false))}
            </div>
          </div>
        )}

        {/* 空状态 */}
        {proofState.goals.length === 0 && (
          <div className="text-center py-8 text-gray-500">
            <svg className="w-12 h-12 mx-auto mb-3 text-green-500" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
            </svg>
            <p className="text-lg font-medium">证明完成！</p>
            <p className="text-sm">所有目标已解决</p>
          </div>
        )}
      </div>
    );
  };

  const renderProofContext = () => {
    const { context } = proofState;
    
    if (context.variables.length === 0 && 
        context.constants.length === 0 && 
        context.definitions.length === 0) {
      return null;
    }

    return (
      <div className="mt-6 p-4 bg-gray-50 rounded-lg border border-gray-200">
        <h3 className="text-sm font-semibold text-gray-600 mb-3">证明上下文</h3>
        
        {context.variables.length > 0 && (
          <div className="mb-3">
            <div className="text-xs font-medium text-gray-500 mb-1">变量</div>
            <div className="flex flex-wrap gap-2">
              {context.variables.map((v, i) => (
                <span key={i} className="text-xs font-mono bg-white px-2 py-1 rounded border">
                  {v.name}:{v.type}
                </span>
              ))}
            </div>
          </div>
        )}

        {context.constants.length > 0 && (
          <div className="mb-3">
            <div className="text-xs font-medium text-gray-500 mb-1">常量</div>
            <div className="flex flex-wrap gap-2">
              {context.constants.map((c, i) => (
                <span key={i} className="text-xs font-mono bg-white px-2 py-1 rounded border">
                  {c.name}:{c.type}
                </span>
              ))}
            </div>
          </div>
        )}

        {context.definitions.length > 0 && (
          <div>
            <div className="text-xs font-medium text-gray-500 mb-1">定义</div>
            <div className="space-y-1">
              {context.definitions.map((d, i) => (
                <div key={i} className="text-xs font-mono bg-white px-2 py-1 rounded border">
                  {d.name} {d.params.join(' ')} := {d.body}
                </div>
              ))}
            </div>
          </div>
        )}
      </div>
    );
  };

  return (
    <div className={`${className}`}>
      {renderGoalTree()}
      {renderProofContext()}
    </div>
  );
};

export default ProofStateView;
