// ==================== 练习系统组件导出 ====================

export { SingleChoice } from './SingleChoice';
export { MultipleChoice } from './MultipleChoice';
export { FillBlank } from './FillBlank';
export { Calculation } from './Calculation';
export { TrueFalse } from './TrueFalse';
export { Proof } from './Proof';

export { ExerciseFeedback } from './ExerciseFeedback';
export { HintPanel } from './HintPanel';
export { SolutionPanel } from './SolutionPanel';
export { ProgressTracker, CompactProgressTracker } from './ProgressTracker';
export { MistakeBook, MistakeOverview } from './MistakeBook';

// ==================== 主练习组件 ====================

import React, { useMemo } from 'react';
import type { Exercise, ExerciseComponentProps } from '../../types/exercise';
import { SingleChoice } from './SingleChoice';
import { MultipleChoice } from './MultipleChoice';
import { FillBlank } from './FillBlank';
import { Calculation } from './Calculation';
import { TrueFalse } from './TrueFalse';
import { Proof } from './Proof';

/**
 * 根据题型获取对应组件
 */
export function getExerciseComponent(type: Exercise['type']) {
  switch (type) {
    case 'single_choice':
      return SingleChoice;
    case 'multiple_choice':
      return MultipleChoice;
    case 'fill_blank':
      return FillBlank;
    case 'calculation':
      return Calculation;
    case 'true_false':
      return TrueFalse;
    case 'proof':
      return Proof;
    default:
      return SingleChoice;
  }
}

/**
 * 通用练习组件
 * 根据题型自动渲染对应组件
 */
export const ExerciseComponent: React.FC<ExerciseComponentProps> = (props) => {
  const Component = useMemo(() => getExerciseComponent(props.exercise.type), [props.exercise.type]);
  return <Component {...props} />;
};

/**
 * 练习类型标签
 */
export const ExerciseTypeLabel: React.FC<{ type: Exercise['type'] }> = ({ type }) => {
  const labels: Record<Exercise['type'], { label: string; color: string }> = {
    single_choice: { label: '单选题', color: 'bg-blue-100 text-blue-800' },
    multiple_choice: { label: '多选题', color: 'bg-purple-100 text-purple-800' },
    fill_blank: { label: '填空题', color: 'bg-green-100 text-green-800' },
    calculation: { label: '计算题', color: 'bg-orange-100 text-orange-800' },
    proof: { label: '证明题', color: 'bg-red-100 text-red-800' },
    matching: { label: '配对题', color: 'bg-yellow-100 text-yellow-800' },
    ordering: { label: '排序题', color: 'bg-pink-100 text-pink-800' },
    true_false: { label: '判断题', color: 'bg-gray-100 text-gray-800' },
  };

  const { label, color } = labels[type] || labels.single_choice;

  return (
    <span className={`px-2 py-0.5 text-xs rounded-full ${color}`}>
      {label}
    </span>
  );
};

/**
 * 难度标签
 */
export const DifficultyLabel: React.FC<{ level: Exercise['difficulty'] }> = ({ level }) => {
  const config = {
    beginner: { label: '入门', stars: 1, color: 'text-green-500' },
    intermediate: { label: '进阶', stars: 2, color: 'text-blue-500' },
    advanced: { label: '高级', stars: 3, color: 'text-orange-500' },
    expert: { label: '专家', stars: 4, color: 'text-red-500' },
  };

  const { label, stars, color } = config[level];

  return (
    <span className="flex items-center gap-1">
      <span className="text-xs text-gray-500">{label}</span>
      <span className={color}>
        {'★'.repeat(stars)}
      </span>
    </span>
  );
};

export default ExerciseComponent;
