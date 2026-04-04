/**
 * FormalMath React Hooks 统一导出
 * T2.1/T2.2/T3.1 智能学习系统 Hooks
 */

// 认知诊断系统 (T2.1)
export {
  useDiagnosis,
  useDiagnosisHistory,
  useDiagnosisQuestions,
} from './useDiagnosis';

// 评估系统 (T2.2)
export {
  useEvaluation,
  useGrowthCurve,
  useComparisons,
  useBadges,
} from './useEvaluation';

// 自适应学习系统 (T3.1)
export {
  useAdaptive,
  useNodeDetail,
  useLearningStats,
} from './useAdaptive';

// 进度追踪
export {
  useProgressTracking,
  useAchievements,
  useStreak,
  useSkillGrowth,
} from './useProgressTracking';

// 默认导出
export { default } from './useDiagnosis';
