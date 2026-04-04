/**
 * FormalMath 可视化组件统一导出
 */

export { PersonalizedGraph } from './PersonalizedGraph';
export { LearningPathView } from './LearningPathView';
export { ProgressDashboard } from './ProgressDashboard';

export default {
  PersonalizedGraph: require('./PersonalizedGraph').default,
  LearningPathView: require('./LearningPathView').default,
  ProgressDashboard: require('./ProgressDashboard').default,
};
