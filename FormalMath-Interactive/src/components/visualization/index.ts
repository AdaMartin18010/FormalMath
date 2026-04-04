/**
 * FormalMath 可视化组件统一导出
 */

export { PersonalizedGraph } from './PersonalizedGraph';
export { LearningPathView } from './LearningPathView';
export { ProgressDashboard } from './ProgressDashboard';

import { PersonalizedGraph as PG } from './PersonalizedGraph';
import { LearningPathView as LPV } from './LearningPathView';
import { ProgressDashboard as PD } from './ProgressDashboard';

export default {
  PersonalizedGraph: PG,
  LearningPathView: LPV,
  ProgressDashboard: PD,
};
