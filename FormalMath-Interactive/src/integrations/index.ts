/**
 * FormalMath 数据整合模块统一导出
 * 个性化知识图谱 / 学习路径可视化 / 进度追踪
 */

// 个性化知识图谱
export { 
  personalizedGraphService, 
  default as personalizedGraph 
} from './personalizedGraph';
export type { 
  ConceptGraph, 
  ConceptEdge, 
  WeakPointHighlight 
} from './personalizedGraph';

// 学习路径可视化
export { 
  learningPathService, 
  default as learningPath 
} from './learningPath';
export type { 
  LayoutAdjustment, 
  PathTimeEstimate, 
  PathComparison 
} from './learningPath';

// 进度追踪
export { 
  progressTracker, 
  default as progress 
} from './progressTracker';
export type { 
  Notification, 
  ProgressUpdateWithAchievements, 
  RealtimeProgress 
} from './progressTracker';

// 统一服务对象
import { personalizedGraphService } from './personalizedGraph';
import { learningPathService } from './learningPath';
import { progressTracker } from './progressTracker';

export const integrations = {
  graph: personalizedGraphService,
  path: learningPathService,
  progress: progressTracker,
};

export default integrations;
