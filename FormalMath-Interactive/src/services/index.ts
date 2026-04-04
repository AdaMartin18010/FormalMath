/**
 * 服务模块导出
 * Services Module Exports
 */

// 证明策略引擎
export { 
  ProofStrategyEngine, 
  proofStrategyEngine,
} from './proofStrategy';

// Lean4 代码生成器
export { 
  LeanCodeGenerator, 
  leanCodeGenerator,
  LEAN_TEMPLATES,
} from './leanCodeGenerator';

// 证明验证器
export { 
  ProofVerifier, 
  proofVerifier,
} from './proofVerifier';

// 交互式证明构造服务
export { 
  ProofConstructionService,
  proofConstructionService,
} from './proofConstruction';

// 离线学习服务
export {
  offlineService,
  preloadForOffline,
  isContentAvailableOffline,
  type OfflineContent,
  type LearningProgress,
  type OfflineQueueItem,
} from './offlineService';

// 智能提醒服务
export {
  reminderService,
  reminderTemplates,
  type Reminder,
  type ReminderType,
  type ReminderFrequency,
  type ReminderLog,
  type LearningGoal,
  type LearningStats,
} from './reminderService';
