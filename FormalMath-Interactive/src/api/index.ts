/**
 * FormalMath API 模块统一导出
 * T2.1/T2.2/T3.1 智能学习系统 API
 */

// 客户端
export { apiClient, TokenManager, ApiClientError } from './client';
export type { RequestOptions } from './client';

// 认知诊断系统 API (T2.1)
export { diagnosisApi, default as diagnosis } from './diagnosis';
export type { 
  DiagnosisQuestion, 
  DiagnosisComparison 
} from './diagnosis';

// 评估系统 API (T2.2)
export { evaluationApi, default as evaluation } from './evaluation';
export type { 
  EvaluationHistoryItem, 
  RadarData, 
  ProgressAnalysis 
} from './evaluation';

// 自适应学习系统 API (T3.1)
export { adaptiveApi, default as adaptive } from './adaptive';
export type { 
  PathGenerationOptions, 
  BatchProgressResponse,
  PathAdjustmentOptions,
  NodeCompletionData,
  LearningStats,
  PathPreview
} from './adaptive';

// 统一 API 对象
import { diagnosisApi } from './diagnosis';
import { evaluationApi } from './evaluation';
import { adaptiveApi } from './adaptive';

export const api = {
  diagnosis: diagnosisApi,
  evaluation: evaluationApi,
  adaptive: adaptiveApi,
};

export default api;
