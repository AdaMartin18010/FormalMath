/**
 * FormalMath 数据分析系统 API
 * 学习进度 / 概念掌握 / 学习效率 / 知识网络 / 预测分析
 */

import { get, post } from './client';
import type {
  LearningProgressData,
  MasteryHeatmapData,
  EfficiencyAnalysisData,
  KnowledgeNetworkData,
  PredictionData,
  AnalyticsRequest,
  AnalyticsResponse,
  ExportAnalyticsRequest,
  TimeRange,
} from '@types/analytics';

// ==================== API 端点配置 ====================

const ANALYTICS_BASE = '/analytics';

// ==================== 学习进度仪表板 API ====================

/**
 * 获取学习进度数据
 */
export async function getLearningProgress(
  userId: string,
  timeRange: TimeRange = 'month'
): Promise<AnalyticsResponse<LearningProgressData>> {
  return get<LearningProgressData>(
    `${ANALYTICS_BASE}/progress/${userId}`,
    { params: { timeRange } }
  );
}

/**
 * 获取进度趋势数据
 */
export async function getProgressTrends(
  userId: string,
  days: number = 30
): Promise<AnalyticsResponse<LearningProgressData['trends']>> {
  return get<LearningProgressData['trends']>(
    `${ANALYTICS_BASE}/progress/${userId}/trends`,
    { params: { days } }
  );
}

/**
 * 更新学习目标
 */
export async function updateLearningGoals(
  userId: string,
  goals: LearningProgressData['goals']
): Promise<AnalyticsResponse<LearningProgressData['goals']>> {
  return post<LearningProgressData['goals']>(
    `${ANALYTICS_BASE}/progress/${userId}/goals`,
    { goals }
  );
}

// ==================== 概念掌握热力图 API ====================

/**
 * 获取概念掌握热力图数据
 */
export async function getMasteryHeatmap(
  userId: string,
  categoryId?: string
): Promise<AnalyticsResponse<MasteryHeatmapData>> {
  const params: Record<string, string> = {};
  if (categoryId) params.category = categoryId;
  
  return get<MasteryHeatmapData>(
    `${ANALYTICS_BASE}/heatmap/${userId}`,
    { params }
  );
}

/**
 * 获取分类列表
 */
export async function getHeatmapCategories(
  userId: string
): Promise<AnalyticsResponse<MasteryHeatmapData['categories']>> {
  return get<MasteryHeatmapData['categories']>(
    `${ANALYTICS_BASE}/heatmap/${userId}/categories`
  );
}

/**
 * 获取需要复习的概念
 */
export async function getReviewRecommendations(
  userId: string,
  limit: number = 10
): Promise<AnalyticsResponse<string[]>> {
  return get<string[]>(
    `${ANALYTICS_BASE}/heatmap/${userId}/review`,
    { params: { limit } }
  );
}

// ==================== 学习效率分析 API ====================

/**
 * 获取学习效率分析数据
 */
export async function getEfficiencyAnalysis(
  userId: string,
  timeRange: TimeRange = 'month'
): Promise<AnalyticsResponse<EfficiencyAnalysisData>> {
  return get<EfficiencyAnalysisData>(
    `${ANALYTICS_BASE}/efficiency/${userId}`,
    { params: { timeRange } }
  );
}

/**
 * 获取最佳学习时间推荐
 */
export async function getOptimalStudyTimes(
  userId: string
): Promise<AnalyticsResponse<EfficiencyAnalysisData['timeDistribution']['byHour']>> {
  return get<EfficiencyAnalysisData['timeDistribution']['byHour']>(
    `${ANALYTICS_BASE}/efficiency/${userId}/optimal-times`
  );
}

/**
 * 获取学习效率建议
 */
export async function getEfficiencyRecommendations(
  userId: string,
  count: number = 5
): Promise<AnalyticsResponse<EfficiencyAnalysisData['recommendations']>> {
  return get<EfficiencyAnalysisData['recommendations']>(
    `${ANALYTICS_BASE}/efficiency/${userId}/recommendations`,
    { params: { count } }
  );
}

// ==================== 知识网络分析 API ====================

/**
 * 获取知识网络数据
 */
export async function getKnowledgeNetwork(
  userId: string,
  depth: number = 2
): Promise<AnalyticsResponse<KnowledgeNetworkData>> {
  return get<KnowledgeNetworkData>(
    `${ANALYTICS_BASE}/network/${userId}`,
    { params: { depth } }
  );
}

/**
 * 获取知识社区（聚类）
 */
export async function getKnowledgeCommunities(
  userId: string
): Promise<AnalyticsResponse<KnowledgeNetworkData['communities']>> {
  return get<KnowledgeNetworkData['communities']>(
    `${ANALYTICS_BASE}/network/${userId}/communities`
  );
}

/**
 * 获取关键概念（桥接概念）
 */
export async function getBridgeConcepts(
  userId: string,
  limit: number = 10
): Promise<AnalyticsResponse<KnowledgeNetworkData['bridges']>> {
  return get<KnowledgeNetworkData['bridges']>(
    `${ANALYTICS_BASE}/network/${userId}/bridges`,
    { params: { limit } }
  );
}

/**
 * 获取知识覆盖度统计
 */
export async function getNetworkStats(
  userId: string
): Promise<AnalyticsResponse<KnowledgeNetworkData['networkStats']>> {
  return get<KnowledgeNetworkData['networkStats']>(
    `${ANALYTICS_BASE}/network/${userId}/stats`
  );
}

// ==================== 预测分析 API ====================

/**
 * 获取预测分析数据
 */
export async function getPredictions(
  userId: string
): Promise<AnalyticsResponse<PredictionData>> {
  return get<PredictionData>(
    `${ANALYTICS_BASE}/prediction/${userId}`
  );
}

/**
 * 获取完成时间预测
 */
export async function getCompletionPrediction(
  userId: string,
  targetConcepts?: number
): Promise<AnalyticsResponse<PredictionData['completionPrediction']>> {
  const params: Record<string, string | number> = {};
  if (targetConcepts) params.target = targetConcepts;
  
  return get<PredictionData['completionPrediction']>(
    `${ANALYTICS_BASE}/prediction/${userId}/completion`,
    { params }
  );
}

/**
 * 获取性能预测
 */
export async function getPerformanceForecast(
  userId: string
): Promise<AnalyticsResponse<PredictionData['performanceForecast']>> {
  return get<PredictionData['performanceForecast']>(
    `${ANALYTICS_BASE}/prediction/${userId}/forecast`
  );
}

/**
 * 获取风险分析
 */
export async function getRiskAnalysis(
  userId: string
): Promise<AnalyticsResponse<PredictionData['riskAnalysis']>> {
  return get<PredictionData['riskAnalysis']>(
    `${ANALYTICS_BASE}/prediction/${userId}/risk`
  );
}

/**
 * 获取自适应建议
 */
export async function getAdaptiveSuggestions(
  userId: string
): Promise<AnalyticsResponse<PredictionData['adaptiveSuggestions']>> {
  return get<PredictionData['adaptiveSuggestions']>(
    `${ANALYTICS_BASE}/prediction/${userId}/suggestions`
  );
}

// ==================== 综合报表 API ====================

/**
 * 获取综合学习分析报告
 */
export async function getComprehensiveReport(
  userId: string,
  timeRange: TimeRange = 'month'
): Promise<AnalyticsResponse<{
  progress: LearningProgressData;
  heatmap: MasteryHeatmapData;
  efficiency: EfficiencyAnalysisData;
  network: KnowledgeNetworkData;
  prediction: PredictionData;
}>> {
  return get<{
    progress: LearningProgressData;
    heatmap: MasteryHeatmapData;
    efficiency: EfficiencyAnalysisData;
    network: KnowledgeNetworkData;
    prediction: PredictionData;
  }>(
    `${ANALYTICS_BASE}/report/${userId}`,
    { params: { timeRange } }
  );
}

/**
 * 导出分析报告
 */
export async function exportAnalyticsReport(
  request: ExportAnalyticsRequest
): Promise<Blob> {
  const response = await fetch(
    `${import.meta.env.VITE_API_BASE_URL || '/api'}${ANALYTICS_BASE}/export`,
    {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Authorization': `Bearer ${localStorage.getItem('auth_token') || ''}`,
      },
      body: JSON.stringify(request),
    }
  );
  
  if (!response.ok) {
    throw new Error('导出失败');
  }
  
  return response.blob();
}

// ==================== API 对象导出 ====================

export const analyticsApi = {
  // 学习进度
  getLearningProgress,
  getProgressTrends,
  updateLearningGoals,
  
  // 热力图
  getMasteryHeatmap,
  getHeatmapCategories,
  getReviewRecommendations,
  
  // 效率分析
  getEfficiencyAnalysis,
  getOptimalStudyTimes,
  getEfficiencyRecommendations,
  
  // 知识网络
  getKnowledgeNetwork,
  getKnowledgeCommunities,
  getBridgeConcepts,
  getNetworkStats,
  
  // 预测分析
  getPredictions,
  getCompletionPrediction,
  getPerformanceForecast,
  getRiskAnalysis,
  getAdaptiveSuggestions,
  
  // 综合报表
  getComprehensiveReport,
  exportAnalyticsReport,
};

export default analyticsApi;
