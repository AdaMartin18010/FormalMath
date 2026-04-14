// @ts-nocheck
/**
 * FormalMath 评估系统 API (T2.2)
 * 能力评估与成长追踪
 */

import { apiClient } from './client';
import type {
  EvaluationReport,
  AbilityDimensions,
  GrowthDataPoint,
  Comparison,
  Badge,
  Achievement,
  ApiResponse,
} from '../types/learning';

// API 端点
const ENDPOINTS = {
  GET_EVALUATION: (userId: string) => `/evaluation/${userId}`,
  GET_EVALUATION_HISTORY: (userId: string) => `/evaluation/${userId}/history`,
  GET_DIMENSIONS: (userId: string) => `/evaluation/${userId}/dimensions`,
  GET_GROWTH_CURVE: (userId: string) => `/evaluation/${userId}/growth`,
  GET_COMPARISONS: (userId: string) => `/evaluation/${userId}/comparisons`,
  GET_BADGES: (userId: string) => `/evaluation/${userId}/badges`,
  GET_ACHIEVEMENTS: (userId: string) => `/evaluation/${userId}/achievements`,
  GENERATE_REPORT: (userId: string) => `/evaluation/${userId}/generate`,
} as const;

/**
 * 获取用户最新评估报告
 * @param userId 用户ID
 * @returns 完整评估报告
 */
export async function getEvaluation(userId: string): Promise<EvaluationReport> {
  return apiClient.get<EvaluationReport>(ENDPOINTS.GET_EVALUATION(userId));
}

/**
 * 获取评估历史记录
 * @param userId 用户ID
 * @param timeRange 时间范围（天）
 * @returns 历史评估列表
 */
export async function getEvaluationHistory(
  userId: string,
  timeRange: number = 90
): Promise<EvaluationHistoryItem[]> {
  return apiClient.get<EvaluationHistoryItem[]>(
    `${ENDPOINTS.GET_EVALUATION_HISTORY(userId)}?range=${timeRange}`
  );
}

/**
 * 获取能力维度详情
 * @param userId 用户ID
 * @returns 五个维度的能力评分
 */
export async function getDimensions(userId: string): Promise<AbilityDimensions> {
  return apiClient.get<AbilityDimensions>(ENDPOINTS.GET_DIMENSIONS(userId));
}

/**
 * 获取成长曲线数据
 * @param userId 用户ID
 * @param granularity 数据粒度 ('daily' | 'weekly' | 'monthly')
 * @returns 成长数据点列表
 */
export async function getGrowthCurve(
  userId: string,
  granularity: 'daily' | 'weekly' | 'monthly' = 'weekly'
): Promise<GrowthDataPoint[]> {
  return apiClient.get<GrowthDataPoint[]>(
    `${ENDPOINTS.GET_GROWTH_CURVE(userId)}?granularity=${granularity}`
  );
}

/**
 * 获取能力对比数据
 * @param userId 用户ID
 * @param comparisonTypes 对比类型数组
 * @returns 对比数据列表
 */
export async function getComparisons(
  userId: string,
  comparisonTypes: Array<'peer' | 'historical' | 'target'> = ['peer', 'historical']
): Promise<Comparison[]> {
  return apiClient.post<Comparison[]>(ENDPOINTS.GET_COMPARISONS(userId), {
    types: comparisonTypes,
  });
}

/**
 * 获取用户徽章
 * @param userId 用户ID
 * @returns 徽章列表
 */
export async function getBadges(userId: string): Promise<Badge[]> {
  return apiClient.get<Badge[]>(ENDPOINTS.GET_BADGES(userId));
}

/**
 * 获取用户成就
 * @param userId 用户ID
 * @param includeCompleted 是否包含已完成成就
 * @returns 成就列表
 */
export async function getAchievements(
  userId: string,
  includeCompleted: boolean = true
): Promise<Achievement[]> {
  return apiClient.get<Achievement[]>(
    `${ENDPOINTS.GET_ACHIEVEMENTS(userId)}?completed=${includeCompleted}`
  );
}

/**
 * 生成新评估报告
 * @param userId 用户ID
 * @param force 是否强制重新生成
 * @returns 新生成的评估报告
 */
export async function generateReport(
  userId: string,
  force: boolean = false
): Promise<EvaluationReport> {
  return apiClient.post<EvaluationReport>(
    ENDPOINTS.GENERATE_REPORT(userId),
    { force }
  );
}

/**
 * 获取雷达图数据（用于可视化）
 * @param userId 用户ID
 * @returns 雷达图格式数据
 */
export async function getRadarData(userId: string): Promise<RadarData> {
  const [dimensions, comparisons] = await Promise.all([
    getDimensions(userId),
    getComparisons(userId, ['peer']),
  ]);

  const peerComparison = comparisons.find(c => c.type === 'peer');

  return {
    dimensions: [
      { key: 'knowledge', name: '知识掌握', value: dimensions.knowledge },
      { key: 'problemSolving', name: '问题解决', value: dimensions.problemSolving },
      { key: 'proofAbility', name: '证明能力', value: dimensions.proofAbility },
      { key: 'application', name: '应用实践', value: dimensions.application },
      { key: 'innovation', name: '创新思维', value: dimensions.innovation },
    ],
    peerAverage: peerComparison?.value || null,
    maxValue: 100,
  };
}

/**
 * 获取进步分析
 * @param userId 用户ID
 * @returns 进步分析报告
 */
export async function getProgressAnalysis(userId: string): Promise<ProgressAnalysis> {
  return apiClient.get<ProgressAnalysis>(`/evaluation/${userId}/progress-analysis`);
}

// 评估历史项
export interface EvaluationHistoryItem {
  id: string;
  date: string;
  overallScore: number;
  dimensions: AbilityDimensions;
  percentile: number;
}

// 雷达图数据
export interface RadarData {
  dimensions: Array<{
    key: string;
    name: string;
    value: number;
  }>;
  peerAverage: number | null;
  maxValue: number;
}

// 进步分析
export interface ProgressAnalysis {
  period: {
    start: string;
    end: string;
  };
  overallChange: number;
  dimensionChanges: Array<{
    dimension: keyof AbilityDimensions;
    change: number;
    trend: 'up' | 'down' | 'stable';
  }>;
  fastestGrowing: keyof AbilityDimensions | null;
  needsAttention: keyof AbilityDimensions | null;
  milestones: Array<{
    type: string;
    description: string;
    achievedAt: string;
  }>;
  predictions: {
    nextWeekScore: number;
    nextMonthScore: number;
    confidence: number;
  };
}

// 评估服务组合对象
export const evaluationApi = {
  getEvaluation,
  getEvaluationHistory,
  getDimensions,
  getGrowthCurve,
  getComparisons,
  getBadges,
  getAchievements,
  generateReport,
  getRadarData,
  getProgressAnalysis,
};

export default evaluationApi;
