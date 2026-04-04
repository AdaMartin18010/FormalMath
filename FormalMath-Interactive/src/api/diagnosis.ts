/**
 * FormalMath 认知诊断系统 API (T2.1)
 * 诊断结果获取与提交
 */

import { apiClient } from './client';
import type {
  DiagnosisReport,
  DiagnosisSubmitRequest,
  DiagnosisSubmitResponse,
  WeakPoint,
  Recommendation,
  ApiResponse,
} from '../types/learning';

// API 端点
const ENDPOINTS = {
  GET_DIAGNOSIS: (userId: string) => `/diagnosis/${userId}`,
  GET_DIAGNOSIS_HISTORY: (userId: string) => `/diagnosis/${userId}/history`,
  SUBMIT_DIAGNOSIS: '/diagnosis/submit',
  GET_DIAGNOSIS_BY_ID: (diagnosisId: string) => `/diagnosis/detail/${diagnosisId}`,
  GET_DIAGNOSIS_QUESTIONS: '/diagnosis/questions',
  GET_WEAK_POINTS: (userId: string) => `/diagnosis/${userId}/weak-points`,
  GET_RECOMMENDATIONS: (userId: string) => `/diagnosis/${userId}/recommendations`,
} as const;

/**
 * 获取用户最新诊断结果
 * @param userId 用户ID
 * @returns 诊断报告
 */
export async function getDiagnosis(userId: string): Promise<DiagnosisReport> {
  return apiClient.get<DiagnosisReport>(ENDPOINTS.GET_DIAGNOSIS(userId));
}

/**
 * 获取用户诊断历史
 * @param userId 用户ID
 * @param limit 返回数量限制
 * @returns 诊断报告历史列表
 */
export async function getDiagnosisHistory(
  userId: string, 
  limit: number = 10
): Promise<DiagnosisReport[]> {
  return apiClient.get<DiagnosisReport[]>(
    `${ENDPOINTS.GET_DIAGNOSIS_HISTORY(userId)}?limit=${limit}`
  );
}

/**
 * 提交诊断答案
 * @param request 诊断提交请求
 * @returns 诊断结果
 */
export async function submitDiagnosis(
  request: DiagnosisSubmitRequest
): Promise<DiagnosisSubmitResponse> {
  return apiClient.post<DiagnosisSubmitResponse>(
    ENDPOINTS.SUBMIT_DIAGNOSIS, 
    request
  );
}

/**
 * 获取特定诊断详情
 * @param diagnosisId 诊断ID
 * @returns 诊断报告详情
 */
export async function getDiagnosisById(diagnosisId: string): Promise<DiagnosisReport> {
  return apiClient.get<DiagnosisReport>(ENDPOINTS.GET_DIAGNOSIS_BY_ID(diagnosisId));
}

/**
 * 获取诊断问题列表
 * @param category 可选分类筛选
 * @param difficulty 可选难度筛选
 * @returns 问题列表
 */
export async function getDiagnosisQuestions(
  category?: string,
  difficulty?: number
): Promise<DiagnosisQuestion[]> {
  const params = new URLSearchParams();
  if (category) params.append('category', category);
  if (difficulty) params.append('difficulty', difficulty.toString());
  
  const queryString = params.toString();
  return apiClient.get<DiagnosisQuestion[]>(
    `${ENDPOINTS.GET_DIAGNOSIS_QUESTIONS}${queryString ? `?${queryString}` : ''}`
  );
}

/**
 * 获取用户薄弱点分析
 * @param userId 用户ID
 * @returns 薄弱点列表
 */
export async function getWeakPoints(userId: string): Promise<WeakPoint[]> {
  return apiClient.get<WeakPoint[]>(ENDPOINTS.GET_WEAK_POINTS(userId));
}

/**
 * 获取个性化推荐
 * @param userId 用户ID
 * @param count 推荐数量
 * @returns 推荐列表
 */
export async function getRecommendations(
  userId: string, 
  count: number = 5
): Promise<Recommendation[]> {
  return apiClient.get<Recommendation[]>(
    `${ENDPOINTS.GET_RECOMMENDATIONS(userId)}?count=${count}`
  );
}

/**
 * 对比多次诊断结果
 * @param userId 用户ID
 * @param diagnosisIds 要对比的诊断ID列表
 * @returns 对比结果
 */
export async function compareDiagnoses(
  userId: string,
  diagnosisIds: string[]
): Promise<DiagnosisComparison> {
  return apiClient.post<DiagnosisComparison>(
    `/diagnosis/${userId}/compare`,
    { diagnosisIds }
  );
}

// 诊断问题类型
export interface DiagnosisQuestion {
  id: string;
  type: 'single_choice' | 'multiple_choice' | 'true_false' | 'fill_blank';
  category: string;
  difficulty: number;
  content: {
    text: string;
    options?: Array<{
      id: string;
      text: string;
      isCorrect?: boolean; // 仅在提交后返回
    }>;
    hint?: string;
  };
  relatedConcepts: string[];
  estimatedTime: number;
}

// 诊断对比结果
export interface DiagnosisComparison {
  diagnoses: Array<{
    id: string;
    date: string;
    overallLevel: number;
  }>;
  conceptProgress: Array<{
    conceptId: string;
    conceptName: string;
    levels: number[];
    trend: 'improving' | 'stable' | 'declining';
  }>;
  overallTrend: 'improving' | 'stable' | 'declining';
  keyChanges: Array<{
    type: 'improvement' | 'decline' | 'new_weakness';
    conceptId: string;
    description: string;
  }>;
}

// 诊断服务组合对象
export const diagnosisApi = {
  getDiagnosis,
  getDiagnosisHistory,
  submitDiagnosis,
  getDiagnosisById,
  getDiagnosisQuestions,
  getWeakPoints,
  getRecommendations,
  compareDiagnoses,
};

export default diagnosisApi;
