/**
 * FormalMath 自适应学习系统 API (T3.1)
 * 学习路径与进度管理
 */

import { apiClient } from './client';
import type {
  LearningPath,
  LearningNode,
  ProgressUpdateRequest,
  ProgressUpdateResponse,
  LearningNodeStatus,
  MasteryLevel,
  ApiResponse,
} from '../types/learning';

// API 端点
const ENDPOINTS = {
  GET_PATH: (userId: string) => `/adaptive/path/${userId}`,
  GENERATE_PATH: (userId: string) => `/adaptive/path/${userId}/generate`,
  UPDATE_PROGRESS: '/adaptive/progress',
  GET_NODE_DETAIL: (nodeId: string) => `/adaptive/node/${nodeId}`,
  UPDATE_NODE_STATUS: (nodeId: string) => `/adaptive/node/${nodeId}/status`,
  SKIP_NODE: (nodeId: string) => `/adaptive/node/${nodeId}/skip`,
  GET_NEXT_NODES: (userId: string) => `/adaptive/${userId}/next-nodes`,
  ADJUST_PATH: (userId: string) => `/adaptive/path/${userId}/adjust`,
  GET_LEARNING_STATS: (userId: string) => `/adaptive/${userId}/stats`,
} as const;

/**
 * 获取用户学习路径
 * @param userId 用户ID
 * @param refresh 是否刷新路径
 * @returns 学习路径
 */
export async function getLearningPath(
  userId: string,
  refresh: boolean = false
): Promise<LearningPath> {
  const params = refresh ? '?refresh=true' : '';
  return apiClient.get<LearningPath>(`${ENDPOINTS.GET_PATH(userId)}${params}`);
}

/**
 * 生成新的学习路径
 * @param userId 用户ID
 * @param options 路径生成选项
 * @returns 新生成的学习路径
 */
export async function generatePath(
  userId: string,
  options?: PathGenerationOptions
): Promise<LearningPath> {
  return apiClient.post<LearningPath>(
    ENDPOINTS.GENERATE_PATH(userId),
    options || {}
  );
}

/**
 * 更新学习进度
 * @param request 进度更新请求
 * @returns 更新结果
 */
export async function updateProgress(
  request: ProgressUpdateRequest
): Promise<ProgressUpdateResponse> {
  return apiClient.post<ProgressUpdateResponse>(ENDPOINTS.UPDATE_PROGRESS, request);
}

/**
 * 批量更新进度
 * @param requests 进度更新请求列表
 * @returns 批量更新结果
 */
export async function batchUpdateProgress(
  requests: ProgressUpdateRequest[]
): Promise<BatchProgressResponse> {
  return apiClient.post<BatchProgressResponse>('/adaptive/progress/batch', { updates: requests });
}

/**
 * 获取节点详情
 * @param nodeId 节点ID
 * @returns 节点详细信息
 */
export async function getNodeDetail(nodeId: string): Promise<LearningNode> {
  return apiClient.get<LearningNode>(ENDPOINTS.GET_NODE_DETAIL(nodeId));
}

/**
 * 更新节点状态
 * @param nodeId 节点ID
 * @param status 新状态
 * @param data 附加数据
 * @returns 更新后的节点
 */
export async function updateNodeStatus(
  nodeId: string,
  status: LearningNodeStatus,
  data?: { mastery?: number; timeSpent?: number }
): Promise<LearningNode> {
  return apiClient.patch<LearningNode>(ENDPOINTS.UPDATE_NODE_STATUS(nodeId), {
    status,
    ...data,
  });
}

/**
 * 跳过节点
 * @param nodeId 节点ID
 * @param reason 跳过原因
 * @returns 更新后的路径
 */
export async function skipNode(
  nodeId: string,
  reason?: string
): Promise<LearningPath> {
  return apiClient.post<LearningPath>(ENDPOINTS.SKIP_NODE(nodeId), { reason });
}

/**
 * 获取下一个推荐节点
 * @param userId 用户ID
 * @param count 返回数量
 * @returns 推荐节点列表
 */
export async function getNextNodes(
  userId: string,
  count: number = 3
): Promise<LearningNode[]> {
  return apiClient.get<LearningNode[]>(
    `${ENDPOINTS.GET_NEXT_NODES(userId)}?count=${count}`
  );
}

/**
 * 调整学习路径
 * @param userId 用户ID
 * @param adjustments 调整选项
 * @returns 调整后的路径
 */
export async function adjustPath(
  userId: string,
  adjustments: PathAdjustmentOptions
): Promise<LearningPath> {
  return apiClient.post<LearningPath>(ENDPOINTS.ADJUST_PATH(userId), adjustments);
}

/**
 * 获取学习统计
 * @param userId 用户ID
 * @returns 学习统计数据
 */
export async function getLearningStats(userId: string): Promise<LearningStats> {
  return apiClient.get<LearningStats>(ENDPOINTS.GET_LEARNING_STATS(userId));
}

/**
 * 完成节点学习
 * @param nodeId 节点ID
 * @param completionData 完成数据
 * @returns 完成结果
 */
export async function completeNode(
  nodeId: string,
  completionData: NodeCompletionData
): Promise<ProgressUpdateResponse> {
  return apiClient.post<ProgressUpdateResponse>(`/adaptive/node/${nodeId}/complete`, completionData);
}

/**
 * 获取路径预览
 * @param userId 用户ID
 * @param targetConceptId 目标概念ID
 * @returns 路径预览
 */
export async function getPathPreview(
  userId: string,
  targetConceptId: string
): Promise<PathPreview> {
  return apiClient.get<PathPreview>(
    `/adaptive/path/${userId}/preview?target=${targetConceptId}`
  );
}

// 路径生成选项
export interface PathGenerationOptions {
  focusAreas?: string[]; // 重点学习领域
  excludeConcepts?: string[]; // 排除的概念
  timeLimit?: number; // 时间限制（分钟）
  difficultyPreference?: 'easier' | 'balanced' | 'challenging';
  prioritizeWeakPoints?: boolean;
}

// 批量进度响应
export interface BatchProgressResponse {
  results: Array<{
    conceptId: string;
    success: boolean;
    newMastery: number;
  }>;
  summary: {
    updated: number;
    failed: number;
    levelUps: number;
  };
}

// 路径调整选项
export interface PathAdjustmentOptions {
  reason: 'too_hard' | 'too_easy' | 'time_constraints' | 'interest_change' | 'other';
  direction: 'slower' | 'faster' | 'more_fundamental' | 'more_advanced';
  specificConcepts?: string[];
  note?: string;
}

// 节点完成数据
export interface NodeCompletionData {
  timeSpent: number;
  exercisesCompleted: number;
  correctRate: number;
  notes?: string;
  difficultyRating?: number;
}

// 学习统计
export interface LearningStats {
  userId: string;
  totalTimeSpent: number; // minutes
  nodesCompleted: number;
  nodesInProgress: number;
  averageMastery: number;
  streakDays: number;
  lastStudyDate: string;
  weeklyProgress: Array<{
    date: string;
    nodesCompleted: number;
    timeSpent: number;
  }>;
  conceptDistribution: Array<{
    conceptId: string;
    conceptName: string;
    mastery: number;
    timeSpent: number;
  }>;
  velocity: {
    nodesPerDay: number;
    minutesPerDay: number;
    estimatedCompletionDate: string;
  };
}

// 路径预览
export interface PathPreview {
  targetConceptId: string;
  targetConceptName: string;
  pathLength: number;
  estimatedTime: number;
  requiredPrerequisites: Array<{
    conceptId: string;
    name: string;
    currentMastery: number;
    requiredMastery: number;
  }>;
  suggestedStartingPoint: string;
  difficultyProfile: {
    beginner: number;
    intermediate: number;
    advanced: number;
  };
}

// 自适应学习服务组合对象
export const adaptiveApi = {
  getLearningPath,
  generatePath,
  updateProgress,
  batchUpdateProgress,
  getNodeDetail,
  updateNodeStatus,
  skipNode,
  getNextNodes,
  adjustPath,
  getLearningStats,
  completeNode,
  getPathPreview,
};

export default adaptiveApi;
