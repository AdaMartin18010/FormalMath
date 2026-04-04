/**
 * FormalMath 自适应学习系统 Hooks (T3.1)
 */

import { useState, useEffect, useCallback } from 'react';
import { adaptiveApi } from '../api/adaptive';
import type {
  LearningPath,
  LearningNode,
  ProgressUpdateRequest,
  ProgressUpdateResponse,
  LearningStats,
} from '../types/learning';
import type { 
  PathGenerationOptions, 
  PathAdjustmentOptions,
  PathPreview,
  LearningStats as ApiLearningStats
} from '../api/adaptive';

interface UseAdaptiveOptions {
  userId: string;
  autoFetch?: boolean;
}

interface UseAdaptiveReturn {
  // 数据
  learningPath: LearningPath | null;
  currentNode: LearningNode | null;
  nextNodes: LearningNode[];
  stats: LearningStats | null;
  
  // 状态
  loading: boolean;
  error: Error | null;
  updating: boolean;
  
  // 方法
  fetchPath: () => Promise<void>;
  refreshPath: () => Promise<void>;
  generateNewPath: (options?: PathGenerationOptions) => Promise<LearningPath>;
  updateProgress: (conceptId: string, mastery: number, data?: Partial<ProgressUpdateRequest>) => Promise<ProgressUpdateResponse>;
  completeNode: (nodeId: string, data: { timeSpent: number; exercisesCompleted: number; correctRate: number }) => Promise<ProgressUpdateResponse>;
  skipNode: (nodeId: string, reason?: string) => Promise<LearningPath>;
  adjustPath: (adjustments: PathAdjustmentOptions) => Promise<LearningPath>;
  getPathPreview: (targetConceptId: string) => Promise<PathPreview>;
}

/**
 * 自适应学习系统 Hook
 */
export function useAdaptive(options: UseAdaptiveOptions): UseAdaptiveReturn {
  const { userId, autoFetch = true } = options;
  
  const [learningPath, setLearningPath] = useState<LearningPath | null>(null);
  const [currentNode, setCurrentNode] = useState<LearningNode | null>(null);
  const [nextNodes, setNextNodes] = useState<LearningNode[]>([]);
  const [stats, setStats] = useState<LearningStats | null>(null);
  
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);
  const [updating, setUpdating] = useState(false);

  const fetchPath = useCallback(async () => {
    if (!userId) return;
    
    setLoading(true);
    setError(null);
    
    try {
      const [pathData, nextNodesData, statsData] = await Promise.all([
        adaptiveApi.getLearningPath(userId),
        adaptiveApi.getNextNodes(userId, 3),
        adaptiveApi.getLearningStats(userId),
      ]);
      
      setLearningPath(pathData);
      setNextNodes(nextNodesData);
      setStats(statsData);
      
      // 找到当前正在进行的节点
      const current = pathData.path.find(n => n.status === 'in_progress');
      setCurrentNode(current || null);
    } catch (err) {
      setError(err instanceof Error ? err : new Error('Failed to fetch learning path'));
    } finally {
      setLoading(false);
    }
  }, [userId]);

  const refreshPath = useCallback(async () => {
    await fetchPath();
  }, [fetchPath]);

  const generateNewPath = useCallback(async (
    options?: PathGenerationOptions
  ): Promise<LearningPath> => {
    const path = await adaptiveApi.generatePath(userId, options);
    setLearningPath(path);
    
    const current = path.path.find(n => n.status === 'in_progress');
    setCurrentNode(current || null);
    
    return path;
  }, [userId]);

  const updateProgress = useCallback(async (
    conceptId: string,
    mastery: number,
    data?: Partial<ProgressUpdateRequest>
  ): Promise<ProgressUpdateResponse> => {
    setUpdating(true);
    
    try {
      const request: ProgressUpdateRequest = {
        userId,
        conceptId,
        mastery,
        ...data,
      };
      
      const result = await adaptiveApi.updateProgress(request);
      
      // 刷新路径以获取最新状态
      await refreshPath();
      
      return result;
    } finally {
      setUpdating(false);
    }
  }, [userId, refreshPath]);

  const completeNode = useCallback(async (
    nodeId: string,
    data: { timeSpent: number; exercisesCompleted: number; correctRate: number }
  ): Promise<ProgressUpdateResponse> => {
    setUpdating(true);
    
    try {
      const result = await adaptiveApi.completeNode(nodeId, data);
      await refreshPath();
      return result;
    } finally {
      setUpdating(false);
    }
  }, [refreshPath]);

  const skipNode = useCallback(async (
    nodeId: string,
    reason?: string
  ): Promise<LearningPath> => {
    const path = await adaptiveApi.skipNode(nodeId, reason);
    setLearningPath(path);
    return path;
  }, []);

  const adjustPath = useCallback(async (
    adjustments: PathAdjustmentOptions
  ): Promise<LearningPath> => {
    const path = await adaptiveApi.adjustPath(userId, adjustments);
    setLearningPath(path);
    return path;
  }, [userId]);

  const getPathPreview = useCallback(async (
    targetConceptId: string
  ): Promise<PathPreview> => {
    return adaptiveApi.getPathPreview(userId, targetConceptId);
  }, [userId]);

  useEffect(() => {
    if (autoFetch && userId) {
      fetchPath();
    }
  }, [autoFetch, userId, fetchPath]);

  return {
    learningPath,
    currentNode,
    nextNodes,
    stats,
    loading,
    error,
    updating,
    fetchPath,
    refreshPath,
    generateNewPath,
    updateProgress,
    completeNode,
    skipNode,
    adjustPath,
    getPathPreview,
  };
}

/**
 * 学习节点详情 Hook
 */
export function useNodeDetail(nodeId: string | null) {
  const [node, setNode] = useState<LearningNode | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!nodeId) {
      setNode(null);
      return;
    }

    setLoading(true);
    adaptiveApi.getNodeDetail(nodeId)
      .then(setNode)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch node')))
      .finally(() => setLoading(false));
  }, [nodeId]);

  return { node, loading, error };
}

/**
 * 学习统计 Hook
 */
export function useLearningStats(userId: string) {
  const [stats, setStats] = useState<ApiLearningStats | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    adaptiveApi.getLearningStats(userId)
      .then(setStats)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch stats')))
      .finally(() => setLoading(false));
  }, [userId]);

  return { stats, loading, error };
}

export default useAdaptive;
