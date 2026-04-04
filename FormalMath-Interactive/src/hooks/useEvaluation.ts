/**
 * FormalMath 评估系统 Hooks (T2.2)
 */

import { useState, useEffect, useCallback } from 'react';
import { evaluationApi } from '../api/evaluation';
import type {
  EvaluationReport,
  AbilityDimensions,
  GrowthDataPoint,
  Badge,
  Achievement,
} from '../types/learning';
import type { RadarData, ProgressAnalysis } from '../api/evaluation';

interface UseEvaluationOptions {
  userId: string;
  autoFetch?: boolean;
}

interface UseEvaluationReturn {
  // 数据
  evaluation: EvaluationReport | null;
  dimensions: AbilityDimensions | null;
  growthCurve: GrowthDataPoint[];
  badges: Badge[];
  achievements: Achievement[];
  radarData: RadarData | null;
  progressAnalysis: ProgressAnalysis | null;
  
  // 加载状态
  loading: boolean;
  error: Error | null;
  
  // 方法
  fetchEvaluation: () => Promise<void>;
  refreshEvaluation: () => Promise<void>;
  generateReport: (force?: boolean) => Promise<EvaluationReport>;
}

/**
 * 评估系统 Hook
 */
export function useEvaluation(options: UseEvaluationOptions): UseEvaluationReturn {
  const { userId, autoFetch = true } = options;
  
  const [evaluation, setEvaluation] = useState<EvaluationReport | null>(null);
  const [dimensions, setDimensions] = useState<AbilityDimensions | null>(null);
  const [growthCurve, setGrowthCurve] = useState<GrowthDataPoint[]>([]);
  const [badges, setBadges] = useState<Badge[]>([]);
  const [achievements, setAchievements] = useState<Achievement[]>([]);
  const [radarData, setRadarData] = useState<RadarData | null>(null);
  const [progressAnalysis, setProgressAnalysis] = useState<ProgressAnalysis | null>(null);
  
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  const fetchEvaluation = useCallback(async () => {
    if (!userId) return;
    
    setLoading(true);
    setError(null);
    
    try {
      const [
        evalData,
        dimsData,
        growthData,
        badgesData,
        achievementsData,
        radar,
        analysis,
      ] = await Promise.all([
        evaluationApi.getEvaluation(userId),
        evaluationApi.getDimensions(userId),
        evaluationApi.getGrowthCurve(userId),
        evaluationApi.getBadges(userId),
        evaluationApi.getAchievements(userId),
        evaluationApi.getRadarData(userId),
        evaluationApi.getProgressAnalysis(userId),
      ]);
      
      setEvaluation(evalData);
      setDimensions(dimsData);
      setGrowthCurve(growthData);
      setBadges(badgesData);
      setAchievements(achievementsData);
      setRadarData(radar);
      setProgressAnalysis(analysis);
    } catch (err) {
      setError(err instanceof Error ? err : new Error('Failed to fetch evaluation'));
    } finally {
      setLoading(false);
    }
  }, [userId]);

  const refreshEvaluation = useCallback(async () => {
    await fetchEvaluation();
  }, [fetchEvaluation]);

  const generateReport = useCallback(async (force: boolean = false): Promise<EvaluationReport> => {
    const report = await evaluationApi.generateReport(userId, force);
    await fetchEvaluation();
    return report;
  }, [userId, fetchEvaluation]);

  useEffect(() => {
    if (autoFetch && userId) {
      fetchEvaluation();
    }
  }, [autoFetch, userId, fetchEvaluation]);

  return {
    evaluation,
    dimensions,
    growthCurve,
    badges,
    achievements,
    radarData,
    progressAnalysis,
    loading,
    error,
    fetchEvaluation,
    refreshEvaluation,
    generateReport,
  };
}

/**
 * 成长曲线 Hook
 */
export function useGrowthCurve(
  userId: string,
  granularity: 'daily' | 'weekly' | 'monthly' = 'weekly'
) {
  const [data, setData] = useState<GrowthDataPoint[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    evaluationApi.getGrowthCurve(userId, granularity)
      .then(setData)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch growth curve')))
      .finally(() => setLoading(false));
  }, [userId, granularity]);

  return { data, loading, error };
}

/**
 * 能力对比 Hook
 */
export function useComparisons(
  userId: string,
  types: Array<'peer' | 'historical' | 'target'> = ['peer', 'historical']
) {
  const [comparisons, setComparisons] = useState<import('../types/learning').Comparison[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    evaluationApi.getComparisons(userId, types)
      .then(setComparisons)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch comparisons')))
      .finally(() => setLoading(false));
  }, [userId, JSON.stringify(types)]);

  return { comparisons, loading, error };
}

/**
 * 徽章展示 Hook
 */
export function useBadges(userId: string) {
  const [badges, setBadges] = useState<Badge[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);
  const [stats, setStats] = useState({
    total: 0,
    common: 0,
    rare: 0,
    epic: 0,
    legendary: 0,
  });

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    evaluationApi.getBadges(userId)
      .then((data) => {
        setBadges(data);
        setStats({
          total: data.length,
          common: data.filter(b => b.rarity === 'common').length,
          rare: data.filter(b => b.rarity === 'rare').length,
          epic: data.filter(b => b.rarity === 'epic').length,
          legendary: data.filter(b => b.rarity === 'legendary').length,
        });
      })
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch badges')))
      .finally(() => setLoading(false));
  }, [userId]);

  return { badges, stats, loading, error };
}

export default useEvaluation;
