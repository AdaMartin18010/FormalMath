/**
 * FormalMath 认知诊断系统 Hooks (T2.1)
 */

import { useState, useEffect, useCallback } from 'react';
import { diagnosisApi } from '../api/diagnosis';
import type {
  DiagnosisReport,
  DiagnosisSubmitRequest,
  DiagnosisSubmitResponse,
  WeakPoint,
  Recommendation,
  Answer,
} from '../types/learning';

interface UseDiagnosisOptions {
  userId: string;
  autoFetch?: boolean;
}

interface UseDiagnosisReturn {
  // 数据
  diagnosis: DiagnosisReport | null;
  weakPoints: WeakPoint[];
  recommendations: Recommendation[];
  loading: boolean;
  error: Error | null;
  
  // 方法
  fetchDiagnosis: () => Promise<void>;
  submitDiagnosis: (answers: Answer[]) => Promise<DiagnosisSubmitResponse>;
  refreshDiagnosis: () => Promise<void>;
  
  // 状态
  isSubmitting: boolean;
  submitError: Error | null;
  lastSubmitResult: DiagnosisSubmitResponse | null;
}

/**
 * 认知诊断系统 Hook
 * 获取和管理诊断数据
 */
export function useDiagnosis(options: UseDiagnosisOptions): UseDiagnosisReturn {
  const { userId, autoFetch = true } = options;
  
  const [diagnosis, setDiagnosis] = useState<DiagnosisReport | null>(null);
  const [weakPoints, setWeakPoints] = useState<WeakPoint[]>([]);
  const [recommendations, setRecommendations] = useState<Recommendation[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);
  
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [submitError, setSubmitError] = useState<Error | null>(null);
  const [lastSubmitResult, setLastSubmitResult] = useState<DiagnosisSubmitResponse | null>(null);

  const fetchDiagnosis = useCallback(async () => {
    if (!userId) return;
    
    setLoading(true);
    setError(null);
    
    try {
      const [diagnosisData, weakPointsData, recommendationsData] = await Promise.all([
        diagnosisApi.getDiagnosis(userId),
        diagnosisApi.getWeakPoints(userId),
        diagnosisApi.getRecommendations(userId),
      ]);
      
      setDiagnosis(diagnosisData);
      setWeakPoints(weakPointsData);
      setRecommendations(recommendationsData);
    } catch (err) {
      setError(err instanceof Error ? err : new Error('Failed to fetch diagnosis'));
    } finally {
      setLoading(false);
    }
  }, [userId]);

  const submitDiagnosis = useCallback(async (
    answers: Answer[],
    metadata?: { totalTime: number; device: string; version: string }
  ): Promise<DiagnosisSubmitResponse> => {
    setIsSubmitting(true);
    setSubmitError(null);
    
    try {
      const request: DiagnosisSubmitRequest = {
        answers,
        metadata,
      };
      
      const result = await diagnosisApi.submitDiagnosis(request);
      setLastSubmitResult(result);
      
      // 提交成功后刷新诊断数据
      await fetchDiagnosis();
      
      return result;
    } catch (err) {
      const error = err instanceof Error ? err : new Error('Failed to submit diagnosis');
      setSubmitError(error);
      throw error;
    } finally {
      setIsSubmitting(false);
    }
  }, [fetchDiagnosis]);

  const refreshDiagnosis = useCallback(async () => {
    await fetchDiagnosis();
  }, [fetchDiagnosis]);

  useEffect(() => {
    if (autoFetch && userId) {
      fetchDiagnosis();
    }
  }, [autoFetch, userId, fetchDiagnosis]);

  return {
    diagnosis,
    weakPoints,
    recommendations,
    loading,
    error,
    fetchDiagnosis,
    submitDiagnosis,
    refreshDiagnosis,
    isSubmitting,
    submitError,
    lastSubmitResult,
  };
}

/**
 * 诊断历史 Hook
 */
export function useDiagnosisHistory(userId: string, limit: number = 10) {
  const [history, setHistory] = useState<DiagnosisReport[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    diagnosisApi.getDiagnosisHistory(userId, limit)
      .then(setHistory)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch history')))
      .finally(() => setLoading(false));
  }, [userId, limit]);

  return { history, loading, error };
}

/**
 * 诊断问题 Hook
 */
export function useDiagnosisQuestions(category?: string, difficulty?: number) {
  const [questions, setQuestions] = useState<import('../api/diagnosis').DiagnosisQuestion[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    setLoading(true);
    diagnosisApi.getDiagnosisQuestions(category, difficulty)
      .then(setQuestions)
      .catch(err => setError(err instanceof Error ? err : new Error('Failed to fetch questions')))
      .finally(() => setLoading(false));
  }, [category, difficulty]);

  return { questions, loading, error };
}

export default useDiagnosis;
