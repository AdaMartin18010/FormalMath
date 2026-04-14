// @ts-nocheck
/**
 * FormalMath 进度追踪与成就系统 Hooks
 */

import { useState, useEffect, useCallback, useRef } from 'react';
import { progressTracker } from '../integrations/progressTracker';
import type {
  RealtimeProgress,
  Notification,
  ProgressUpdateWithAchievements,
} from '../integrations/progressTracker';
import type { ProgressUpdateRequest } from '../types/learning';

interface UseProgressTrackingOptions {
  userId: string;
  autoRefresh?: boolean;
  refreshInterval?: number;
}

interface UseProgressTrackingReturn {
  // 数据
  progress: RealtimeProgress | null;
  notifications: Notification[];
  
  // 状态
  loading: boolean;
  error: Error | null;
  updating: boolean;
  
  // 方法
  refreshProgress: () => Promise<void>;
  updateProgress: (request: ProgressUpdateRequest) => Promise<ProgressUpdateWithAchievements>;
  dismissNotification: (index: number) => void;
  dismissAllNotifications: () => void;
  
  // 工具方法
  getMasteryColor: (mastery: number) => string;
  getMasteryLabel: (mastery: number) => string;
}

/**
 * 进度追踪 Hook
 * 实时追踪学习进度和成就
 */
export function useProgressTracking(
  options: UseProgressTrackingOptions
): UseProgressTrackingReturn {
  const { userId, autoRefresh = true, refreshInterval = 30000 } = options;
  
  const [progress, setProgress] = useState<RealtimeProgress | null>(null);
  const [notifications, setNotifications] = useState<Notification[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);
  const [updating, setUpdating] = useState(false);
  
  const intervalRef = useRef<NodeJS.Timeout | null>(null);

  const refreshProgress = useCallback(async () => {
    if (!userId) return;
    
    setLoading(true);
    setError(null);
    
    try {
      const data = await progressTracker.getRealtimeProgress(userId);
      setProgress(data);
    } catch (err) {
      setError(err instanceof Error ? err : new Error('Failed to fetch progress'));
    } finally {
      setLoading(false);
    }
  }, [userId]);

  const updateProgress = useCallback(async (
    request: ProgressUpdateRequest
  ): Promise<ProgressUpdateWithAchievements> => {
    setUpdating(true);
    
    try {
      const result = await progressTracker.updateProgressWithAchievements(request);
      
      // 添加新通知
      if (result.notifications.length > 0) {
        setNotifications(prev => [...result.notifications, ...prev]);
      }
      
      // 刷新进度数据
      await refreshProgress();
      
      return result;
    } finally {
      setUpdating(false);
    }
  }, [refreshProgress]);

  const dismissNotification = useCallback((index: number) => {
    setNotifications(prev => prev.filter((_, i) => i !== index));
  }, []);

  const dismissAllNotifications = useCallback(() => {
    setNotifications([]);
  }, []);

  // 初始加载
  useEffect(() => {
    if (userId) {
      refreshProgress();
    }
  }, [userId, refreshProgress]);

  // 自动刷新
  useEffect(() => {
    if (autoRefresh && userId) {
      intervalRef.current = setInterval(refreshProgress, refreshInterval);
    }
    
    return () => {
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }
    };
  }, [autoRefresh, userId, refreshInterval, refreshProgress]);

  return {
    progress,
    notifications,
    loading,
    error,
    updating,
    refreshProgress,
    updateProgress,
    dismissNotification,
    dismissAllNotifications,
    getMasteryColor: progressTracker.getMasteryColor,
    getMasteryLabel: progressTracker.getMasteryLabel,
  };
}

/**
 * 成就追踪 Hook
 */
export function useAchievements(userId: string) {
  const [progress, setProgress] = useState<RealtimeProgress | null>(null);
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    progressTracker.getRealtimeProgress(userId)
      .then(setProgress)
      .finally(() => setLoading(false));
  }, [userId]);

  const achievements = progress?.achievements;
  const badges = progress?.badges;

  return {
    achievements,
    badges,
    loading,
  };
}

/**
 * 学习连续天数 Hook
 */
export function useStreak(userId: string) {
  const [streak, setStreak] = useState(0);
  const [lastStudyDate, setLastStudyDate] = useState<string | null>(null);
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    progressTracker.getRealtimeProgress(userId)
      .then((data) => {
        setStreak(data.summary.streakDays);
        setLastStudyDate(data.velocity.lastStudyDate);
      })
      .finally(() => setLoading(false));
  }, [userId]);

  return { streak, lastStudyDate, loading };
}

/**
 * 技能增长追踪 Hook
 */
export function useSkillGrowth(userId: string) {
  const [growth, setGrowth] = useState<RealtimeProgress['skillGrowth'] | null>(null);
  const [loading, setLoading] = useState(false);

  useEffect(() => {
    if (!userId) return;

    setLoading(true);
    progressTracker.getRealtimeProgress(userId)
      .then((data) => {
        setGrowth(data.skillGrowth);
      })
      .finally(() => setLoading(false));
  }, [userId]);

  return { growth, loading };
}

export default useProgressTracking;
