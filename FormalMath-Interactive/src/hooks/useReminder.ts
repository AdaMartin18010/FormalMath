import { useState, useEffect, useCallback } from 'react';
import { reminderService, type Reminder, type LearningGoal } from '@/services/reminderService';

// 提醒管理 Hook
export const useReminders = (userId: string) => {
  const [reminders, setReminders] = useState<Reminder[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const loadReminders = useCallback(async () => {
    if (!userId) return;
    
    setIsLoading(true);
    try {
      const data = await reminderService.getUserReminders(userId);
      setReminders(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : '加载失败');
    } finally {
      setIsLoading(false);
    }
  }, [userId]);

  useEffect(() => {
    loadReminders();
  }, [loadReminders]);

  const createReminder = useCallback(async (
    reminderData: Omit<Reminder, 'id' | 'createdAt' | 'updatedAt' | 'triggerCount'>
  ) => {
    setIsLoading(true);
    try {
      const newReminder = await reminderService.createReminder(reminderData);
      await loadReminders();
      return { success: true, reminder: newReminder };
    } catch (err) {
      const message = err instanceof Error ? err.message : '创建失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [loadReminders]);

  const updateReminder = useCallback(async (id: string, updates: Partial<Reminder>) => {
    setIsLoading(true);
    try {
      const updated = await reminderService.updateReminder(id, updates);
      await loadReminders();
      return { success: true, reminder: updated };
    } catch (err) {
      const message = err instanceof Error ? err.message : '更新失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [loadReminders]);

  const deleteReminder = useCallback(async (id: string) => {
    setIsLoading(true);
    try {
      await reminderService.deleteReminder(id);
      await loadReminders();
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '删除失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [loadReminders]);

  const toggleReminder = useCallback(async (id: string) => {
    const reminder = reminders.find(r => r.id === id);
    if (!reminder) return { success: false, error: '提醒不存在' };

    return updateReminder(id, { isActive: !reminder.isActive });
  }, [reminders, updateReminder]);

  return {
    reminders,
    isLoading,
    error,
    createReminder,
    updateReminder,
    deleteReminder,
    toggleReminder,
    refreshReminders: loadReminders,
  };
};

// 学习目标管理 Hook
export const useLearningGoals = (userId: string) => {
  const [goals, setGoals] = useState<LearningGoal[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  const loadGoals = useCallback(async () => {
    if (!userId) return;
    
    setIsLoading(true);
    try {
      const data = await reminderService['db']?.getAllFromIndex('goals', 'by-user', userId) || [];
      setGoals(data);
    } catch (err) {
      console.error('Failed to load goals:', err);
    } finally {
      setIsLoading(false);
    }
  }, [userId]);

  useEffect(() => {
    loadGoals();
  }, [loadGoals]);

  const createGoal = useCallback(async (
    goalData: Omit<LearningGoal, 'id' | 'current' | 'isCompleted' | 'completedAt'>
  ) => {
    setIsLoading(true);
    try {
      const newGoal = await reminderService.createGoal(goalData);
      await loadGoals();
      return { success: true, goal: newGoal };
    } catch (err) {
      const message = err instanceof Error ? err.message : '创建失败';
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [loadGoals]);

  const updateGoalProgress = useCallback(async (
    goalId: string,
    progress: Partial<LearningGoal['current']>
  ) => {
    try {
      const updated = await reminderService.updateGoalProgress(goalId, progress);
      await loadGoals();
      return { success: true, goal: updated };
    } catch (err) {
      const message = err instanceof Error ? err.message : '更新失败';
      return { success: false, error: message };
    }
  }, [loadGoals]);

  const deleteGoal = useCallback(async (goalId: string) => {
    try {
      await reminderService['db']?.delete('goals', goalId);
      await loadGoals();
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '删除失败';
      return { success: false, error: message };
    }
  }, [loadGoals]);

  return {
    goals,
    isLoading,
    createGoal,
    updateGoalProgress,
    deleteGoal,
    refreshGoals: loadGoals,
  };
};

// 学习统计 Hook
export const useLearningStats = (userId: string) => {
  const [todayStats, setTodayStats] = useState<{
    studyMinutes: number;
    problemsSolved: number;
    conceptsLearned: number;
    streakDay: number;
  } | null>(null);
  const [weeklyStats, setWeeklyStats] = useState<{
    totalMinutes: number;
    totalProblems: number;
    averageMinutes: number;
    bestDay: string;
  } | null>(null);
  const [isLoading, setIsLoading] = useState(false);

  const loadTodayStats = useCallback(async () => {
    if (!userId) return;
    
    const today = new Date().toISOString().split('T')[0];
    try {
      const stats = await reminderService.getStats(userId, today);
      setTodayStats(stats || {
        studyMinutes: 0,
        problemsSolved: 0,
        conceptsLearned: 0,
        streakDay: 0,
      });
    } catch (err) {
      console.error('Failed to load today stats:', err);
    }
  }, [userId]);

  const loadWeeklyStats = useCallback(async () => {
    if (!userId) return;
    
    setIsLoading(true);
    try {
      const endDate = new Date().toISOString().split('T')[0];
      const startDate = new Date(Date.now() - 7 * 24 * 60 * 60 * 1000).toISOString().split('T')[0];
      
      const stats = await reminderService.getStatsRange(userId, startDate, endDate);
      
      const totalMinutes = stats.reduce((sum, s) => sum + s.studyMinutes, 0);
      const totalProblems = stats.reduce((sum, s) => sum + s.problemsSolved, 0);
      
      const bestDay = stats.reduce((best, s) => 
        s.studyMinutes > (best?.studyMinutes || 0) ? s : best
      , stats[0]);

      setWeeklyStats({
        totalMinutes,
        totalProblems,
        averageMinutes: Math.round(totalMinutes / 7),
        bestDay: bestDay?.date || '-',
      });
    } catch (err) {
      console.error('Failed to load weekly stats:', err);
    } finally {
      setIsLoading(false);
    }
  }, [userId]);

  useEffect(() => {
    loadTodayStats();
    loadWeeklyStats();
  }, [loadTodayStats, loadWeeklyStats]);

  const recordStudy = useCallback(async (
    minutes: number,
    problemsSolved = 0,
    conceptsLearned = 0
  ) => {
    try {
      await reminderService.recordStudySession(userId, minutes, problemsSolved, conceptsLearned);
      await loadTodayStats();
      await loadWeeklyStats();
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '记录失败';
      return { success: false, error: message };
    }
  }, [userId, loadTodayStats, loadWeeklyStats]);

  return {
    todayStats,
    weeklyStats,
    isLoading,
    recordStudy,
    refreshStats: () => {
      loadTodayStats();
      loadWeeklyStats();
    },
  };
};

// 智能建议 Hook
export const useSmartSuggestions = (userId: string) => {
  const [suggestions, setSuggestions] = useState<string[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  const loadSuggestions = useCallback(async () => {
    if (!userId) return;
    
    setIsLoading(true);
    try {
      const data = await reminderService.getSmartSuggestions(userId);
      setSuggestions(data);
    } catch (err) {
      console.error('Failed to load suggestions:', err);
    } finally {
      setIsLoading(false);
    }
  }, [userId]);

  useEffect(() => {
    loadSuggestions();
  }, [loadSuggestions]);

  return {
    suggestions,
    isLoading,
    refreshSuggestions: loadSuggestions,
  };
};

// 通知权限 Hook
export const useNotificationPermission = () => {
  const [permission, setPermission] = useState<NotificationPermission>('default');
  const [isSupported, setIsSupported] = useState(true);

  useEffect(() => {
    if (!('Notification' in window)) {
      setIsSupported(false);
      return;
    }

    setPermission(Notification.permission);
  }, []);

  const requestPermission = useCallback(async () => {
    if (!('Notification' in window)) {
      return { success: false, error: '浏览器不支持通知' };
    }

    try {
      const result = await Notification.requestPermission();
      setPermission(result);
      return { success: result === 'granted', permission: result };
    } catch (err) {
      return { success: false, error: err instanceof Error ? err.message : '请求失败' };
    }
  }, []);

  return {
    permission,
    isSupported,
    isGranted: permission === 'granted',
    isDenied: permission === 'denied',
    requestPermission,
  };
};

// 学习追踪 Hook（组合 Hook）
export const useLearningTracker = (userId: string) => {
  const reminders = useReminders(userId);
  const goals = useLearningGoals(userId);
  const stats = useLearningStats(userId);
  const suggestions = useSmartSuggestions(userId);
  const notifications = useNotificationPermission();

  return {
    reminders,
    goals,
    stats,
    suggestions,
    notifications,
  };
};

export default useReminders;
