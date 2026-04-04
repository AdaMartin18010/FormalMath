import { useState, useEffect, useCallback } from 'react';
import { offlineService, type OfflineContent, type LearningProgress } from '@/services/offlineService';

// 离线内容管理 Hook
export const useOfflineContent = () => {
  const [isInitialized, setIsInitialized] = useState(false);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [cachedContents, setCachedContents] = useState<OfflineContent[]>([]);
  const [stats, setStats] = useState<{
    totalItems: number;
    totalSize: number;
    pendingSync: number;
  } | null>(null);

  // 初始化
  useEffect(() => {
    const init = async () => {
      try {
        await offlineService.init();
        setIsInitialized(true);
        await refreshContents();
        await refreshStats();
      } catch (err) {
        setError(err instanceof Error ? err.message : '初始化失败');
      }
    };
    init();
  }, []);

  const refreshContents = useCallback(async () => {
    if (!isInitialized) return;
    
    try {
      const contents = await offlineService.db?.getAll('content') || [];
      setCachedContents(contents);
    } catch (err) {
      console.error('Failed to refresh contents:', err);
    }
  }, [isInitialized]);

  const refreshStats = useCallback(async () => {
    if (!isInitialized) return;
    
    try {
      const stats = await offlineService.getCacheStats();
      setStats(stats);
    } catch (err) {
      console.error('Failed to refresh stats:', err);
    }
  }, [isInitialized]);

  const cacheContent = useCallback(async (content: OfflineContent) => {
    setIsLoading(true);
    setError(null);
    
    try {
      await offlineService.cacheContent(content);
      await refreshContents();
      await refreshStats();
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '缓存失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [refreshContents, refreshStats]);

  const removeContent = useCallback(async (id: string) => {
    setIsLoading(true);
    
    try {
      await offlineService.removeCachedContent(id);
      await refreshContents();
      await refreshStats();
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '删除失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [refreshContents, refreshStats]);

  const getContent = useCallback(async (id: string) => {
    try {
      const content = await offlineService.getCachedContent(id);
      return content;
    } catch (err) {
      console.error('Failed to get content:', err);
      return undefined;
    }
  }, []);

  const clearExpired = useCallback(async () => {
    setIsLoading(true);
    
    try {
      const cleared = await offlineService.clearExpiredCache();
      await refreshContents();
      await refreshStats();
      return { success: true, cleared };
    } catch (err) {
      const message = err instanceof Error ? err.message : '清理失败';
      setError(message);
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [refreshContents, refreshStats]);

  return {
    isInitialized,
    isLoading,
    error,
    cachedContents,
    stats,
    cacheContent,
    removeContent,
    getContent,
    clearExpired,
    refreshContents,
    refreshStats,
  };
};

// 学习进度管理 Hook
export const useOfflineProgress = (userId: string) => {
  const [progress, setProgress] = useState<LearningProgress[]>([]);
  const [isLoading, setIsLoading] = useState(false);
  const [isOnline, setIsOnline] = useState(navigator.onLine);

  // 监听网络状态
  useEffect(() => {
    const handleOnline = () => setIsOnline(true);
    const handleOffline = () => setIsOnline(false);

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
    };
  }, []);

  // 加载进度
  const loadProgress = useCallback(async () => {
    try {
      const allProgress = await offlineService.getAllProgress();
      setProgress(allProgress.filter(p => p.userId === userId));
    } catch (err) {
      console.error('Failed to load progress:', err);
    }
  }, [userId]);

  useEffect(() => {
    loadProgress();
  }, [loadProgress]);

  // 保存进度
  const saveProgress = useCallback(async (
    contentId: string,
    progressData: Partial<LearningProgress>
  ) => {
    setIsLoading(true);
    
    try {
      const existing = await offlineService.getProgress(contentId);
      
      const progressToSave: LearningProgress = {
        contentId,
        userId,
        progress: progressData.progress ?? existing?.progress ?? 0,
        completed: progressData.completed ?? existing?.completed ?? false,
        startedAt: existing?.startedAt ?? Date.now(),
        lastAccessedAt: Date.now(),
        syncStatus: isOnline ? 'synced' : 'pending',
        ...progressData,
      };

      await offlineService.saveProgress(progressToSave);
      await loadProgress();
      
      return { success: true };
    } catch (err) {
      const message = err instanceof Error ? err.message : '保存失败';
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [userId, isOnline, loadProgress]);

  // 同步进度
  const syncProgress = useCallback(async () => {
    if (!isOnline) {
      return { success: false, error: '当前处于离线状态' };
    }

    setIsLoading(true);
    
    try {
      const result = await offlineService.syncWithServer();
      await loadProgress();
      return { success: true, ...result };
    } catch (err) {
      const message = err instanceof Error ? err.message : '同步失败';
      return { success: false, error: message };
    } finally {
      setIsLoading(false);
    }
  }, [isOnline, loadProgress]);

  // 获取特定内容的进度
  const getProgress = useCallback(async (contentId: string) => {
    try {
      return await offlineService.getProgress(contentId);
    } catch (err) {
      console.error('Failed to get progress:', err);
      return undefined;
    }
  }, []);

  return {
    progress,
    isLoading,
    isOnline,
    saveProgress,
    syncProgress,
    getProgress,
    refreshProgress: loadProgress,
  };
};

// 离线队列管理 Hook
export const useOfflineQueue = () => {
  const [pendingItems, setPendingItems] = useState<Awaited<ReturnType<typeof offlineService.getQueueItems>>>([]);
  const [isProcessing, setIsProcessing] = useState(false);

  const loadPendingItems = useCallback(async () => {
    try {
      const items = await offlineService.getQueueItems('pending');
      setPendingItems(items);
    } catch (err) {
      console.error('Failed to load queue:', err);
    }
  }, []);

  const processQueue = useCallback(async () => {
    if (!navigator.onLine) {
      return { success: false, error: '当前处于离线状态' };
    }

    setIsProcessing(true);
    
    try {
      const result = await offlineService.syncWithServer();
      await loadPendingItems();
      return { success: true, ...result };
    } catch (err) {
      const message = err instanceof Error ? err.message : '处理失败';
      return { success: false, error: message };
    } finally {
      setIsProcessing(false);
    }
  }, [loadPendingItems]);

  return {
    pendingItems,
    isProcessing,
    loadPendingItems,
    processQueue,
  };
};

// 预加载管理 Hook
export const usePreload = () => {
  const [isPreloading, setIsPreloading] = useState(false);
  const [progress, setProgress] = useState(0);
  const [results, setResults] = useState<{
    success: string[];
    failed: string[];
  } | null>(null);

  const preloadContent = useCallback(async (contentIds: string[]) => {
    setIsPreloading(true);
    setProgress(0);
    setResults(null);

    const success: string[] = [];
    const failed: string[] = [];

    for (let i = 0; i < contentIds.length; i++) {
      const id = contentIds[i];
      
      try {
        const response = await fetch(`/api/content/${id}`);
        if (response.ok) {
          const content = await response.json();
          await offlineService.cacheContent(content);
          success.push(id);
        } else {
          failed.push(id);
        }
      } catch (err) {
        failed.push(id);
      }

      setProgress(Math.round(((i + 1) / contentIds.length) * 100));
    }

    setResults({ success, failed });
    setIsPreloading(false);

    return { success, failed };
  }, []);

  const preloadCourse = useCallback(async (courseId: string) => {
    setIsPreloading(true);
    
    try {
      const response = await fetch(`/api/courses/${courseId}/contents`);
      if (!response.ok) throw new Error('Failed to fetch course contents');
      
      const contents = await response.json();
      const contentIds = contents.map((c: { id: string }) => c.id);
      
      return await preloadContent(contentIds);
    } catch (err) {
      setIsPreloading(false);
      return { success: [], failed: [] };
    }
  }, [preloadContent]);

  return {
    isPreloading,
    progress,
    results,
    preloadContent,
    preloadCourse,
  };
};

// 网络状态 Hook
export const useNetworkStatus = () => {
  const [isOnline, setIsOnline] = useState(navigator.onLine);
  const [connectionType, setConnectionType] = useState<string>('unknown');
  const [effectiveType, setEffectiveType] = useState<string>('unknown');

  useEffect(() => {
    const handleOnline = () => setIsOnline(true);
    const handleOffline = () => setIsOnline(false);

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    // 获取连接信息（如果支持）
    const connection = (navigator as any).connection;
    if (connection) {
      setConnectionType(connection.type || 'unknown');
      setEffectiveType(connection.effectiveType || 'unknown');

      const handleConnectionChange = () => {
        setConnectionType(connection.type || 'unknown');
        setEffectiveType(connection.effectiveType || 'unknown');
      };

      connection.addEventListener('change', handleConnectionChange);

      return () => {
        window.removeEventListener('online', handleOnline);
        window.removeEventListener('offline', handleOffline);
        connection.removeEventListener('change', handleConnectionChange);
      };
    }

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
    };
  }, []);

  return {
    isOnline,
    connectionType,
    effectiveType,
    isSlowConnection: effectiveType === '2g' || effectiveType === 'slow-2g',
  };
};

export default useOfflineContent;
