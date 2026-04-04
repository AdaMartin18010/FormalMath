/**
 * 实时数据分析 Hook
 * 支持 WebSocket 连接和轮询更新
 */

import { useEffect, useRef, useState, useCallback } from 'react';
import type {
  LearningProgressData,
  MasteryHeatmapData,
  EfficiencyAnalysisData,
  KnowledgeNetworkData,
  PredictionData,
} from '@types/analytics';

interface RealtimeConfig {
  enabled: boolean;
  interval?: number; // 轮询间隔（毫秒）
  useWebSocket?: boolean;
  wsUrl?: string;
}

interface RealtimeAnalyticsData {
  progress: LearningProgressData | null;
  heatmap: MasteryHeatmapData | null;
  efficiency: EfficiencyAnalysisData | null;
  network: KnowledgeNetworkData | null;
  prediction: PredictionData | null;
  lastUpdate: Date | null;
  isConnected: boolean;
}

interface UseRealtimeAnalyticsReturn extends RealtimeAnalyticsData {
  refresh: () => Promise<void>;
  connectionStatus: 'connected' | 'disconnected' | 'connecting' | 'error';
  error: Error | null;
}

const DEFAULT_CONFIG: RealtimeConfig = {
  enabled: true,
  interval: 30000, // 30秒
  useWebSocket: false,
};

/**
 * 实时数据分析 Hook
 */
export function useRealtimeAnalytics(
  userId: string,
  config: Partial<RealtimeConfig> = {}
): UseRealtimeAnalyticsReturn {
  const mergedConfig = { ...DEFAULT_CONFIG, ...config };
  
  const [data, setData] = useState<RealtimeAnalyticsData>({
    progress: null,
    heatmap: null,
    efficiency: null,
    network: null,
    prediction: null,
    lastUpdate: null,
    isConnected: false,
  });
  
  const [connectionStatus, setConnectionStatus] = useState<UseRealtimeAnalyticsReturn['connectionStatus']>('disconnected');
  const [error, setError] = useState<Error | null>(null);
  
  const wsRef = useRef<WebSocket | null>(null);
  const intervalRef = useRef<NodeJS.Timeout | null>(null);
  const isMountedRef = useRef(true);

  // 生成模拟实时数据更新
  const generateRealtimeUpdate = useCallback((currentData: RealtimeAnalyticsData): Partial<RealtimeAnalyticsData> => {
    const updates: Partial<RealtimeAnalyticsData> = {};
    
    // 模拟进度数据的微小变化
    if (currentData.progress) {
      const randomChange = Math.random() > 0.7;
      if (randomChange) {
        updates.progress = {
          ...currentData.progress,
          summary: {
            ...currentData.progress.summary,
            totalTimeSpent: currentData.progress.summary.totalTimeSpent + Math.floor(Math.random() * 5),
            weeklyStudyTime: currentData.progress.summary.weeklyStudyTime + Math.floor(Math.random() * 3),
          },
          generatedAt: new Date().toISOString(),
        };
      }
    }
    
    // 模拟热力图数据的微小变化
    if (currentData.heatmap && Math.random() > 0.8) {
      const randomCell = Math.floor(Math.random() * currentData.heatmap.cells.length);
      const newCells = [...currentData.heatmap.cells];
      const cell = newCells[randomCell];
      if (cell && cell.masteryLevel < 100) {
        newCells[randomCell] = {
          ...cell,
          masteryLevel: Math.min(100, cell.masteryLevel + Math.floor(Math.random() * 3)),
          studyCount: cell.studyCount + 1,
        };
        updates.heatmap = {
          ...currentData.heatmap,
          cells: newCells,
          generatedAt: new Date().toISOString(),
        };
      }
    }
    
    return updates;
  }, []);

  // 获取数据（模拟 API 调用）
  const fetchData = useCallback(async () => {
    try {
      setConnectionStatus('connecting');
      setError(null);
      
      // 模拟 API 调用延迟
      await new Promise(resolve => setTimeout(resolve, 500));
      
      if (!isMountedRef.current) return;
      
      // 生成新的模拟数据或更新现有数据
      setData(prev => {
        const updates = generateRealtimeUpdate(prev);
        return {
          ...prev,
          ...updates,
          lastUpdate: new Date(),
          isConnected: true,
        };
      });
      
      setConnectionStatus('connected');
    } catch (err) {
      if (!isMountedRef.current) return;
      setError(err instanceof Error ? err : new Error('获取数据失败'));
      setConnectionStatus('error');
    }
  }, [generateRealtimeUpdate]);

  // WebSocket 连接
  const connectWebSocket = useCallback(() => {
    if (!mergedConfig.useWebSocket || !mergedConfig.wsUrl) return;
    
    try {
      const ws = new WebSocket(`${mergedConfig.wsUrl}/analytics/${userId}`);
      
      ws.onopen = () => {
        if (!isMountedRef.current) return;
        setConnectionStatus('connected');
        setData(prev => ({ ...prev, isConnected: true }));
      };
      
      ws.onmessage = (event) => {
        if (!isMountedRef.current) return;
        try {
          const update = JSON.parse(event.data);
          setData(prev => ({
            ...prev,
            ...update,
            lastUpdate: new Date(),
          }));
        } catch (err) {
          console.error('WebSocket 消息解析失败:', err);
        }
      };
      
      ws.onerror = () => {
        if (!isMountedRef.current) return;
        setConnectionStatus('error');
        setData(prev => ({ ...prev, isConnected: false }));
      };
      
      ws.onclose = () => {
        if (!isMountedRef.current) return;
        setConnectionStatus('disconnected');
        setData(prev => ({ ...prev, isConnected: false }));
      };
      
      wsRef.current = ws;
    } catch (err) {
      setError(err instanceof Error ? err : new Error('WebSocket 连接失败'));
      setConnectionStatus('error');
    }
  }, [userId, mergedConfig.useWebSocket, mergedConfig.wsUrl]);

  // 刷新数据
  const refresh = useCallback(async () => {
    await fetchData();
  }, [fetchData]);

  // 初始化
  useEffect(() => {
    isMountedRef.current = true;
    
    if (mergedConfig.enabled) {
      if (mergedConfig.useWebSocket) {
        connectWebSocket();
      } else {
        fetchData();
        intervalRef.current = setInterval(fetchData, mergedConfig.interval);
      }
    }
    
    return () => {
      isMountedRef.current = false;
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }
      if (wsRef.current) {
        wsRef.current.close();
      }
    };
  }, [mergedConfig.enabled, mergedConfig.useWebSocket, mergedConfig.interval, connectWebSocket, fetchData]);

  return {
    ...data,
    refresh,
    connectionStatus,
    error,
  };
}

/**
 * 数据变化检测 Hook
 */
export function useDataChanges<T>(
  data: T,
  options: { compareFn?: (a: T, b: T) => boolean; debounceMs?: number } = {}
) {
  const { compareFn = (a, b) => JSON.stringify(a) === JSON.stringify(b), debounceMs = 100 } = options;
  const [hasChanges, setHasChanges] = useState(false);
  const prevDataRef = useRef<T>(data);
  const timeoutRef = useRef<NodeJS.Timeout | null>(null);

  useEffect(() => {
    const isEqual = compareFn(prevDataRef.current, data);
    
    if (!isEqual) {
      if (timeoutRef.current) {
        clearTimeout(timeoutRef.current);
      }
      
      timeoutRef.current = setTimeout(() => {
        setHasChanges(true);
        prevDataRef.current = data;
        
        // 重置变化标志
        setTimeout(() => setHasChanges(false), 2000);
      }, debounceMs);
    }
    
    return () => {
      if (timeoutRef.current) {
        clearTimeout(timeoutRef.current);
      }
    };
  }, [data, compareFn, debounceMs]);

  return hasChanges;
}

export default useRealtimeAnalytics;
