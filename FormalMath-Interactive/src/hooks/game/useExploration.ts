/**
 * 探索模式 Hook
 * 提供数学世界探索、历史时间线和概念收集的功能
 */

import { useState, useCallback, useEffect } from 'react';
import useGameStore from '../../stores/gameStore';
import type {
  MathWorld,
  HistoryTimeline,
  ExplorationSession,
  ExplorationMode,
  CollectionItem,
  GameReward,
  Quest,
} from '../../types/gamification';

interface UseExplorationOptions {
  onNodeDiscover?: (nodeId: string, rewards: GameReward[]) => void;
  onItemCollect?: (item: CollectionItem) => void;
  onQuestComplete?: (quest: Quest) => void;
  onError?: (error: Error) => void;
}

interface UseExplorationReturn {
  // 世界探索
  worlds: MathWorld[];
  currentWorld: MathWorld | null;
  explorationSession: ExplorationSession | null;
  isExploring: boolean;
  explorationProgress: {
    totalNodes: number;
    visitedCount: number;
    unlockedCount: number;
    completionRate: number;
  };

  // 历史时间线
  timeline: HistoryTimeline | null;

  // 收集
  collection: CollectionItem[];
  collectedCount: number;
  totalCollectibles: number;

  // 方法 - 探索
  loadWorlds: () => Promise<void>;
  startExploration: (mode: ExplorationMode, worldId?: string) => Promise<void>;
  endExploration: () => void;
  exploreNode: (nodeId: string) => Promise<void>;
  teleportTo: (nodeId: string) => void;

  // 方法 - 时间线
  loadTimeline: () => Promise<void>;
  visitTimelineEvent: (eventId: string) => Promise<GameReward[]>;

  // 方法 - 收集
  loadCollection: () => Promise<void>;
  collectItem: (itemId: string) => Promise<void>;
  getItemsByRarity: (rarity: CollectionItem['rarity']) => CollectionItem[];
  getItemsByCategory: (category: string) => CollectionItem[];

  // 状态
  isLoading: boolean;
  currentPosition: { x: number; y: number } | null;
}

export function useExploration(options: UseExplorationOptions = {}): UseExplorationReturn {
  const store = useGameStore();
  const [currentWorldId, setCurrentWorldId] = useState<string | null>(null);

  const currentWorld =
    store.worlds.find((w) => w.id === currentWorldId) || store.worlds[0] || null;
  
  const explorationSession = store.activeExploration || null;
  const isExploring = !!explorationSession;

  const collectedCount = store.collection.filter((i) => i.isUnlocked).length;
  const totalCollectibles = store.collection.length;

  // 加载世界
  const loadWorlds = useCallback(async () => {
    try {
      await store.loadWorlds();
    } catch (error) {
      options.onError?.(error as Error);
    }
  }, [store, options]);

  // 开始探索
  const startExploration = useCallback(
    async (mode: ExplorationMode, worldId?: string) => {
      try {
        if (worldId) {
          setCurrentWorldId(worldId);
        }
        await store.startExploration(mode, worldId);
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, options]
  );

  // 结束探索
  const endExploration = useCallback(() => {
    store.endSession();
    setCurrentWorldId(null);
  }, [store]);

  // 探索节点
  const exploreNode = useCallback(
    async (nodeId: string) => {
      try {
        await store.exploreNode(nodeId);
        // 触发发现回调
        const region = currentWorld?.regions.find((r) => r.id === nodeId);
        if (region && options.onNodeDiscover) {
          options.onNodeDiscover(nodeId, []);
        }
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, currentWorld, options]
  );

  // 传送到节点
  const teleportTo = useCallback(
    (nodeId: string) => {
      // 检查是否已解锁
      if (explorationSession?.unlockedNodes.includes(nodeId)) {
        // 更新当前位置
      }
    },
    [explorationSession]
  );

  // 加载时间线
  const loadTimeline = useCallback(async () => {
    try {
      await store.loadTimeline();
    } catch (error) {
      options.onError?.(error as Error);
    }
  }, [store, options]);

  // 访问时间线事件
  const visitTimelineEvent = useCallback(
    async (eventId: string) => {
      try {
        // 返回奖励
        const rewards: GameReward[] = [{ type: 'xp', amount: 20 }];
        await store.addXP(20);
        return rewards;
      } catch (error) {
        options.onError?.(error as Error);
        return [];
      }
    },
    [store, options]
  );

  // 加载收集
  const loadCollection = useCallback(async () => {
    try {
      await store.loadCollection();
    } catch (error) {
      options.onError?.(error as Error);
    }
  }, [store, options]);

  // 收集物品
  const collectItem = useCallback(
    async (itemId: string) => {
      try {
        await store.collectItem(itemId);
        const item = store.collection.find((i) => i.id === itemId);
        if (item && options.onItemCollect) {
          options.onItemCollect(item);
        }
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, options]
  );

  // 按稀有度筛选
  const getItemsByRarity = useCallback(
    (rarity: CollectionItem['rarity']) => {
      return store.collection.filter((item) => item.rarity === rarity);
    },
    [store.collection]
  );

  // 按分类筛选
  const getItemsByCategory = useCallback(
    (category: string) => {
      // 根据分类筛选
      return store.collection;
    },
    [store.collection]
  );

  // 初始化加载
  useEffect(() => {
    loadWorlds();
    loadTimeline();
    loadCollection();
  }, []);

  return {
    worlds: store.worlds,
    currentWorld,
    explorationSession,
    isExploring,
    explorationProgress: explorationSession?.progress || {
      totalNodes: 0,
      visitedCount: 0,
      unlockedCount: 0,
      completionRate: 0,
    },
    timeline: store.timeline,
    collection: store.collection,
    collectedCount,
    totalCollectibles,
    loadWorlds,
    startExploration,
    endExploration,
    exploreNode,
    teleportTo,
    loadTimeline,
    visitTimelineEvent,
    loadCollection,
    collectItem,
    getItemsByRarity,
    getItemsByCategory,
    isLoading: store.isLoading,
    currentPosition: explorationSession?.currentPosition
      ? { x: explorationSession.currentPosition.x, y: explorationSession.currentPosition.y }
      : null,
  };
}

export default useExploration;
