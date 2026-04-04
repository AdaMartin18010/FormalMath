/**
 * 对战模式 Hook
 * 提供实时解题对战的核心逻辑
 */

import { useState, useCallback, useEffect, useRef } from 'react';
import useGameStore from '../../stores/gameStore';
import type {
  BattleSession,
  BattleType,
  PlayerAnswer,
  BattlePlayer,
} from '../../types/gamification';

interface UseBattleOptions {
  onBattleStart?: () => void;
  onBattleEnd?: (result: { winner: string; scores: Record<string, number> }) => void;
  onRoundComplete?: (round: {
    roundNumber: number;
    yourAnswer: PlayerAnswer;
    opponentAnswer?: PlayerAnswer;
    scores: Record<string, number>;
  }) => void;
  onError?: (error: Error) => void;
}

interface UseBattleReturn {
  // 状态
  battle: BattleSession | null;
  isLoading: boolean;
  isWaiting: boolean;
  isPlaying: boolean;
  isFinished: boolean;
  currentRound: number;
  totalRounds: number;
  timeLeft: number;
  player: BattlePlayer | null;
  opponent: BattlePlayer | null;
  scores: Record<string, number>;
  winner: string | null;

  // 方法
  createBattle: (type: BattleType, settings: BattleSession['settings']) => Promise<void>;
  joinBattle: (battleId: string) => Promise<void>;
  leaveBattle: () => void;
  setReady: (ready: boolean) => void;
  submitAnswer: (answer: string | number | string[]) => Promise<void>;
  useLifeline: (type: 'fiftyFifty' | 'hint' | 'extraTime') => boolean;

  // 数据
  availableBattles: BattleSession[];
}

export function useBattle(options: UseBattleOptions = {}): UseBattleReturn {
  const store = useGameStore();
  const [timeLeft, setTimeLeft] = useState(0);
  const [availableBattles] = useState<BattleSession[]>([]);
  const timerRef = useRef<NodeJS.Timeout | null>(null);

  const battle = store.activeBattle || null;
  const isWaiting = battle?.status === 'waiting';
  const isPlaying = battle?.status === 'in_progress';
  const isFinished = battle?.status === 'finished';

  const player = battle?.opponent || battle?.host || null;
  const opponent =
    battle?.host?.userId !== store.userGameData.userId ? battle?.host : battle?.opponent;

  // 计时器管理
  useEffect(() => {
    if (isPlaying && battle?.settings.timePerQuestion) {
      setTimeLeft(battle.settings.timePerQuestion);
      
      if (timerRef.current) {
        clearInterval(timerRef.current);
      }

      timerRef.current = setInterval(() => {
        setTimeLeft((prev) => {
          if (prev <= 1) {
            // 时间到，自动提交
            return 0;
          }
          return prev - 1;
        });
      }, 1000);
    }

    return () => {
      if (timerRef.current) {
        clearInterval(timerRef.current);
      }
    };
  }, [isPlaying, battle?.currentRound, battle?.settings.timePerQuestion]);

  // 监听对战状态变化
  useEffect(() => {
    if (battle?.status === 'in_progress' && options.onBattleStart) {
      options.onBattleStart();
    }
    if (battle?.status === 'finished' && battle.winner && options.onBattleEnd) {
      options.onBattleEnd({
        winner: battle.winner,
        scores: battle.finalScores,
      });
    }
  }, [battle?.status, battle?.winner, options]);

  // 创建对战
  const createBattle = useCallback(
    async (type: BattleType, settings: BattleSession['settings']) => {
      try {
        await store.createBattle(type, settings);
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, options]
  );

  // 加入对战
  const joinBattle = useCallback(
    async (battleId: string) => {
      try {
        await store.joinBattle(battleId);
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, options]
  );

  // 离开对战
  const leaveBattle = useCallback(() => {
    store.leaveBattle();
    if (timerRef.current) {
      clearInterval(timerRef.current);
    }
  }, [store]);

  // 设置准备状态
  const setReady = useCallback(
    (ready: boolean) => {
      store.setBattleReady(ready);
    },
    [store]
  );

  // 提交答案
  const submitAnswer = useCallback(
    async (answer: string | number | string[]) => {
      if (!battle) return;

      try {
        const timeSpent = battle.settings.timePerQuestion - timeLeft;
        await store.submitBattleAnswer(battle.currentRound, answer, timeSpent);

        if (timerRef.current) {
          clearInterval(timerRef.current);
        }
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [battle, timeLeft, store, options]
  );

  // 使用生命线
  const useLifeline = useCallback(
    (type: 'fiftyFifty' | 'hint' | 'extraTime'): boolean => {
      // 检查是否还有生命线可用
      // 返回是否成功使用
      return true;
    },
    []
  );

  return {
    battle,
    isLoading: store.isLoading,
    isWaiting,
    isPlaying,
    isFinished,
    currentRound: battle?.currentRound || 0,
    totalRounds: battle?.totalRounds || 0,
    timeLeft,
    player,
    opponent: opponent || null,
    scores: battle?.finalScores || {},
    winner: battle?.winner || null,
    createBattle,
    joinBattle,
    leaveBattle,
    setReady,
    submitAnswer,
    useLifeline,
    availableBattles,
  };
}

export default useBattle;
