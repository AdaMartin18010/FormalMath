/**
 * 解谜游戏 Hook
 * 提供谜题游戏的核心逻辑和状态管理
 */

import { useState, useCallback, useRef, useEffect } from 'react';
import useGameStore from '../../stores/gameStore';
import type { Puzzle, GameReward, PuzzleType, GameDifficulty } from '../../types/gamification';

interface UsePuzzleOptions {
  autoStart?: boolean;
  onComplete?: (result: {
    correct: boolean;
    score: number;
    rewards: GameReward[];
    timeSpent: number;
  }) => void;
  onError?: (error: Error) => void;
}

interface UsePuzzleReturn {
  // 状态
  puzzle: Puzzle | null;
  isLoading: boolean;
  isPlaying: boolean;
  isCompleted: boolean;
  timeSpent: number;
  hintsUsed: string[];
  score: number;
  feedback: string | null;
  result: {
    correct: boolean;
    score: number;
    rewards: GameReward[];
    feedback: string;
  } | null;

  // 方法
  startPuzzle: (puzzleId: string) => Promise<void>;
  submitAnswer: (answer: unknown) => Promise<void>;
  useHint: (hintId: string) => Promise<boolean>;
  resetPuzzle: () => void;
  pauseTimer: () => void;
  resumeTimer: () => void;

  // 数据获取
  loadPuzzles: (filters?: {
    type?: PuzzleType;
    difficulty?: GameDifficulty;
    conceptId?: string;
  }) => Promise<void>;
  puzzles: Puzzle[];
}

export function usePuzzle(options: UsePuzzleOptions = {}): UsePuzzleReturn {
  const store = useGameStore();
  const [feedback, setFeedback] = useState<string | null>(null);
  const [result, setResult] = useState<UsePuzzleReturn['result']>(null);
  const [localTimeSpent, setLocalTimeSpent] = useState(0);
  const [localHintsUsed, setLocalHintsUsed] = useState<string[]>([]);
  const timerRef = useRef<NodeJS.Timeout | null>(null);
  const isPausedRef = useRef(false);

  // 清理计时器
  useEffect(() => {
    return () => {
      if (timerRef.current) {
        clearInterval(timerRef.current);
      }
    };
  }, []);

  // 开始计时
  const startTimer = useCallback(() => {
    if (timerRef.current) {
      clearInterval(timerRef.current);
    }
    isPausedRef.current = false;
    timerRef.current = setInterval(() => {
      if (!isPausedRef.current) {
        setLocalTimeSpent((prev) => prev + 1);
      }
    }, 1000);
  }, []);

  // 停止计时
  const stopTimer = useCallback(() => {
    if (timerRef.current) {
      clearInterval(timerRef.current);
      timerRef.current = null;
    }
  }, []);

  // 开始谜题
  const startPuzzle = useCallback(
    async (puzzleId: string) => {
      try {
        setFeedback(null);
        setResult(null);
        setLocalTimeSpent(0);
        setLocalHintsUsed([]);
        await store.startPuzzle(puzzleId);
        startTimer();
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, startTimer, options]
  );

  // 提交答案
  const submitAnswer = useCallback(
    async (answer: unknown) => {
      try {
        stopTimer();
        const response = await store.submitPuzzleAnswer(
          answer,
          localTimeSpent,
          localHintsUsed.length
        );
        
        setResult(response);
        setFeedback(response.feedback);

        if (options.onComplete) {
          options.onComplete({
            correct: response.correct,
            score: response.score,
            rewards: response.rewards,
            timeSpent: localTimeSpent,
          });
        }
      } catch (error) {
        options.onError?.(error as Error);
      }
    },
    [store, localTimeSpent, localHintsUsed, stopTimer, options]
  );

  // 使用提示
  const useHint = useCallback(
    async (hintId: string) => {
      if (store.activePuzzle) {
        const success = await store.useHint(store.activePuzzle.id, hintId);
        if (success) {
          setLocalHintsUsed((prev) => [...prev, hintId]);
        }
        return success;
      }
      return false;
    },
    [store]
  );

  // 重置谜题
  const resetPuzzle = useCallback(() => {
    stopTimer();
    store.endSession();
    setFeedback(null);
    setResult(null);
    setLocalTimeSpent(0);
    setLocalHintsUsed([]);
  }, [store, stopTimer]);

  // 暂停计时
  const pauseTimer = useCallback(() => {
    isPausedRef.current = true;
  }, []);

  // 恢复计时
  const resumeTimer = useCallback(() => {
    isPausedRef.current = false;
  }, []);

  // 加载谜题列表
  const loadPuzzles = useCallback(
    async (filters?: {
      type?: PuzzleType;
      difficulty?: GameDifficulty;
      conceptId?: string;
    }) => {
      await store.loadPuzzles(filters);
    },
    [store]
  );

  return {
    puzzle: store.activePuzzle || null,
    isLoading: store.isLoading,
    isPlaying: !!store.activePuzzle && !result,
    isCompleted: !!result,
    timeSpent: localTimeSpent,
    hintsUsed: localHintsUsed,
    score: store.currentSession?.score || 0,
    feedback,
    result,
    startPuzzle,
    submitAnswer,
    useHint,
    resetPuzzle,
    pauseTimer,
    resumeTimer,
    loadPuzzles,
    puzzles: store.puzzles,
  };
}

export default usePuzzle;
