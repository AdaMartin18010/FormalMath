// ==================== 练习系统 Hooks ====================

import { useState, useCallback, useMemo, useEffect } from 'react';
import type {
  Exercise,
  ExerciseType,
  DifficultyLevel,
  UserAnswer,
  ValidationResult,
  StepHint,
  ExerciseSettings,
  ExerciseSession,
  MistakeRecord,
  ErrorType,
  ExerciseProgress,
} from '../types/exercise';
import { exerciseValidator } from '../services/exerciseValidator';
import { hintService } from '../services/hintService';
import { 
  mistakeBookService, 
  ERROR_TYPE_LABELS,
  MASTERY_LEVEL_LABELS,
  MASTERY_LEVEL_COLORS,
} from '../services/mistakeBookService';

/** 练习状态 */
interface ExerciseState {
  currentExercise: Exercise | null;
  userAnswer: unknown;
  validationResult: ValidationResult | null;
  revealedHints: number;
  hints: StepHint[];
  isSubmitting: boolean;
  showSolution: boolean;
  timeSpent: number;
  attempts: number;
}

/** 练习 Hook 配置 */
interface UseExerciseOptions {
  userId: string;
  settings?: Partial<ExerciseSettings>;
  onExerciseComplete?: (result: ValidationResult, timeSpent: number) => void;
  onMistakeRecorded?: (mistake: MistakeRecord) => void;
}

/** 默认设置 */
const defaultSettings: ExerciseSettings = {
  showHintButton: true,
  showSolutionButton: true,
  autoShowSolution: false,
  autoAdvance: false,
  allowSkip: true,
  requireExplanation: false,
  immediateFeedback: true,
  showCorrectAnswer: true,
  showDetailedFeedback: true,
  adaptiveDifficulty: true,
  spacedRepetition: true,
  dailyGoal: 10,
};

/**
 * 单个练习 Hook
 */
export function useExercise(options: UseExerciseOptions) {
  const { userId, settings: userSettings, onExerciseComplete, onMistakeRecorded } = options;
  const settings = useMemo(() => ({ ...defaultSettings, ...userSettings }), [userSettings]);

  const [state, setState] = useState<ExerciseState>({
    currentExercise: null,
    userAnswer: undefined,
    validationResult: null,
    revealedHints: 0,
    hints: [],
    isSubmitting: false,
    showSolution: false,
    timeSpent: 0,
    attempts: 0,
  });

  const [timer, setTimer] = useState<NodeJS.Timeout | null>(null);

  // 计时器
  useEffect(() => {
    if (state.currentExercise && !state.validationResult) {
      const interval = setInterval(() => {
        setState(prev => ({ ...prev, timeSpent: prev.timeSpent + 1 }));
      }, 1000);
      setTimer(interval);
      return () => clearInterval(interval);
    } else if (timer) {
      clearInterval(timer);
      setTimer(null);
    }
  }, [state.currentExercise, state.validationResult]);

  /**
   * 加载练习
   */
  const loadExercise = useCallback((exercise: Exercise) => {
    const hints = hintService.getAllHints(exercise);
    setState({
      currentExercise: exercise,
      userAnswer: undefined,
      validationResult: null,
      revealedHints: 0,
      hints: hints.map((h, i) => ({ ...h, revealed: false })),
      isSubmitting: false,
      showSolution: false,
      timeSpent: 0,
      attempts: 0,
    });
  }, []);

  /**
   * 更新答案
   */
  const setAnswer = useCallback((answer: unknown) => {
    setState(prev => ({ ...prev, userAnswer: answer }));
  }, []);

  /**
   * 提交答案
   */
  const submitAnswer = useCallback(async () => {
    if (!state.currentExercise || state.userAnswer === undefined) return;

    setState(prev => ({ ...prev, isSubmitting: true }));

    const result = exerciseValidator.validate(
      state.currentExercise,
      state.userAnswer
    );

    setState(prev => ({
      ...prev,
      validationResult: result,
      isSubmitting: false,
      attempts: prev.attempts + 1,
    }));

    // 记录错题
    if (!result.isCorrect) {
      const errorType = inferErrorType(state.currentExercise, state.userAnswer, result);
      const mistake = mistakeBookService.addMistake(
        state.currentExercise.id,
        userId,
        state.userAnswer,
        errorType,
        result
      );
      onMistakeRecorded?.(mistake);
    }

    onExerciseComplete?.(result, state.timeSpent);
  }, [state.currentExercise, state.userAnswer, state.timeSpent, userId, onExerciseComplete, onMistakeRecorded]);

  /**
   * 请求提示
   */
  const requestHint = useCallback(() => {
    if (!state.currentExercise) return;

    const hint = hintService.getHint(state.currentExercise, state.revealedHints);
    if (hint) {
      setState(prev => ({
        ...prev,
        revealedHints: prev.revealedHints + 1,
        hints: prev.hints.map((h, i) => 
          i === prev.revealedHints ? { ...h, revealed: true } : h
        ),
      }));
    }
  }, [state.currentExercise, state.revealedHints]);

  /**
   * 显示解答
   */
  const showSolution = useCallback(() => {
    setState(prev => ({ ...prev, showSolution: true }));
  }, []);

  /**
   * 跳过练习
   */
  const skipExercise = useCallback(() => {
    setState(prev => ({
      ...prev,
      validationResult: {
        isCorrect: false,
        score: 0,
        feedback: '已跳过此题',
      },
    }));
  }, []);

  /**
   * 重置练习
   */
  const resetExercise = useCallback(() => {
    if (!state.currentExercise) return;
    loadExercise(state.currentExercise);
  }, [state.currentExercise, loadExercise]);

  // 格式化时间
  const formattedTime = useMemo(() => {
    const minutes = Math.floor(state.timeSpent / 60);
    const seconds = state.timeSpent % 60;
    return `${minutes}:${seconds.toString().padStart(2, '0')}`;
  }, [state.timeSpent]);

  return {
    // 状态
    exercise: state.currentExercise,
    userAnswer: state.userAnswer,
    validationResult: state.validationResult,
    hints: state.hints.filter(h => h.revealed),
    revealedHintsCount: state.revealedHints,
    isSubmitting: state.isSubmitting,
    showSolution: state.showSolution,
    timeSpent: state.timeSpent,
    formattedTime,
    attempts: state.attempts,
    hasMoreHints: state.currentExercise ? state.revealedHints < state.currentExercise.maxHints : false,
    
    // 方法
    loadExercise,
    setAnswer,
    submitAnswer,
    requestHint,
    showSolution,
    skipExercise,
    resetExercise,
    settings,
  };
}

/**
 * 错题本 Hook
 */
export function useMistakeBook(userId: string) {
  const [mistakes, setMistakes] = useState<MistakeRecord[]>([]);
  const [overview, setOverview] = useState<ReturnType<typeof mistakeBookService.getMistakeOverview> | null>(null);
  const [loading, setLoading] = useState(false);

  // 加载错题数据
  useEffect(() => {
    setLoading(true);
    const allMistakes = mistakeBookService.getAllMistakes(userId);
    const overviewData = mistakeBookService.getMistakeOverview(userId);
    setMistakes(allMistakes);
    setOverview(overviewData);
    setLoading(false);
  }, [userId]);

  /**
   * 获取待复习错题
   */
  const getPendingReviews = useCallback(() => {
    return mistakeBookService.getPendingReviews(userId);
  }, [userId]);

  /**
   * 记录复习结果
   */
  const recordReview = useCallback((mistakeId: string, isCorrect: boolean, timeSpent: number, hintsUsed: number = 0) => {
    const updated = mistakeBookService.recordReview(mistakeId, isCorrect, timeSpent, hintsUsed);
    if (updated) {
      setMistakes(prev => prev.map(m => m.id === mistakeId ? updated : m));
      setOverview(mistakeBookService.getMistakeOverview(userId));
    }
    return updated;
  }, [userId]);

  /**
   * 获取推荐复习
   */
  const getRecommendedMistakes = useCallback((limit?: number) => {
    return mistakeBookService.getRecommendedMistakes(userId, limit);
  }, [userId]);

  /**
   * 删除错题
   */
  const deleteMistake = useCallback((mistakeId: string) => {
    const deleted = mistakeBookService.deleteMistake(mistakeId);
    if (deleted) {
      setMistakes(prev => prev.filter(m => m.id !== mistakeId));
      setOverview(mistakeBookService.getMistakeOverview(userId));
    }
    return deleted;
  }, [userId]);

  return {
    mistakes,
    overview,
    loading,
    getPendingReviews,
    recordReview,
    getRecommendedMistakes,
    deleteMistake,
    errorTypeLabels: ERROR_TYPE_LABELS,
    masteryLabels: MASTERY_LEVEL_LABELS,
    masteryColors: MASTERY_LEVEL_COLORS,
  };
}

/**
 * 练习会话 Hook
 */
export function useExerciseSession(userId: string) {
  const [session, setSession] = useState<ExerciseSession | null>(null);
  const [currentIndex, setCurrentIndex] = useState(0);

  /**
   * 开始新会话
   */
  const startSession = useCallback((exerciseIds: string[], config: Partial<ExerciseSession> = {}) => {
    const newSession: ExerciseSession = {
      id: `session_${Date.now()}`,
      userId,
      title: config.title || '练习会话',
      description: config.description,
      exerciseIds,
      shuffleOrder: config.shuffleOrder ?? false,
      timeLimit: config.timeLimit,
      allowHints: config.allowHints ?? true,
      maxAttempts: config.maxAttempts ?? 3,
      status: 'in_progress',
      currentIndex: 0,
      answers: {},
      startTime: new Date().toISOString(),
      totalScore: 0,
      maxPossibleScore: exerciseIds.length * 100,
      ...config,
    };

    if (newSession.shuffleOrder) {
      newSession.exerciseIds = shuffleArray(newSession.exerciseIds);
    }

    setSession(newSession);
    setCurrentIndex(0);
    return newSession;
  }, [userId]);

  /**
   * 提交答案
   */
  const submitAnswer = useCallback((exerciseId: string, answer: UserAnswer) => {
    setSession(prev => {
      if (!prev) return null;
      return {
        ...prev,
        answers: { ...prev.answers, [exerciseId]: answer },
      };
    });
  }, []);

  /**
   * 下一题
   */
  const nextExercise = useCallback(() => {
    if (!session) return;
    if (currentIndex < session.exerciseIds.length - 1) {
      setCurrentIndex(prev => prev + 1);
      setSession(prev => prev ? { ...prev, currentIndex: currentIndex + 1 } : null);
    } else {
      // 完成会话
      completeSession();
    }
  }, [session, currentIndex]);

  /**
   * 上一题
   */
  const previousExercise = useCallback(() => {
    if (currentIndex > 0) {
      setCurrentIndex(prev => prev - 1);
      setSession(prev => prev ? { ...prev, currentIndex: currentIndex - 1 } : null);
    }
  }, [currentIndex]);

  /**
   * 完成会话
   */
  const completeSession = useCallback(() => {
    setSession(prev => {
      if (!prev) return null;
      
      const totalScore = Object.values(prev.answers).reduce(
        (sum, answer) => sum + (answer.score || 0),
        0
      );

      return {
        ...prev,
        status: 'completed',
        endTime: new Date().toISOString(),
        totalScore,
      };
    });
  }, []);

  /**
   * 暂停会话
   */
  const pauseSession = useCallback(() => {
    setSession(prev => prev ? { ...prev, status: 'paused' } : null);
  }, []);

  /**
   * 恢复会话
   */
  const resumeSession = useCallback(() => {
    setSession(prev => prev ? { ...prev, status: 'in_progress' } : null);
  }, []);

  const progress = useMemo(() => {
    if (!session) return 0;
    return Math.round((Object.keys(session.answers).length / session.exerciseIds.length) * 100);
  }, [session]);

  return {
    session,
    currentIndex,
    currentExerciseId: session?.exerciseIds[currentIndex],
    progress,
    startSession,
    submitAnswer,
    nextExercise,
    previousExercise,
    pauseSession,
    resumeSession,
    completeSession,
  };
}

// ============ 辅助函数 ============

/**
 * 推断错误类型
 */
function inferErrorType(exercise: Exercise, userAnswer: unknown, result: ValidationResult): ErrorType {
  // 根据题型和答案特征推断错误类型
  if (exercise.type === 'calculation') {
    const userValue = parseFloat(userAnswer as string);
    const correctValue = parseFloat(exercise.correctAnswer as string);
    
    if (!isNaN(userValue) && !isNaN(correctValue)) {
      const error = Math.abs(userValue - correctValue);
      // 如果误差很小，可能是计算错误
      if (error < correctValue * 0.1) {
        return 'calculation_error';
      }
    }
    return 'formula_misapplication';
  }

  if (exercise.type === 'proof') {
    return 'logic_error';
  }

  if (result.score && result.score > 0 && result.score < 100) {
    return 'concept_misunderstanding';
  }

  return 'other';
}

/**
 * 随机打乱数组
 */
function shuffleArray<T>(array: T[]): T[] {
  const newArray = [...array];
  for (let i = newArray.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [newArray[i], newArray[j]] = [newArray[j], newArray[i]];
  }
  return newArray;
}

export default useExercise;
