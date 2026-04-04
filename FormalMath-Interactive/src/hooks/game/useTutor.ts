/**
 * 虚拟导师 Hook
 * 提供AI数学导师的个性化指导功能
 */

import { useState, useCallback, useEffect, useRef } from 'react';
import useGameStore from '../../stores/gameStore';
import type {
  VirtualTutor,
  TutorMessage,
  GuidanceType,
  PersonalizedGuidance,
  LearningRecommendation,
  TutorPersonality,
} from '../../types/gamification';

interface UseTutorOptions {
  onMessage?: (message: TutorMessage) => void;
  onRecommendation?: (recommendations: LearningRecommendation[]) => void;
}

interface UseTutorReturn {
  // 导师状态
  tutor: VirtualTutor | null;
  isEnabled: boolean;
  personality: TutorPersonality;
  messages: TutorMessage[];
  
  // 个性化设置
  guidance: PersonalizedGuidance | null;
  recommendations: LearningRecommendation[];

  // 方法
  toggleTutor: () => void;
  setPersonality: (personality: TutorPersonality) => void;
  getHint: (context?: { puzzleId?: string; conceptId?: string }) => Promise<TutorMessage>;
  getExplanation: (conceptId: string) => Promise<TutorMessage>;
  getFeedback: (result: 'success' | 'failure' | 'hint_used') => Promise<TutorMessage>;
  getMotivation: () => Promise<TutorMessage>;
  getChallenge: () => Promise<TutorMessage>;
  askQuestion: (question: string) => Promise<TutorMessage>;
  clearMessages: () => void;

  // 推荐
  refreshRecommendations: () => Promise<void>;
  acceptRecommendation: (recommendationId: string) => void;
  dismissRecommendation: (recommendationId: string) => void;

  // 个性化
  updateLearningStyle: (style: PersonalizedGuidance['learningStyle']) => void;
  updateDifficultyPreference: (difficulty: PersonalizedGuidance['difficultyPreference']) => void;
  updateHintFrequency: (frequency: PersonalizedGuidance['hintFrequency']) => void;
}

export function useTutor(options: UseTutorOptions = {}): UseTutorReturn {
  const store = useGameStore();
  const [messages, setMessages] = useState<TutorMessage[]>([]);
  const [recommendations, setRecommendations] = useState<LearningRecommendation[]>([]);
  const lastInteractionRef = useRef<number>(Date.now());

  const tutor = store.tutor;
  const isEnabled = store.settings.tutorEnabled;
  const personality = store.settings.tutorPersonality;

  // 加载推荐
  const loadRecommendations = useCallback(async () => {
    try {
      const recs = await gameService.getLearningRecommendations(store.userGameData.userId);
      setRecommendations(recs);
      options.onRecommendation?.(recs);
    } catch (error) {
      console.error('Failed to load recommendations:', error);
    }
  }, [store.userGameData.userId, options]);

  // 添加消息
  const addMessage = useCallback(
    (message: TutorMessage) => {
      setMessages((prev) => [...prev, message]);
      options.onMessage?.(message);
      lastInteractionRef.current = Date.now();
    },
    [options]
  );

  // 切换导师
  const toggleTutor = useCallback(() => {
    store.setTutorEnabled(!isEnabled);
  }, [store, isEnabled]);

  // 设置性格
  const setPersonality = useCallback(
    (newPersonality: TutorPersonality) => {
      store.setTutorPersonality(newPersonality);
    },
    [store]
  );

  // 获取提示
  const getHint = useCallback(
    async (context?: { puzzleId?: string; conceptId?: string }) => {
      const message = await store.getTutorMessage('hint', context);
      addMessage(message);
      return message;
    },
    [store, addMessage]
  );

  // 获取解释
  const getExplanation = useCallback(
    async (conceptId: string) => {
      const message = await store.getTutorMessage('explanation', { conceptId });
      addMessage(message);
      return message;
    },
    [store, addMessage]
  );

  // 获取反馈
  const getFeedback = useCallback(
    async (result: 'success' | 'failure' | 'hint_used') => {
      const message = await store.getTutorMessage('feedback', { lastAction: result });
      addMessage(message);
      return message;
    },
    [store, addMessage]
  );

  // 获取激励
  const getMotivation = useCallback(async () => {
    const message = await store.getTutorMessage('motivation');
    addMessage(message);
    return message;
  }, [store, addMessage]);

  // 获取挑战
  const getChallenge = useCallback(async () => {
    const message = await store.getTutorMessage('challenge');
    addMessage(message);
    return message;
  }, [store, addMessage]);

  // 提问
  const askQuestion = useCallback(
    async (question: string) => {
      // 根据问题内容决定返回什么类型的消息
      let type: GuidanceType = 'explanation';
      if (question.includes('提示') || question.includes('怎么做')) {
        type = 'hint';
      } else if (question.includes('为什么')) {
        type = 'explanation';
      }
      
      const message = await store.getTutorMessage(type);
      addMessage(message);
      return message;
    },
    [store, addMessage]
  );

  // 清空消息
  const clearMessages = useCallback(() => {
    setMessages([]);
  }, []);

  // 刷新推荐
  const refreshRecommendations = useCallback(async () => {
    await loadRecommendations();
  }, [loadRecommendations]);

  // 接受推荐
  const acceptRecommendation = useCallback((recommendationId: string) => {
    setRecommendations((prev) => prev.filter((r) => r.id !== recommendationId));
  }, []);

  // 忽略推荐
  const dismissRecommendation = useCallback((recommendationId: string) => {
    setRecommendations((prev) => prev.filter((r) => r.id !== recommendationId));
  }, []);

  // 更新学习风格
  const updateLearningStyle = useCallback(
    (style: PersonalizedGuidance['learningStyle']) => {
      // 更新个性化设置
    },
    []
  );

  // 更新难度偏好
  const updateDifficultyPreference = useCallback(
    (difficulty: PersonalizedGuidance['difficultyPreference']) => {
      // 更新个性化设置
    },
    []
  );

  // 更新提示频率
  const updateHintFrequency = useCallback(
    (frequency: PersonalizedGuidance['hintFrequency']) => {
      // 更新个性化设置
    },
    []
  );

  // 自动激励（长时间无操作时）
  useEffect(() => {
    if (!isEnabled) return;

    const interval = setInterval(() => {
      const idleTime = Date.now() - lastInteractionRef.current;
      if (idleTime > 5 * 60 * 1000) {
        // 5分钟无操作
        getMotivation();
      }
    }, 60 * 1000);

    return () => clearInterval(interval);
  }, [isEnabled, getMotivation]);

  // 初始化加载
  useEffect(() => {
    store.loadTutor();
    loadRecommendations();
  }, []);

  return {
    tutor,
    isEnabled,
    personality,
    messages,
    guidance: null,
    recommendations,
    toggleTutor,
    setPersonality,
    getHint,
    getExplanation,
    getFeedback,
    getMotivation,
    getChallenge,
    askQuestion,
    clearMessages,
    refreshRecommendations,
    acceptRecommendation,
    dismissRecommendation,
    updateLearningStyle,
    updateDifficultyPreference,
    updateHintFrequency,
  };
}

// 临时模拟 gameService
const gameService = {
  getLearningRecommendations: async (userId: string): Promise<LearningRecommendation[]> => {
    return [
      {
        id: 'rec_1',
        type: 'next_puzzle',
        title: '继续挑战',
        description: '基于你的进度，推荐尝试下一个难度适中的证明题',
        reason: '你最近完成了3个方程求解题，证明能力有待提升',
        targetId: 'puzzle_002',
        priority: 1,
        estimatedTime: 15,
      },
    ];
  },
};

export default useTutor;
