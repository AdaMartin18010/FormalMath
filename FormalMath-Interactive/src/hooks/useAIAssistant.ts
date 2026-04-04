// ==================== AI助手Hook ====================

import { useState, useCallback, useEffect, useRef } from 'react';
import { aiService, generateId, loadSessions, saveSessions } from '@services/aiService';
import type {
  ChatSession,
  ChatMessage,
  PageContext,
  AIRequestParams,
  QuickQuestion,
} from '@types/aiAssistant';

interface UseAIAssistantOptions {
  initialSessionId?: string;
  context?: PageContext;
  enableStreaming?: boolean;
}

interface UseAIAssistantReturn {
  // 状态
  sessions: ChatSession[];
  currentSession: ChatSession | null;
  isLoading: boolean;
  isStreaming: boolean;
  error: string | null;

  // 操作方法
  sendMessage: (message: string) => Promise<void>;
  createSession: () => ChatSession;
  selectSession: (sessionId: string) => void;
  deleteSession: (sessionId: string) => void;
  clearAllSessions: () => void;
  stopGeneration: () => void;
  askAboutSelection: (selection: string, questionType: 'explain' | 'prove' | 'apply' | 'relate') => Promise<void>;
  sendQuickQuestion: (question: QuickQuestion) => void;

  // 快捷提问
  quickQuestions: QuickQuestion[];
}

/**
 * AI助手Hook
 * 
 * 提供AI助手的核心功能，包括：
 * - 会话管理（创建、选择、删除）
 * - 消息发送（流式/非流式）
 * - 快捷提问
 * - 选中内容提问
 */
export function useAIAssistant(options: UseAIAssistantOptions = {}): UseAIAssistantReturn {
  const { initialSessionId, context, enableStreaming = true } = options;

  // ==================== 状态 ====================
  
  const [sessions, setSessions] = useState<ChatSession[]>([]);
  const [currentSession, setCurrentSession] = useState<ChatSession | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [isStreaming, setIsStreaming] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const abortControllerRef = useRef<AbortController | null>(null);

  // 快捷提问选项
  const quickQuestions: QuickQuestion[] = [
    { id: 'explain', label: '解释概念', question: '请解释这个概念的含义和作用', icon: 'lightbulb' },
    { id: 'prove', label: '查看证明', question: '请提供相关的证明或推导过程', icon: 'check' },
    { id: 'example', label: '举例说明', question: '请给出具体的例子说明', icon: 'book' },
    { id: 'relate', label: '相关概念', question: '这个概念与其他哪些概念相关', icon: 'link' },
  ];

  // ==================== 初始化 ====================

  useEffect(() => {
    const savedSessions = loadSessions();
    setSessions(savedSessions);

    if (initialSessionId) {
      const session = savedSessions.find(s => s.id === initialSessionId);
      if (session) {
        setCurrentSession(session);
      } else {
        createNewSession();
      }
    } else if (savedSessions.length > 0) {
      setCurrentSession(savedSessions[0]);
    } else {
      createNewSession();
    }
  }, [initialSessionId]);

  useEffect(() => {
    if (sessions.length > 0) {
      saveSessions(sessions);
    }
  }, [sessions]);

  // ==================== 会话管理 ====================

  const createNewSession = useCallback((): ChatSession => {
    const newSession: ChatSession = {
      id: generateId(),
      title: '新对话',
      messages: [],
      createdAt: new Date(),
      updatedAt: new Date(),
      context,
    };

    setSessions(prev => [newSession, ...prev]);
    setCurrentSession(newSession);
    return newSession;
  }, [context]);

  const createSession = useCallback((): ChatSession => {
    return createNewSession();
  }, [createNewSession]);

  const selectSession = useCallback((sessionId: string): void => {
    const session = sessions.find(s => s.id === sessionId);
    if (session) {
      setCurrentSession(session);
    }
  }, [sessions]);

  const deleteSession = useCallback((sessionId: string): void => {
    setSessions(prev => {
      const updated = prev.filter(s => s.id !== sessionId);

      if (currentSession?.id === sessionId) {
        if (updated.length > 0) {
          setCurrentSession(updated[0]);
        } else {
          const newSession = createNewSession();
          return [newSession];
        }
      }

      return updated;
    });
  }, [currentSession, createNewSession]);

  const clearAllSessions = useCallback((): void => {
    setSessions([]);
    createNewSession();
  }, [createNewSession]);

  // ==================== 消息发送 ====================

  const sendMessage = useCallback(async (message: string): Promise<void> => {
    if (!currentSession) return;

    setError(null);

    // 创建用户消息
    const userMessage: ChatMessage = {
      id: generateId(),
      role: 'user',
      content: message,
      timestamp: new Date(),
    };

    // 更新会话
    const updatedSession: ChatSession = {
      ...currentSession,
      messages: [...currentSession.messages, userMessage],
      updatedAt: new Date(),
    };

    setCurrentSession(updatedSession);
    setSessions(prev =>
      prev.map(s => s.id === updatedSession.id ? updatedSession : s)
    );

    setIsLoading(true);

    try {
      if (enableStreaming) {
        setIsStreaming(true);

        const assistantMessage: ChatMessage = {
          id: generateId(),
          role: 'assistant',
          content: '',
          timestamp: new Date(),
          isStreaming: true,
        };

        const sessionWithAssistant: ChatSession = {
          ...updatedSession,
          messages: [...updatedSession.messages, assistantMessage],
        };

        setCurrentSession(sessionWithAssistant);

        // 流式获取响应
        for await (const chunk of aiService.streamMessage({
          message,
          sessionId: currentSession.id,
          context: context || currentSession.context,
          history: updatedSession.messages,
        })) {
          assistantMessage.content += chunk.content;

          setCurrentSession(prev => {
            if (!prev) return prev;
            const messages = [...prev.messages];
            messages[messages.length - 1] = { ...assistantMessage };
            return { ...prev, messages };
          });
        }

        assistantMessage.isStreaming = false;

        finalizeSession(assistantMessage);
        setIsStreaming(false);
      } else {
        const response = await aiService.sendMessage({
          message,
          sessionId: currentSession.id,
          context: context || currentSession.context,
          history: updatedSession.messages,
        });

        const assistantMessage: ChatMessage = {
          id: response.messageId,
          role: 'assistant',
          content: response.message,
          timestamp: new Date(),
          metadata: response.metadata,
        };

        finalizeSession(assistantMessage);
      }
    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : '发送消息失败';
      setError(errorMessage);

      // 添加错误消息
      const errorChatMessage: ChatMessage = {
        id: generateId(),
        role: 'assistant',
        content: '',
        error: errorMessage,
        timestamp: new Date(),
      };

      finalizeSession(errorChatMessage);
    } finally {
      setIsLoading(false);
      setIsStreaming(false);
    }

    function finalizeSession(assistantMessage: ChatMessage) {
      const finalSession: ChatSession = {
        ...updatedSession,
        messages: [...updatedSession.messages, assistantMessage],
        updatedAt: new Date(),
      };

      setCurrentSession(finalSession);
      setSessions(prev => {
        const updated = prev.map(s =>
          s.id === currentSession.id ? finalSession : s
        );

        // 更新标题
        const session = updated.find(s => s.id === currentSession.id);
        if (session && session.messages.length === 2 && session.title === '新对话') {
          session.title = message.slice(0, 20) + (message.length > 20 ? '...' : '');
        }

        return updated;
      });
    }
  }, [currentSession, context, enableStreaming]);

  const stopGeneration = useCallback((): void => {
    aiService.abort();
    setIsStreaming(false);
    setIsLoading(false);
  }, []);

  // ==================== 快捷功能 ====================

  const askAboutSelection = useCallback(async (
    selection: string,
    questionType: 'explain' | 'prove' | 'apply' | 'relate'
  ): Promise<void> => {
    const prompts: Record<string, string> = {
      explain: `请详细解释以下内容：\n\n${selection}`,
      prove: `请为以下内容提供证明或推导：\n\n${selection}`,
      apply: `请举例说明以下内容的应用场景：\n\n${selection}`,
      relate: `请说明以下内容与其他相关概念的联系：\n\n${selection}`,
    };

    await sendMessage(prompts[questionType]);
  }, [sendMessage]);

  const sendQuickQuestion = useCallback((question: QuickQuestion): void => {
    let customizedQuestion = question.question;
    if (context?.currentConcept) {
      customizedQuestion = `关于"${context.currentConcept}"：${question.question}`;
    }
    sendMessage(customizedQuestion);
  }, [context, sendMessage]);

  return {
    sessions,
    currentSession,
    isLoading,
    isStreaming,
    error,
    sendMessage,
    createSession,
    selectSession,
    deleteSession,
    clearAllSessions,
    stopGeneration,
    askAboutSelection,
    sendQuickQuestion,
    quickQuestions,
  };
}

export default useAIAssistant;
