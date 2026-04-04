// ==================== AI服务层 ====================

import type {
  AIRequestParams,
  AIResponse,
  StreamChunk,
  AIServiceConfig,
  ChatMessage,
  ChatSession,
} from '@types/aiAssistant';

// 默认配置
const DEFAULT_CONFIG: AIServiceConfig = {
  baseURL: import.meta.env.VITE_AI_API_BASE_URL || '/api/ai',
  model: import.meta.env.VITE_AI_MODEL || 'gpt-4',
  temperature: 0.7,
  maxTokens: 4096,
  enableStreaming: true,
  timeout: 60000,
  retryCount: 3,
};

/**
 * AI服务类
 */
export class AIService {
  private config: AIServiceConfig;
  private abortController: AbortController | null = null;

  constructor(config: Partial<AIServiceConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }

  /**
   * 发送消息并获取响应
   */
  async sendMessage(params: AIRequestParams): Promise<AIResponse> {
    const { message, context, history, sessionId } = params;

    try {
      const response = await this.fetchWithRetry('/chat', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          message,
          context,
          history: history?.map(msg => ({
            role: msg.role,
            content: msg.content,
          })),
          sessionId,
          model: this.config.model,
          temperature: params.temperature ?? this.config.temperature,
          maxTokens: params.maxTokens ?? this.config.maxTokens,
        }),
      });

      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }

      const data = await response.json();
      return {
        message: data.message,
        messageId: data.messageId,
        metadata: data.metadata,
      };
    } catch (error) {
      console.error('AI Service Error:', error);
      throw this.handleError(error);
    }
  }

  /**
   * 发送消息并获取流式响应
   */
  async *streamMessage(params: AIRequestParams): AsyncGenerator<StreamChunk, void, unknown> {
    const { message, context, history, sessionId } = params;

    this.abortController = new AbortController();

    try {
      const response = await fetch(`${this.config.baseURL}/chat/stream`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'Accept': 'text/event-stream',
        },
        body: JSON.stringify({
          message,
          context,
          history: history?.map(msg => ({
            role: msg.role,
            content: msg.content,
          })),
          sessionId,
          model: this.config.model,
          temperature: params.temperature ?? this.config.temperature,
          maxTokens: params.maxTokens ?? this.config.maxTokens,
        }),
        signal: this.abortController.signal,
      });

      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }

      const reader = response.body?.getReader();
      if (!reader) {
        throw new Error('Response body is null');
      }

      const decoder = new TextDecoder();
      let buffer = '';
      let messageId = '';

      while (true) {
        const { done, value } = await reader.read();
        
        if (done) {
          yield { content: '', isComplete: true, messageId };
          break;
        }

        buffer += decoder.decode(value, { stream: true });
        const lines = buffer.split('\n');
        buffer = lines.pop() || '';

        for (const line of lines) {
          if (line.startsWith('data: ')) {
            const data = line.slice(6);
            
            if (data === '[DONE]') {
              yield { content: '', isComplete: true, messageId };
              return;
            }

            try {
              const parsed = JSON.parse(data);
              
              if (parsed.messageId) {
                messageId = parsed.messageId;
              }

              yield {
                content: parsed.content || '',
                isComplete: false,
                messageId,
              };
            } catch (e) {
              console.warn('Failed to parse SSE data:', data);
            }
          }
        }
      }
    } catch (error) {
      if (error instanceof Error && error.name === 'AbortError') {
        console.log('Stream aborted');
        return;
      }
      console.error('Stream Error:', error);
      throw this.handleError(error);
    }
  }

  /**
   * 发送选中内容的快捷提问
   */
  async askAboutSelection(
    selection: string,
    questionType: 'explain' | 'prove' | 'apply' | 'relate',
    context?: AIRequestParams['context']
  ): Promise<AIResponse> {
    const prompts: Record<string, string> = {
      explain: `请详细解释以下内容：\n\n${selection}`,
      prove: `请为以下内容提供证明或推导：\n\n${selection}`,
      apply: `请举例说明以下内容的应用场景：\n\n${selection}`,
      relate: `请说明以下内容与其他相关概念的联系：\n\n${selection}`,
    };

    return this.sendMessage({
      message: prompts[questionType],
      context,
    });
  }

  /**
   * 获取学习路径推荐解释
   */
  async getLearningPathExplanation(
    conceptId: string,
    path: string[]
  ): Promise<AIResponse> {
    return this.sendMessage({
      message: `请解释为什么学习"${conceptId}"需要按照以下路径：${path.join(' → ')}`,
      context: {
        pageType: 'knowledge-graph',
        currentConcept: conceptId,
        learningPath: path,
      },
    });
  }

  /**
   * 生成会话标题
   */
  async generateSessionTitle(messages: ChatMessage[]): Promise<string> {
    if (messages.length === 0) return '新对话';

    const firstUserMessage = messages.find(m => m.role === 'user');
    if (!firstUserMessage) return '新对话';

    // 截取前20个字符作为标题
    const content = firstUserMessage.content;
    return content.length > 20 ? content.slice(0, 20) + '...' : content;
  }

  /**
   * 获取相关概念推荐
   */
  async getRelatedConcepts(conceptId: string): Promise<string[]> {
    try {
      const response = await this.fetchWithRetry(`/concepts/${conceptId}/related`, {
        method: 'GET',
      });

      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }

      const data = await response.json();
      return data.concepts || [];
    } catch (error) {
      console.error('Failed to get related concepts:', error);
      return [];
    }
  }

  /**
   * 取消当前请求
   */
  abort(): void {
    if (this.abortController) {
      this.abortController.abort();
      this.abortController = null;
    }
  }

  /**
   * 更新配置
   */
  updateConfig(config: Partial<AIServiceConfig>): void {
    this.config = { ...this.config, ...config };
  }

  /**
   * 获取当前配置
   */
  getConfig(): AIServiceConfig {
    return { ...this.config };
  }

  // ==================== 私有方法 ====================

  /**
   * 带重试的请求
   */
  private async fetchWithRetry(
    url: string,
    options: RequestInit,
    retryCount: number = this.config.retryCount || 3
  ): Promise<Response> {
    let lastError: Error | null = null;

    for (let i = 0; i < retryCount; i++) {
      try {
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), this.config.timeout);

        const response = await fetch(`${this.config.baseURL}${url}`, {
          ...options,
          signal: controller.signal,
        });

        clearTimeout(timeoutId);
        return response;
      } catch (error) {
        lastError = error instanceof Error ? error : new Error(String(error));
        
        // 如果是最后一次尝试，抛出错误
        if (i === retryCount - 1) {
          throw lastError;
        }

        // 指数退避重试
        const delay = Math.pow(2, i) * 1000;
        await new Promise(resolve => setTimeout(resolve, delay));
      }
    }

    throw lastError || new Error('Request failed');
  }

  /**
   * 错误处理
   */
  private handleError(error: unknown): Error {
    if (error instanceof Error) {
      if (error.name === 'AbortError') {
        return new Error('请求超时，请稍后重试');
      }
      if (error.message.includes('NetworkError')) {
        return new Error('网络连接失败，请检查网络设置');
      }
      if (error.message.includes('429')) {
        return new Error('请求过于频繁，请稍后再试');
      }
      if (error.message.includes('401')) {
        return new Error('API密钥无效或已过期');
      }
      if (error.message.includes('500')) {
        return new Error('服务器内部错误，请稍后重试');
      }
      return error;
    }
    return new Error('未知错误');
  }
}

// 导出单例实例
export const aiService = new AIService();

// ==================== 本地存储管理 ====================

const STORAGE_KEY = 'formalmath_ai_sessions';

/**
 * 保存会话到本地存储
 */
export function saveSessions(sessions: ChatSession[]): void {
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(sessions));
  } catch (error) {
    console.error('Failed to save sessions:', error);
  }
}

/**
 * 从本地存储加载会话
 */
export function loadSessions(): ChatSession[] {
  try {
    const data = localStorage.getItem(STORAGE_KEY);
    if (!data) return [];
    
    const sessions = JSON.parse(data);
    return sessions.map((session: ChatSession) => ({
      ...session,
      createdAt: new Date(session.createdAt),
      updatedAt: new Date(session.updatedAt),
      messages: session.messages.map((msg: ChatMessage) => ({
        ...msg,
        timestamp: new Date(msg.timestamp),
      })),
    }));
  } catch (error) {
    console.error('Failed to load sessions:', error);
    return [];
  }
}

/**
 * 清除所有会话
 */
export function clearSessions(): void {
  localStorage.removeItem(STORAGE_KEY);
}

/**
 * 生成唯一ID
 */
export function generateId(): string {
  return `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
}

export default AIService;
