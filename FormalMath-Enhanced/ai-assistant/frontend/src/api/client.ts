"""
AI助手前端API客户端
"""
const API_BASE = '/api/v1/ai-assistant';

export interface AskRequest {
  question: string;
  context_id?: string;
  user_id?: string;
}

export interface AssistantResponse {
  answer: string;
  answer_type: string;
  confidence: number;
  context_id?: string;
  suggestions: string[];
  references: any[];
  latex_formulas: string[];
  proof_steps: string[];
  timestamp: string;
}

export interface ExplainRequest {
  concept: string;
  level?: 'beginner' | 'intermediate' | 'advanced';
  context_id?: string;
}

export interface ProofHintRequest {
  theorem: string;
  user_attempt?: string;
  context_id?: string;
}

export interface LearningAdviceRequest {
  goal: string;
  user_id?: string;
  context_id?: string;
}

export interface ProblemSolveRequest {
  problem: string;
  show_steps?: boolean;
  context_id?: string;
}

export interface LeanHelpRequest {
  statement: string;
  context_id?: string;
}

class AIAssistantClient {
  private baseUrl: string;

  constructor(baseUrl: string = API_BASE) {
    this.baseUrl = baseUrl;
  }

  private async fetch<T>(endpoint: string, options?: RequestInit): Promise<T> {
    const response = await fetch(`${this.baseUrl}${endpoint}`, {
      ...options,
      headers: {
        'Content-Type': 'application/json',
        ...options?.headers,
      },
    });

    if (!response.ok) {
      throw new Error(`API错误: ${response.status}`);
    }

    return response.json();
  }

  // 通用问答
  async ask(request: AskRequest): Promise<AssistantResponse> {
    return this.fetch('/ask', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // 概念解释
  async explain(request: ExplainRequest): Promise<AssistantResponse> {
    return this.fetch('/explain', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // 证明提示
  async getProofHint(request: ProofHintRequest): Promise<AssistantResponse> {
    return this.fetch('/proof-hint', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // 学习建议
  async getLearningAdvice(request: LearningAdviceRequest): Promise<AssistantResponse> {
    return this.fetch('/learning-advice', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // 问题解答
  async solve(request: ProblemSolveRequest): Promise<AssistantResponse> {
    return this.fetch('/solve', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // Lean帮助
  async leanHelp(request: LeanHelpRequest): Promise<AssistantResponse> {
    return this.fetch('/lean-help', {
      method: 'POST',
      body: JSON.stringify(request),
    });
  }

  // 创建对话
  async createConversation(userId?: string, topic?: string): Promise<{ session_id: string }> {
    return this.fetch('/conversations', {
      method: 'POST',
      body: JSON.stringify({ user_id: userId, topic }),
    });
  }

  // 获取对话
  async getConversation(sessionId: string): Promise<any> {
    return this.fetch(`/conversations/${sessionId}`);
  }

  // 获取建议问题
  async suggestQuestions(topic: string, k: number = 5): Promise<{ suggestions: string[] }> {
    return this.fetch(`/suggest-questions?topic=${encodeURIComponent(topic)}&k=${k}`);
  }
}

export const aiClient = new AIAssistantClient();
export default aiClient;
