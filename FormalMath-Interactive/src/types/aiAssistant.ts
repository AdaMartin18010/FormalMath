// ==================== AI助手类型定义 ====================

/**
 * 消息角色类型
 */
export type MessageRole = 'user' | 'assistant' | 'system';

/**
 * 消息内容类型
 */
export type ContentType = 'text' | 'latex' | 'code' | 'derivation' | 'error';

/**
 * 代码语言类型
 */
export type CodeLanguage = 'lean4' | 'latex' | 'python' | 'javascript' | 'typescript' | 'markdown' | 'text';

/**
 * 对话消息接口
 */
export interface ChatMessage {
  id: string;
  role: MessageRole;
  content: string;
  contentType?: ContentType;
  timestamp: Date;
  isStreaming?: boolean;
  error?: string;
  metadata?: {
    latexFormulas?: string[];
    codeBlocks?: CodeBlock[];
    relatedConcepts?: string[];
    derivationSteps?: DerivationStep[];
  };
}

/**
 * 代码块接口
 */
export interface CodeBlock {
  language: CodeLanguage;
  code: string;
  explanation?: string;
}

/**
 * 推导步骤接口
 */
export interface DerivationStep {
  stepNumber: number;
  statement: string;
  justification: string;
  latex?: string;
}

/**
 * 对话会话接口
 */
export interface ChatSession {
  id: string;
  title: string;
  messages: ChatMessage[];
  createdAt: Date;
  updatedAt: Date;
  context?: PageContext;
}

/**
 * 页面上下文接口
 */
export interface PageContext {
  pageType: 'knowledge-graph' | 'reasoning-tree' | 'mind-map' | 'comparison' | 'decision-tree' | 'evolution' | 'general';
  currentConcept?: string;
  selectedFormulas?: string[];
  selectedNode?: {
    id: string;
    label: string;
    type: string;
    description?: string;
  };
  learningPath?: string[];
}

/**
 * AI请求参数接口
 */
export interface AIRequestParams {
  message: string;
  sessionId?: string;
  context?: PageContext;
  history?: ChatMessage[];
  stream?: boolean;
  temperature?: number;
  maxTokens?: number;
}

/**
 * AI响应接口
 */
export interface AIResponse {
  message: string;
  messageId: string;
  metadata?: {
    relatedConcepts?: string[];
    suggestedQuestions?: string[];
    derivationSteps?: DerivationStep[];
  };
}

/**
 * 流式响应块接口
 */
export interface StreamChunk {
  content: string;
  isComplete: boolean;
  messageId?: string;
}

/**
 * AI服务配置接口
 */
export interface AIServiceConfig {
  apiKey?: string;
  baseURL?: string;
  model?: string;
  temperature?: number;
  maxTokens?: number;
  enableStreaming?: boolean;
  timeout?: number;
  retryCount?: number;
}

/**
 * AI助手状态接口
 */
export interface AIAssistantState {
  isOpen: boolean;
  isMinimized: boolean;
  currentSession: ChatSession | null;
  sessions: ChatSession[];
  isLoading: boolean;
  error: string | null;
}

/**
 * 快捷提问选项接口
 */
export interface QuickQuestion {
  id: string;
  label: string;
  question: string;
  icon?: string;
}

/**
 * 相关概念推荐接口
 */
export interface RelatedConcept {
  id: string;
  name: string;
  description: string;
  relevanceScore: number;
}

/**
 * 数学公式接口
 */
export interface MathFormula {
  id: string;
  latex: string;
  description?: string;
  variables?: Record<string, string>;
}

/**
 * AI助手Props接口
 */
export interface AIAssistantProps {
  initialOpen?: boolean;
  position?: 'right' | 'left' | 'floating';
  context?: PageContext;
  onClose?: () => void;
  onMessageSend?: (message: string) => void;
}
