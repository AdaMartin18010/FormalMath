import React, { useRef, useEffect } from 'react';
import { User, Bot, Copy, Check, ThumbsUp, ThumbsDown, RefreshCw } from 'lucide-react';
import { MarkdownRenderer } from './MarkdownRenderer';
import { ThinkingIndicator, StreamingIndicator } from './ThinkingIndicator';
import type { ChatMessage, DerivationStep } from '@types/aiAssistant';

interface MessageListProps {
  messages: ChatMessage[];
  isStreaming?: boolean;
  onRegenerate?: (messageId: string) => void;
  onFeedback?: (messageId: string, type: 'like' | 'dislike') => void;
}

/**
 * 消息列表组件
 * 
 * 功能特性：
 * - 消息气泡展示
 * - Markdown和数学公式渲染
 * - 代码高亮
 * - 复制功能
 * - 反馈功能
 * - 推导步骤展示
 * - 自动滚动
 */
export const MessageList: React.FC<MessageListProps> = ({
  messages,
  isStreaming = false,
  onRegenerate,
  onFeedback,
}) => {
  const scrollRef = useRef<HTMLDivElement>(null);
  const [copiedId, setCopiedId] = React.useState<string | null>(null);

  // 自动滚动到底部
  useEffect(() => {
    if (scrollRef.current) {
      scrollRef.current.scrollTop = scrollRef.current.scrollHeight;
    }
  }, [messages, isStreaming]);

  // 复制消息内容
  const handleCopy = async (content: string, messageId: string) => {
    try {
      await navigator.clipboard.writeText(content);
      setCopiedId(messageId);
      setTimeout(() => setCopiedId(null), 2000);
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  };

  if (messages.length === 0) {
    return (
      <div className="flex-1 flex items-center justify-center p-8">
        <div className="text-center text-gray-400">
          <Bot className="w-16 h-16 mx-auto mb-4 opacity-50" />
          <p className="text-lg font-medium">开始对话</p>
          <p className="text-sm mt-2">输入问题，AI助手将为您解答数学概念</p>
        </div>
      </div>
    );
  }

  return (
    <div 
      ref={scrollRef}
      className="flex-1 overflow-y-auto p-4 space-y-6"
    >
      {messages.map((message, index) => (
        <MessageItem
          key={message.id}
          message={message}
          isLast={index === messages.length - 1}
          copiedId={copiedId}
          onCopy={handleCopy}
          onRegenerate={onRegenerate}
          onFeedback={onFeedback}
        />
      ))}
      
      {/* 流式响应指示器 */}
      {isStreaming && (
        <div className="flex justify-start">
          <div className="bg-gray-100 rounded-2xl rounded-tl-none px-4 py-2">
            <StreamingIndicator />
          </div>
        </div>
      )}
    </div>
  );
};

// ==================== 消息项组件 ====================

interface MessageItemProps {
  message: ChatMessage;
  isLast: boolean;
  copiedId: string | null;
  onCopy: (content: string, messageId: string) => void;
  onRegenerate?: (messageId: string) => void;
  onFeedback?: (messageId: string, type: 'like' | 'dislike') => void;
}

const MessageItem: React.FC<MessageItemProps> = ({
  message,
  isLast,
  copiedId,
  onCopy,
  onRegenerate,
  onFeedback,
}) => {
  const isUser = message.role === 'user';
  const isError = !!message.error;

  return (
    <div className={`flex ${isUser ? 'justify-end' : 'justify-start'}`}>
      <div className={`flex gap-3 max-w-[85%] ${isUser ? 'flex-row-reverse' : 'flex-row'}`}>
        {/* 头像 */}
        <div className={`flex-shrink-0 w-8 h-8 rounded-full flex items-center justify-center ${
          isUser 
            ? 'bg-blue-600 text-white' 
            : isError 
              ? 'bg-red-100 text-red-600'
              : 'bg-gray-200 text-gray-600'
        }`}>
          {isUser ? <User className="w-5 h-5" /> : <Bot className="w-5 h-5" />}
        </div>

        {/* 消息内容 */}
        <div className={`flex flex-col ${isUser ? 'items-end' : 'items-start'}`}>
          {/* 气泡 */}
          <div className={`relative group ${
            isUser 
              ? 'bg-blue-600 text-white rounded-2xl rounded-tr-none' 
              : isError
                ? 'bg-red-50 text-red-800 border border-red-200 rounded-2xl rounded-tl-none'
                : 'bg-gray-100 text-gray-900 rounded-2xl rounded-tl-none'
          } px-4 py-3`}>
            {/* 错误消息 */}
            {isError ? (
              <div className="flex items-center gap-2">
                <span className="text-sm">{message.error}</span>
              </div>
            ) : (
              <>
                {/* Markdown内容 */}
                <div className={isUser ? '' : 'prose-p:my-0 prose-pre:my-0'}>
                  {isUser ? (
                    <p className="whitespace-pre-wrap">{message.content}</p>
                  ) : (
                    <MarkdownRenderer 
                      content={message.content}
                      enableMath={true}
                      enableCodeHighlight={true}
                    />
                  )}
                </div>

                {/* 推导步骤展示 */}
                {message.metadata?.derivationSteps && (
                  <DerivationSteps steps={message.metadata.derivationSteps} />
                )}

                {/* 相关概念 */}
                {message.metadata?.relatedConcepts && message.metadata.relatedConcepts.length > 0 && (
                  <RelatedConcepts concepts={message.metadata.relatedConcepts} />
                )}
              </>
            )}

            {/* 复制按钮 */}
            {!isUser && !isError && (
              <button
                onClick={() => onCopy(message.content, message.id)}
                className="absolute -right-8 top-0 p-1.5 text-gray-400 hover:text-gray-600 
                         opacity-0 group-hover:opacity-100 transition-opacity"
                title="复制内容"
              >
                {copiedId === message.id ? (
                  <Check className="w-4 h-4 text-green-500" />
                ) : (
                  <Copy className="w-4 h-4" />
                )}
              </button>
            )}
          </div>

          {/* 操作栏 */}
          {!isUser && !isError && (
            <div className="flex items-center gap-2 mt-1 opacity-0 group-hover:opacity-100 transition-opacity">
              {/* 反馈按钮 */}
              <button
                onClick={() => onFeedback?.(message.id, 'like')}
                className="p-1 text-gray-400 hover:text-green-600 transition-colors"
                title="有帮助"
              >
                <ThumbsUp className="w-3.5 h-3.5" />
              </button>
              <button
                onClick={() => onFeedback?.(message.id, 'dislike')}
                className="p-1 text-gray-400 hover:text-red-600 transition-colors"
                title="没帮助"
              >
                <ThumbsDown className="w-3.5 h-3.5" />
              </button>
              
              {/* 重新生成按钮（仅最后一条） */}
              {isLast && onRegenerate && (
                <button
                  onClick={() => onRegenerate(message.id)}
                  className="p-1 text-gray-400 hover:text-blue-600 transition-colors"
                  title="重新生成"
                >
                  <RefreshCw className="w-3.5 h-3.5" />
                </button>
              )}
            </div>
          )}

          {/* 时间戳 */}
          <span className="text-xs text-gray-400 mt-1">
            {message.timestamp.toLocaleTimeString('zh-CN', { 
              hour: '2-digit', 
              minute: '2-digit' 
            })}
          </span>
        </div>
      </div>
    </div>
  );
};

// ==================== 推导步骤组件 ====================

interface DerivationStepsProps {
  steps: DerivationStep[];
}

const DerivationSteps: React.FC<DerivationStepsProps> = ({ steps }) => {
  const [expanded, setExpanded] = React.useState(true);

  if (!steps || steps.length === 0) return null;

  return (
    <div className="mt-4 border border-blue-200 rounded-lg overflow-hidden">
      {/* 标题栏 */}
      <button
        onClick={() => setExpanded(!expanded)}
        className="w-full px-4 py-2 bg-blue-50 flex items-center justify-between text-sm font-medium text-blue-800"
      >
        <span>逐步推导</span>
        <span className="text-xs text-blue-600">
          {expanded ? '收起' : '展开'} ({steps.length}步)
        </span>
      </button>

      {/* 步骤列表 */}
      {expanded && (
        <div className="divide-y divide-blue-100">
          {steps.map((step) => (
            <div key={step.stepNumber} className="px-4 py-3 bg-white">
              <div className="flex gap-3">
                <span className="flex-shrink-0 w-6 h-6 bg-blue-100 text-blue-700 
                               rounded-full flex items-center justify-center text-xs font-medium">
                  {step.stepNumber}
                </span>
                <div className="flex-1">
                  <p className="text-gray-800">{step.statement}</p>
                  {step.latex && (
                    <code className="block mt-1 text-sm text-blue-600 bg-blue-50 px-2 py-1 rounded">
                      {step.latex}
                    </code>
                  )}
                  <p className="mt-1 text-xs text-gray-500">
                    依据: {step.justification}
                  </p>
                </div>
              </div>
            </div>
          ))}
        </div>
      )}
    </div>
  );
};

// ==================== 相关概念组件 ====================

interface RelatedConceptsProps {
  concepts: string[];
}

const RelatedConcepts: React.FC<RelatedConceptsProps> = ({ concepts }) => {
  if (!concepts || concepts.length === 0) return null;

  return (
    <div className="mt-4">
      <p className="text-xs text-gray-500 mb-2">相关概念:</p>
      <div className="flex flex-wrap gap-2">
        {concepts.map((concept) => (
          <button
            key={concept}
            className="px-3 py-1 text-xs bg-blue-50 text-blue-700 rounded-full 
                     hover:bg-blue-100 transition-colors"
          >
            {concept}
          </button>
        ))}
      </div>
    </div>
  );
};

export default MessageList;
