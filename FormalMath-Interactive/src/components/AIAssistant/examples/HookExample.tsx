// @ts-nocheck
/**
 * useAIAssistant Hook使用示例
 * 
 * 展示如何使用Hook来构建自定义AI助手界面
 */

import React, { useState } from 'react';
import { useAIAssistant } from '@hooks/useAIAssistant';
import { MarkdownRenderer } from '../MarkdownRenderer';
import { ThinkingIndicator } from '../ThinkingIndicator';
import type { PageContext, ChatMessage } from '@types/aiAssistant';

// ==================== 示例1: 基础Hook使用 ====================

export const BasicHookExample: React.FC = () => {
  const {
    currentSession,
    isLoading,
    isStreaming,
    error,
    sendMessage,
    createSession,
    quickQuestions,
  } = useAIAssistant({
    context: {
      pageType: 'general',
    },
    enableStreaming: true,
  });

  const [input, setInput] = useState('');

  const handleSend = async () => {
    if (!input.trim()) return;
    await sendMessage(input);
    setInput('');
  };

  return (
    <div className="max-w-2xl mx-auto p-6">
      <h1 className="text-2xl font-bold mb-6">AI助手 (Hook版本)</h1>

      {/* 快捷问题 */}
      <div className="flex flex-wrap gap-2 mb-6">
        {quickQuestions.map((q) => (
          <button
            key={q.id}
            onClick={() => sendMessage(q.question)}
            className="px-4 py-2 bg-gray-100 text-gray-700 rounded-lg hover:bg-gray-200"
          >
            {q.label}
          </button>
        ))}
      </div>

      {/* 消息列表 */}
      <div className="space-y-4 mb-6 min-h-[300px] bg-gray-50 p-4 rounded-xl">
        {currentSession?.messages.map((msg) => (
          <MessageBubble key={msg.id} message={msg} />
        ))}
        
        {isLoading && !isStreaming && (
          <div className="bg-gray-100 rounded-2xl rounded-tl-none inline-block">
            <ThinkingIndicator message="AI正在思考" />
          </div>
        )}
      </div>

      {/* 错误提示 */}
      {error && (
        <div className="mb-4 p-3 bg-red-50 text-red-700 rounded-lg">
          错误: {error}
        </div>
      )}

      {/* 输入区域 */}
      <div className="flex gap-2">
        <input
          type="text"
          value={input}
          onChange={(e) => setInput(e.target.value)}
          onKeyDown={(e) => e.key === 'Enter' && handleSend()}
          placeholder="输入问题..."
          className="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500"
          disabled={isLoading}
        />
        <button
          onClick={handleSend}
          disabled={isLoading || !input.trim()}
          className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 disabled:opacity-50"
        >
          发送
        </button>
      </div>

      {/* 新建会话按钮 */}
      <button
        onClick={createSession}
        className="mt-4 text-sm text-gray-500 hover:text-gray-700"
      >
        + 新建会话
      </button>
    </div>
  );
};

// ==================== 消息气泡组件 ====================

const MessageBubble: React.FC<{ message: ChatMessage }> = ({ message }) => {
  const isUser = message.role === 'user';

  return (
    <div className={`flex ${isUser ? 'justify-end' : 'justify-start'}`}>
      <div
        className={`max-w-[80%] px-4 py-3 rounded-2xl ${
          isUser
            ? 'bg-blue-600 text-white rounded-tr-none'
            : 'bg-gray-100 text-gray-800 rounded-tl-none'
        }`}
      >
        {isUser ? (
          <p>{message.content}</p>
        ) : message.error ? (
          <p className="text-red-600">{message.error}</p>
        ) : (
          <MarkdownRenderer content={message.content} />
        )}
        
        {/* 推导步骤 */}
        {message.metadata?.derivationSteps && (
          <div className="mt-3 pt-3 border-t border-gray-200">
            <p className="text-sm font-medium text-gray-600 mb-2">推导步骤:</p>
            <ol className="space-y-2">
              {message.metadata.derivationSteps.map((step) => (
                <li key={step.stepNumber} className="text-sm">
                  <span className="font-medium">{step.stepNumber}.</span>{' '}
                  {step.statement}
                  {step.latex && (
                    <code className="block mt-1 text-blue-600 bg-blue-50 px-2 py-1 rounded">
                      {step.latex}
                    </code>
                  )}
                </li>
              ))}
            </ol>
          </div>
        )}
        
        {/* 相关概念 */}
        {message.metadata?.relatedConcepts && (
          <div className="mt-3 flex flex-wrap gap-2">
            {message.metadata.relatedConcepts.map((concept) => (
              <span
                key={concept}
                className="text-xs px-2 py-1 bg-blue-100 text-blue-700 rounded-full"
              >
                {concept}
              </span>
            ))}
          </div>
        )}
      </div>
    </div>
  );
};

// ==================== 示例2: 带上下文的Hook使用 ====================

export const ContextualHookExample: React.FC = () => {
  const [currentConcept, setCurrentConcept] = useState('群论');

  const context: PageContext = {
    pageType: 'knowledge-graph',
    currentConcept,
  };

  const {
    currentSession,
    isLoading,
    sendMessage,
    askAboutSelection,
  } = useAIAssistant({
    context,
    enableStreaming: true,
  });

  const concepts = ['群论', '环论', '域论', '线性代数', '拓扑学'];

  return (
    <div className="max-w-3xl mx-auto p-6">
      <h1 className="text-2xl font-bold mb-4">上下文感知AI助手</h1>

      {/* 概念选择器 */}
      <div className="mb-6">
        <p className="text-sm text-gray-600 mb-2">当前学习概念:</p>
        <div className="flex flex-wrap gap-2">
          {concepts.map((concept) => (
            <button
              key={concept}
              onClick={() => setCurrentConcept(concept)}
              className={`px-4 py-2 rounded-lg ${
                currentConcept === concept
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-100 text-gray-700 hover:bg-gray-200'
              }`}
            >
              {concept}
            </button>
          ))}
        </div>
      </div>

      {/* 公式快捷提问 */}
      <div className="grid grid-cols-2 gap-4 mb-6">
        <button
          onClick={() => askAboutSelection('群的定义', 'explain')}
          className="p-4 bg-white border border-gray-200 rounded-xl hover:shadow-md transition-shadow"
        >
          <h3 className="font-medium text-gray-800">解释"群的定义"</h3>
          <p className="text-sm text-gray-500 mt-1">关于{currentConcept}</p>
        </button>
        <button
          onClick={() => askAboutSelection('重要定理', 'prove')}
          className="p-4 bg-white border border-gray-200 rounded-xl hover:shadow-md transition-shadow"
        >
          <h3 className="font-medium text-gray-800">证明思路</h3>
          <p className="text-sm text-gray-500 mt-1">关于{currentConcept}</p>
        </button>
      </div>

      {/* 消息列表 */}
      <div className="space-y-4 mb-6 bg-gray-50 p-4 rounded-xl min-h-[200px]">
        {currentSession?.messages.map((msg) => (
          <MessageBubble key={msg.id} message={msg} />
        ))}
        {isLoading && (
          <div className="bg-gray-100 rounded-2xl rounded-tl-none inline-block">
            <ThinkingIndicator />
          </div>
        )}
      </div>

      {/* 输入框 */}
      <InputWithSend onSend={sendMessage} disabled={isLoading} />
    </div>
  );
};

// ==================== 输入组件 ====================

const InputWithSend: React.FC<{
  onSend: (msg: string) => void;
  disabled?: boolean;
}> = ({ onSend, disabled }) => {
  const [input, setInput] = useState('');

  const handleSend = () => {
    if (input.trim()) {
      onSend(input);
      setInput('');
    }
  };

  return (
    <div className="flex gap-2">
      <input
        type="text"
        value={input}
        onChange={(e) => setInput(e.target.value)}
        onKeyDown={(e) => e.key === 'Enter' && handleSend()}
        placeholder="询问关于当前概念的问题..."
        className="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500"
        disabled={disabled}
      />
      <button
        onClick={handleSend}
        disabled={disabled || !input.trim()}
        className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 disabled:opacity-50"
      >
        发送
      </button>
    </div>
  );
};

// ==================== 示例3: 会话管理示例 ====================

export const SessionManagementExample: React.FC = () => {
  const {
    sessions,
    currentSession,
    isLoading,
    sendMessage,
    createSession,
    selectSession,
    deleteSession,
    clearAllSessions,
  } = useAIAssistant({
    enableStreaming: true,
  });

  const [input, setInput] = useState('');
  const [showHistory, setShowHistory] = useState(false);

  const handleSend = async () => {
    if (!input.trim()) return;
    await sendMessage(input);
    setInput('');
  };

  return (
    <div className="flex h-screen">
      {/* 侧边栏 - 会话列表 */}
      <div className={`w-64 bg-gray-100 border-r border-gray-200 transition-all ${
        showHistory ? 'block' : 'hidden lg:block'
      }`}>
        <div className="p-4">
          <div className="flex items-center justify-between mb-4">
            <h2 className="font-semibold text-gray-700">会话历史</h2>
            <button
              onClick={createSession}
              className="p-1 bg-blue-600 text-white rounded hover:bg-blue-700"
              title="新建会话"
            >
              +
            </button>
          </div>

          <div className="space-y-2">
            {sessions.map((session) => (
              <button
                key={session.id}
                onClick={() => selectSession(session.id)}
                className={`w-full text-left px-3 py-2 rounded-lg text-sm ${
                  currentSession?.id === session.id
                    ? 'bg-blue-100 text-blue-800'
                    : 'hover:bg-gray-200'
                }`}
              >
                <p className="font-medium truncate">{session.title}</p>
                <p className="text-xs text-gray-500">
                  {session.messages.length} 条消息
                </p>
              </button>
            ))}
          </div>

          {sessions.length > 0 && (
            <button
              onClick={clearAllSessions}
              className="mt-4 text-xs text-red-600 hover:text-red-800"
            >
              清除所有会话
            </button>
          )}
        </div>
      </div>

      {/* 主聊天区域 */}
      <div className="flex-1 flex flex-col">
        {/* 标题栏 */}
        <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
          <div className="flex items-center gap-2">
            <button
              onClick={() => setShowHistory(!showHistory)}
              className="lg:hidden p-2 hover:bg-gray-100 rounded-lg"
            >
              ☰
            </button>
            <h1 className="font-semibold">{currentSession?.title || '新对话'}</h1>
          </div>
        </div>

        {/* 消息区域 */}
        <div className="flex-1 overflow-y-auto p-4 space-y-4">
          {currentSession?.messages.map((msg) => (
            <MessageBubble key={msg.id} message={msg} />
          ))}
          {isLoading && (
            <div className="bg-gray-100 rounded-2xl rounded-tl-none inline-block">
              <ThinkingIndicator />
            </div>
          )}
        </div>

        {/* 输入区域 */}
        <div className="p-4 border-t border-gray-200">
          <div className="flex gap-2">
            <input
              type="text"
              value={input}
              onChange={(e) => setInput(e.target.value)}
              onKeyDown={(e) => e.key === 'Enter' && handleSend()}
              placeholder="输入消息..."
              className="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500"
              disabled={isLoading}
            />
            <button
              onClick={handleSend}
              disabled={isLoading || !input.trim()}
              className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 disabled:opacity-50"
            >
              发送
            </button>
          </div>
        </div>
      </div>
    </div>
  );
};

export default {
  BasicHookExample,
  ContextualHookExample,
  SessionManagementExample,
};
