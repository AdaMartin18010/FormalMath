import React, { useState, useRef, useEffect } from 'react';
import { aiClient, AssistantResponse } from '../api/client';
import './ChatInterface.css';

interface Message {
  id: string;
  role: 'user' | 'assistant';
  content: string;
  timestamp: Date;
  latexFormulas?: string[];
  suggestions?: string[];
}

interface ChatInterfaceProps {
  userId?: string;
  initialContextId?: string;
}

export const ChatInterface: React.FC<ChatInterfaceProps> = ({ 
  userId, 
  initialContextId 
}) => {
  const [messages, setMessages] = useState<Message[]>([]);
  const [input, setInput] = useState('');
  const [loading, setLoading] = useState(false);
  const [contextId, setContextId] = useState<string | undefined>(initialContextId);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  const scrollToBottom = () => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  };

  useEffect(() => {
    scrollToBottom();
  }, [messages]);

  const handleSend = async () => {
    if (!input.trim() || loading) return;

    const userMessage: Message = {
      id: Date.now().toString(),
      role: 'user',
      content: input,
      timestamp: new Date(),
    };

    setMessages(prev => [...prev, userMessage]);
    setInput('');
    setLoading(true);

    try {
      const response: AssistantResponse = await aiClient.ask({
        question: input,
        context_id: contextId,
        user_id: userId,
      });

      // 保存上下文ID
      if (response.context_id && !contextId) {
        setContextId(response.context_id);
      }

      const assistantMessage: Message = {
        id: (Date.now() + 1).toString(),
        role: 'assistant',
        content: response.answer,
        timestamp: new Date(),
        latexFormulas: response.latex_formulas,
        suggestions: response.suggestions,
      };

      setMessages(prev => [...prev, assistantMessage]);
    } catch (error) {
      console.error('发送消息失败:', error);
      const errorMessage: Message = {
        id: (Date.now() + 1).toString(),
        role: 'assistant',
        content: '抱歉，处理请求时出错，请稍后重试。',
        timestamp: new Date(),
      };
      setMessages(prev => [...prev, errorMessage]);
    } finally {
      setLoading(false);
    }
  };

  const handleSuggestionClick = (suggestion: string) => {
    setInput(suggestion);
  };

  const renderMessage = (message: Message) => {
    const isUser = message.role === 'user';
    
    return (
      <div key={message.id} className={`message ${isUser ? 'user' : 'assistant'}`}>
        <div className="message-avatar">
          {isUser ? '👤' : '🤖'}
        </div>
        <div className="message-content">
          <div className="message-text">{message.content}</div>
          
          {/* LaTeX公式显示 */}
          {message.latexFormulas && message.latexFormulas.length > 0 && (
            <div className="message-formulas">
              <div className="formula-label">相关公式:</div>
              {message.latexFormulas.map((formula, idx) => (
                <div key={idx} className="formula">${formula}$</div>
              ))}
            </div>
          )}
          
          {/* 建议问题 */}
          {message.suggestions && message.suggestions.length > 0 && (
            <div className="message-suggestions">
              <div className="suggestions-label">建议问题:</div>
              <div className="suggestions-list">
                {message.suggestions.map((suggestion, idx) => (
                  <button
                    key={idx}
                    className="suggestion-chip"
                    onClick={() => handleSuggestionClick(suggestion)}
                  >
                    {suggestion}
                  </button>
                ))}
              </div>
            </div>
          )}
          
          <div className="message-time">
            {message.timestamp.toLocaleTimeString()}
          </div>
        </div>
      </div>
    );
  };

  return (
    <div className="chat-interface">
      <div className="chat-header">
        <h2>🎓 AI数学学习助手</h2>
        {contextId && <span className="context-id">会话: {contextId.slice(0, 8)}...</span>}
      </div>
      
      <div className="messages-container">
        {messages.length === 0 && (
          <div className="welcome-message">
            <h3>欢迎来到FormalMath AI助手！</h3>
            <p>我可以帮助你：</p>
            <ul>
              <li>📚 解释数学概念</li>
              <li>💡 提供证明提示</li>
              <li>📖 推荐学习路径</li>
              <li>✏️ 解答数学问题</li>
              <li>🔧 Lean 4形式化帮助</li>
            </ul>
          </div>
        )}
        {messages.map(renderMessage)}
        {loading && (
          <div className="message assistant">
            <div className="message-avatar">🤖</div>
            <div className="message-content">
              <div className="typing-indicator">
                <span></span>
                <span></span>
                <span></span>
              </div>
            </div>
          </div>
        )}
        <div ref={messagesEndRef} />
      </div>
      
      <div className="input-container">
        <textarea
          value={input}
          onChange={(e) => setInput(e.target.value)}
          onKeyDown={(e) => {
            if (e.key === 'Enter' && !e.shiftKey) {
              e.preventDefault();
              handleSend();
            }
          }}
          placeholder="输入你的数学问题..."
          rows={2}
          disabled={loading}
        />
        <button 
          onClick={handleSend} 
          disabled={!input.trim() || loading}
          className="send-button"
        >
          发送
        </button>
      </div>
    </div>
  );
};

export default ChatInterface;
