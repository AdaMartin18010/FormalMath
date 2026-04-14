// @ts-nocheck
import React, { useState, useCallback, useEffect } from 'react';
import { 
  MessageSquare, 
  X, 
  Minimize2, 
  Maximize2, 
  History, 
  Plus, 
  Trash2,
  ChevronLeft,
  Sparkles,
  Lightbulb
} from 'lucide-react';
import { MessageList } from './MessageList';
import { MessageInput } from './MessageInput';
import { ThinkingIndicator } from './ThinkingIndicator';
import { aiService, saveSessions, loadSessions, generateId } from '@services/aiService';
import type { 
  ChatSession, 
  ChatMessage, 
  AIAssistantProps, 
  QuickQuestion,
  PageContext 
} from '@types/aiAssistant';
import { cn } from '@utils/classNames';

// ==================== 快捷提问选项 ====================

const quickQuestions: QuickQuestion[] = [
  { id: 'explain', label: '解释概念', question: '请解释这个概念的含义和作用', icon: 'lightbulb' },
  { id: 'prove', label: '查看证明', question: '请提供相关的证明或推导过程', icon: 'check' },
  { id: 'example', label: '举例说明', question: '请给出具体的例子说明', icon: 'book' },
  { id: 'relate', label: '相关概念', question: '这个概念与其他哪些概念相关', icon: 'link' },
];

// ==================== 主组件 ====================

export const ChatInterface: React.FC<AIAssistantProps> = ({
  initialOpen = false,
  position = 'right',
  context,
  onClose,
  onMessageSend,
}) => {
  // ==================== 状态管理 ====================
  
  const [isOpen, setIsOpen] = useState(initialOpen);
  const [isMinimized, setIsMinimized] = useState(false);
  const [showHistory, setShowHistory] = useState(false);
  const [sessions, setSessions] = useState<ChatSession[]>([]);
  const [currentSession, setCurrentSession] = useState<ChatSession | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [isStreaming, setIsStreaming] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // ==================== 初始化 ====================

  // 加载历史会话
  useEffect(() => {
    const savedSessions = loadSessions();
    setSessions(savedSessions);
    
    if (savedSessions.length > 0) {
      setCurrentSession(savedSessions[0]);
    } else {
      createNewSession();
    }
  }, []);

  // 保存会话到本地存储
  useEffect(() => {
    if (sessions.length > 0) {
      saveSessions(sessions);
    }
  }, [sessions]);

  // ==================== 会话管理 ====================

  const createNewSession = useCallback(() => {
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
    setShowHistory(false);
  }, [context]);

  const selectSession = useCallback((session: ChatSession) => {
    setCurrentSession(session);
    setShowHistory(false);
  }, []);

  const deleteSession = useCallback((sessionId: string, e: React.MouseEvent) => {
    e.stopPropagation();
    
    setSessions(prev => {
      const updated = prev.filter(s => s.id !== sessionId);
      
      if (currentSession?.id === sessionId) {
        if (updated.length > 0) {
          setCurrentSession(updated[0]);
        } else {
          const newSession: ChatSession = {
            id: generateId(),
            title: '新对话',
            messages: [],
            createdAt: new Date(),
            updatedAt: new Date(),
            context,
          };
          updated.push(newSession);
          setCurrentSession(newSession);
        }
      }
      
      return updated;
    });
  }, [currentSession, context]);

  const clearAllSessions = useCallback(() => {
    if (window.confirm('确定要清除所有对话历史吗？')) {
      setSessions([]);
      createNewSession();
    }
  }, [createNewSession]);

  // ==================== 消息处理 ====================

  const sendMessage = useCallback(async (content: string) => {
    if (!currentSession) return;

    // 创建用户消息
    const userMessage: ChatMessage = {
      id: generateId(),
      role: 'user',
      content,
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
    setError(null);

    onMessageSend?.(content);

    try {
      // 检查是否启用流式响应
      if (aiService.getConfig().enableStreaming) {
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
          message: content,
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

        // 完成流式响应
        assistantMessage.isStreaming = false;
        assistantMessage.timestamp = new Date();

        setCurrentSession(prev => {
          if (!prev) return prev;
          const messages = [...prev.messages];
          messages[messages.length - 1] = assistantMessage;
          return { ...prev, messages, updatedAt: new Date() };
        });

        setIsStreaming(false);
      } else {
        // 非流式响应
        const response = await aiService.sendMessage({
          message: content,
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

        const finalSession: ChatSession = {
          ...updatedSession,
          messages: [...updatedSession.messages, assistantMessage],
          updatedAt: new Date(),
        };

        setCurrentSession(finalSession);
      }

      // 更新会话列表
      setSessions(prev => {
        const updated = prev.map(s => 
          s.id === currentSession.id 
            ? { ...currentSession, messages: currentSession.messages, updatedAt: new Date() }
            : s
        );
        
        // 更新标题（如果是第一条消息）
        const session = updated.find(s => s.id === currentSession.id);
        if (session && session.messages.length === 2 && session.title === '新对话') {
          session.title = content.slice(0, 20) + (content.length > 20 ? '...' : '');
        }
        
        return updated;
      });

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

      const sessionWithError: ChatSession = {
        ...updatedSession,
        messages: [...updatedSession.messages, errorChatMessage],
      };

      setCurrentSession(sessionWithError);
    } finally {
      setIsLoading(false);
      setIsStreaming(false);
    }
  }, [currentSession, context, onMessageSend]);

  const handleStop = useCallback(() => {
    aiService.abort();
    setIsStreaming(false);
    setIsLoading(false);
  }, []);

  const handleQuickQuestion = useCallback((question: QuickQuestion) => {
    // 根据上下文定制问题
    let customizedQuestion = question.question;
    if (context?.currentConcept) {
      customizedQuestion = `关于"${context.currentConcept}"：${question.question}`;
    }
    sendMessage(customizedQuestion);
  }, [context, sendMessage]);

  const handleRegenerate = useCallback(async (messageId: string) => {
    if (!currentSession) return;

    // 找到需要重新生成的消息索引
    const messageIndex = currentSession.messages.findIndex(m => m.id === messageId);
    if (messageIndex <= 0) return;

    // 获取用户的上一条消息
    const userMessage = currentSession.messages[messageIndex - 1];
    
    // 删除助手消息及之后的所有消息
    const truncatedMessages = currentSession.messages.slice(0, messageIndex);
    
    const updatedSession: ChatSession = {
      ...currentSession,
      messages: truncatedMessages,
    };

    setCurrentSession(updatedSession);
    
    // 重新发送
    await sendMessage(userMessage.content);
  }, [currentSession, sendMessage]);

  // ==================== 渲染 ====================

  // 悬浮按钮模式
  if (!isOpen) {
    return (
      <button
        onClick={() => setIsOpen(true)}
        className="fixed bottom-6 right-6 z-50 flex items-center gap-2 px-4 py-3 
                 bg-blue-600 text-white rounded-full shadow-lg hover:bg-blue-700 
                 hover:shadow-xl transition-all duration-300 group"
      >
        <MessageSquare className="w-5 h-5" />
        <span className="font-medium">AI助手</span>
        <Sparkles className="w-4 h-4 text-yellow-300 opacity-0 group-hover:opacity-100 transition-opacity" />
      </button>
    );
  }

  // 侧边栏/浮动窗口模式
  const positionClasses = {
    right: 'right-0 top-0 h-full w-full sm:w-[400px] lg:w-[450px]',
    left: 'left-0 top-0 h-full w-full sm:w-[400px] lg:w-[450px]',
    floating: 'right-6 bottom-6 w-full sm:w-[400px] h-[600px] rounded-2xl shadow-2xl',
  };

  return (
    <div className={`fixed z-50 ${positionClasses[position]} ${
      position === 'floating' ? '' : ''
    }`}>
      <div className={`flex flex-col h-full bg-white border border-gray-200 ${
        position === 'floating' ? 'rounded-2xl overflow-hidden' : ''
      }`}>
        {/* 标题栏 */}
        <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200 bg-gradient-to-r from-blue-600 to-blue-700 text-white">
          <div className="flex items-center gap-3">
            {showHistory ? (
              <button
                onClick={() => setShowHistory(false)}
                className="p-1 hover:bg-white/20 rounded-lg transition-colors"
              >
                <ChevronLeft className="w-5 h-5" />
              </button>
            ) : (
              <div className="w-8 h-8 bg-white/20 rounded-lg flex items-center justify-center">
                <Sparkles className="w-4 h-4" />
              </div>
            )}
            <div>
              <h3 className="font-semibold">
                {showHistory ? '对话历史' : (currentSession?.title || 'AI助手')}
              </h3>
              {!showHistory && context?.currentConcept && (
                <p className="text-xs text-blue-100 truncate max-w-[150px]">
                  上下文: {context.currentConcept}
                </p>
              )}
            </div>
          </div>

          <div className="flex items-center gap-1">
            {/* 历史记录按钮 */}
            {!showHistory && (
              <button
                onClick={() => setShowHistory(true)}
                className="p-2 hover:bg-white/20 rounded-lg transition-colors"
                title="历史记录"
              >
                <History className="w-4 h-4" />
              </button>
            )}

            {/* 最小化按钮 */}
            <button
              onClick={() => setIsMinimized(!isMinimized)}
              className="p-2 hover:bg-white/20 rounded-lg transition-colors"
              title={isMinimized ? '展开' : '最小化'}
            >
              {isMinimized ? <Maximize2 className="w-4 h-4" /> : <Minimize2 className="w-4 h-4" />}
            </button>

            {/* 关闭按钮 */}
            <button
              onClick={() => {
                setIsOpen(false);
                onClose?.();
              }}
              className="p-2 hover:bg-white/20 rounded-lg transition-colors"
              title="关闭"
            >
              <X className="w-4 h-4" />
            </button>
          </div>
        </div>

        {/* 内容区域 */}
        {!isMinimized && (
          <>
            {showHistory ? (
              // 历史记录视图
              <div className="flex-1 overflow-y-auto p-4">
                <div className="flex items-center justify-between mb-4">
                  <button
                    onClick={createNewSession}
                    className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white 
                             rounded-lg hover:bg-blue-700 transition-colors"
                  >
                    <Plus className="w-4 h-4" />
                    新对话
                  </button>
                  
                  {sessions.length > 0 && (
                    <button
                      onClick={clearAllSessions}
                      className="p-2 text-red-600 hover:bg-red-50 rounded-lg transition-colors"
                      title="清除所有"
                    >
                      <Trash2 className="w-4 h-4" />
                    </button>
                  )}
                </div>

                <div className="space-y-2">
                  {sessions.map(session => (
                    <button
                      key={session.id}
                      onClick={() => selectSession(session)}
                      className={cn(
                        'w-full text-left px-4 py-3 rounded-lg transition-colors group',
                        currentSession?.id === session.id
                          ? 'bg-blue-50 border border-blue-200'
                          : 'hover:bg-gray-50 border border-transparent'
                      )}
                    >
                      <div className="flex items-center justify-between">
                        <div className="flex-1 min-w-0">
                          <p className="font-medium text-gray-900 truncate">
                            {session.title}
                          </p>
                          <p className="text-xs text-gray-500">
                            {session.messages.length} 条消息 · {session.updatedAt.toLocaleDateString()}
                          </p>
                        </div>
                        <button
                          onClick={(e) => deleteSession(session.id, e)}
                          className="p-1.5 text-gray-400 hover:text-red-600 
                                   opacity-0 group-hover:opacity-100 transition-opacity"
                        >
                          <Trash2 className="w-4 h-4" />
                        </button>
                      </div>
                    </button>
                  ))}
                </div>

                {sessions.length === 0 && (
                  <div className="text-center py-8 text-gray-400">
                    <History className="w-12 h-12 mx-auto mb-3 opacity-50" />
                    <p>暂无历史对话</p>
                  </div>
                )}
              </div>
            ) : (
              // 聊天视图
              <>
                {/* 快捷提问 */}
                {currentSession?.messages.length === 0 && (
                  <div className="px-4 py-4 border-b border-gray-100">
                    <p className="text-sm text-gray-500 mb-3 flex items-center gap-2">
                      <Lightbulb className="w-4 h-4" />
                      快捷提问
                    </p>
                    <div className="grid grid-cols-2 gap-2">
                      {quickQuestions.map(q => (
                        <button
                          key={q.id}
                          onClick={() => handleQuickQuestion(q)}
                          className="px-3 py-2 text-sm text-left text-gray-700 bg-gray-50 
                                   hover:bg-blue-50 hover:text-blue-700 rounded-lg 
                                   transition-colors border border-gray-200 hover:border-blue-200"
                        >
                          {q.label}
                        </button>
                      ))}
                    </div>
                  </div>
                )}

                {/* 消息列表 */}
                <MessageList
                  messages={currentSession?.messages || []}
                  isStreaming={isStreaming}
                  onRegenerate={handleRegenerate}
                />

                {/* 思考指示器 */}
                {isLoading && !isStreaming && (
                  <div className="px-4 py-2">
                    <div className="bg-gray-100 rounded-2xl rounded-tl-none inline-block">
                      <ThinkingIndicator message="AI正在思考" />
                    </div>
                  </div>
                )}

                {/* 输入框 */}
                <MessageInput
                  onSend={sendMessage}
                  onStop={handleStop}
                  isLoading={isLoading}
                  placeholder={context?.currentConcept 
                    ? `询问关于"${context.currentConcept}"的问题...` 
                    : '输入问题，支持LaTeX公式...'}
                  enableLatexPreview={true}
                />
              </>
            )}
          </>
        )}
      </div>
    </div>
  );
};

export default ChatInterface;
