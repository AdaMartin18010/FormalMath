// ==================== 实时聊天面板组件 ====================

import React, { useState, useRef, useEffect, useCallback } from 'react';
import { collaborationService } from '@services/collaborationService';
import { ChatMessage, MessageType, UserPresence } from '@types/collaboration';
import './ChatPanel.css';

// 组件Props
interface ChatPanelProps {
  roomId: string;
  userId: string;
  userName: string;
  userAvatar?: string;
  onClose?: () => void;
  className?: string;
}

// 表情符号列表
const EMOJIS = ['👍', '❤️', '😂', '🎉', '🤔', '👏', '🔥', '✅', '❌', '🤯'];

export const ChatPanel: React.FC<ChatPanelProps> = ({
  roomId,
  userId,
  userName,
  userAvatar,
  onClose,
  className = '',
}) => {
  // State
  const [messages, setMessages] = useState<ChatMessage[]>([]);
  const [inputValue, setInputValue] = useState('');
  const [isLoading, setIsLoading] = useState(false);
  const [hasMore, setHasMore] = useState(true);
  const [typingUsers, setTypingUsers] = useState<string[]>([]);
  const [showEmojiPicker, setShowEmojiPicker] = useState(false);
  const [replyTo, setReplyTo] = useState<ChatMessage | null>(null);
  const [unreadCount, setUnreadCount] = useState(0);

  // Refs
  const messagesEndRef = useRef<HTMLDivElement>(null);
  const messagesContainerRef = useRef<HTMLDivElement>(null);
  const inputRef = useRef<HTMLInputElement>(null);
  const typingTimerRef = useRef<NodeJS.Timeout | null>(null);
  const isFirstLoadRef = useRef(true);

  // 加载历史消息
  const loadMessages = useCallback(async (before?: number) => {
    try {
      setIsLoading(true);
      const history = await collaborationService.getMessages(50, before);
      
      if (before) {
        setMessages((prev) => [...history, ...prev]);
        setHasMore(history.length === 50);
      } else {
        setMessages(history);
        setHasMore(history.length === 50);
      }
    } catch (error) {
      console.error('Failed to load messages:', error);
    } finally {
      setIsLoading(false);
    }
  }, []);

  // 初始化
  useEffect(() => {
    loadMessages();

    // 监听新消息
    const unsubscribeMessage = collaborationService.on('chat:message', (message) => {
      setMessages((prev) => [...prev, message]);
      
      // 如果不是自己发的消息，增加未读计数
      if (message.userId !== userId) {
        setUnreadCount((prev) => prev + 1);
      }
    });

    // 监听输入状态
    const unsubscribeTyping = collaborationService.on('chat:typing', (typingUserId, isTyping) => {
      setTypingUsers((prev) => {
        if (isTyping) {
          return [...new Set([...prev, typingUserId])];
        }
        return prev.filter((id) => id !== typingUserId);
      });
    });

    return () => {
      unsubscribeMessage();
      unsubscribeTyping();
    };
  }, [roomId, userId, loadMessages]);

  // 自动滚动到底部
  useEffect(() => {
    if (isFirstLoadRef.current && messages.length > 0) {
      messagesEndRef.current?.scrollIntoView({ behavior: 'auto' });
      isFirstLoadRef.current = false;
    } else if (messages.length > 0 && messages[messages.length - 1].userId === userId) {
      messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
    }
  }, [messages, userId]);

  // 清除未读计数（当面板可见时）
  useEffect(() => {
    setUnreadCount(0);
  }, []);

  // 发送消息
  const handleSendMessage = useCallback(async () => {
    if (!inputValue.trim()) return;

    try {
      await collaborationService.sendMessage(
        inputValue.trim(),
        replyTo?.id
      );
      setInputValue('');
      setReplyTo(null);
      setShowEmojiPicker(false);
    } catch (error) {
      console.error('Failed to send message:', error);
    }
  }, [inputValue, replyTo]);

  // 处理输入
  const handleInputChange = useCallback((e: React.ChangeEvent<HTMLInputElement>) => {
    setInputValue(e.target.value);

    // 发送输入状态
    collaborationService.sendTypingStatus(true);

    // 清除之前的定时器
    if (typingTimerRef.current) {
      clearTimeout(typingTimerRef.current);
    }

    // 3秒后停止输入状态
    typingTimerRef.current = setTimeout(() => {
      collaborationService.sendTypingStatus(false);
    }, 3000);
  }, []);

  // 处理键盘事件
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSendMessage();
    }
  }, [handleSendMessage]);

  // 插入表情
  const handleEmojiClick = useCallback((emoji: string) => {
    setInputValue((prev) => prev + emoji);
    setShowEmojiPicker(false);
    inputRef.current?.focus();
  }, []);

  // 回复消息
  const handleReply = useCallback((message: ChatMessage) => {
    setReplyTo(message);
    inputRef.current?.focus();
  }, []);

  // 添加反应
  const handleReaction = useCallback((messageId: string, emoji: string) => {
    collaborationService.addReaction(messageId, emoji);
  }, []);

  // 格式化时间
  const formatTime = useCallback((timestamp: number): string => {
    const date = new Date(timestamp);
    const now = new Date();
    const isToday = date.toDateString() === now.toDateString();

    if (isToday) {
      return date.toLocaleTimeString('zh-CN', {
        hour: '2-digit',
        minute: '2-digit',
      });
    }

    return date.toLocaleDateString('zh-CN', {
      month: 'short',
      day: 'numeric',
      hour: '2-digit',
      minute: '2-digit',
    });
  }, []);

  // 格式化消息内容（处理链接、@提及等）
  const formatMessageContent = useCallback((content: string): React.ReactNode => {
    // 处理URL
    const urlRegex = /(https?:\/\/[^\s]+)/g;
    const parts = content.split(urlRegex);

    return parts.map((part, index) => {
      if (urlRegex.test(part)) {
        return (
          <a
            key={index}
            href={part}
            target="_blank"
            rel="noopener noreferrer"
            className="message-link"
          >
            {part}
          </a>
        );
      }
      return <span key={index}>{part}</span>;
    });
  }, []);

  // 加载更多消息
  const handleLoadMore = useCallback(() => {
    if (isLoading || !hasMore || messages.length === 0) return;
    const oldestMessage = messages[0];
    loadMessages(oldestMessage.timestamp);
  }, [isLoading, hasMore, messages, loadMessages]);

  // 滚动检测
  const handleScroll = useCallback(() => {
    const container = messagesContainerRef.current;
    if (!container) return;

    // 当滚动到顶部时加载更多
    if (container.scrollTop === 0) {
      handleLoadMore();
    }
  }, [handleLoadMore]);

  // 过滤掉自己的输入状态
  const otherTypingUsers = typingUsers.filter((id) => id !== userId);

  return (
    <div className={`chat-panel ${className}`}>
      {/* 头部 */}
      <div className="chat-header">
        <div className="chat-title">
          <span className="chat-icon">💬</span>
          <span>实时讨论</span>
          {unreadCount > 0 && (
            <span className="unread-badge">{unreadCount}</span>
          )}
        </div>
        <button className="chat-close-btn" onClick={onClose} title="关闭">
          ✕
        </button>
      </div>

      {/* 消息列表 */}
      <div
        className="chat-messages"
        ref={messagesContainerRef}
        onScroll={handleScroll}
      >
        {hasMore && (
          <button
            className="load-more-btn"
            onClick={handleLoadMore}
            disabled={isLoading}
          >
            {isLoading ? '加载中...' : '加载更多'}
          </button>
        )}

        {messages.length === 0 && !isLoading ? (
          <div className="empty-state">
            <span className="empty-icon">💬</span>
            <p>还没有消息</p>
            <p className="empty-hint">发送第一条消息开始讨论吧</p>
          </div>
        ) : (
          messages.map((message, index) => {
            const isMine = message.userId === userId;
            const showAvatar = index === 0 || messages[index - 1].userId !== message.userId;
            const showTime =
              index === messages.length - 1 ||
              messages[index + 1].userId !== message.userId ||
              messages[index + 1].timestamp - message.timestamp > 60000;

            return (
              <div
                key={message.id}
                className={`message ${isMine ? 'mine' : 'other'} ${showAvatar ? 'show-avatar' : ''}`}
              >
                {/* 头像 */}
                {showAvatar && !isMine && (
                  <div className="message-avatar">
                    {message.userAvatar ? (
                      <img src={message.userAvatar} alt={message.userName} />
                    ) : (
                      <span>{message.userName.charAt(0).toUpperCase()}</span>
                    )}
                  </div>
                )}

                <div className="message-content-wrapper">
                  {/* 用户名 */}
                  {showAvatar && !isMine && (
                    <span className="message-username">{message.userName}</span>
                  )}

                  {/* 回复引用 */}
                  {message.replyTo && (
                    <div className="message-reply">
                      <span className="reply-to">
                        回复 {messages.find((m) => m.id === message.replyTo)?.userName}
                      </span>
                      <span className="reply-content">
                        {messages.find((m) => m.id === message.replyTo)?.content.slice(0, 50)}
                        {(messages.find((m) => m.id === message.replyTo)?.content.length || 0) > 50 && '...'}
                      </span>
                    </div>
                  )}

                  {/* 消息内容 */}
                  <div className="message-bubble">
                    <div className="message-text">
                      {formatMessageContent(message.content)}
                    </div>

                    {/* 反应 */}
                    {message.reactions && message.reactions.length > 0 && (
                      <div className="message-reactions">
                        {message.reactions.map((reaction, idx) => (
                          <button
                            key={idx}
                            className="reaction-btn"
                            onClick={() => handleReaction(message.id, reaction.emoji)}
                            title={reaction.users.join(', ')}
                          >
                            <span>{reaction.emoji}</span>
                            <span className="reaction-count">{reaction.users.length}</span>
                          </button>
                        ))}
                      </div>
                    )}
                  </div>

                  {/* 时间 */}
                  {showTime && (
                    <span className="message-time">{formatTime(message.timestamp)}</span>
                  )}

                  {/* 操作按钮 */}
                  <div className="message-actions">
                    <button
                      className="action-btn"
                      onClick={() => handleReply(message)}
                      title="回复"
                    >
                      ↩️
                    </button>
                    <div className="reaction-picker-trigger">
                      <button className="action-btn" title="添加反应">
                        😀
                      </button>
                      <div className="reaction-picker">
                        {EMOJIS.map((emoji) => (
                          <button
                            key={emoji}
                            className="emoji-btn"
                            onClick={() => handleReaction(message.id, emoji)}
                          >
                            {emoji}
                          </button>
                        ))}
                      </div>
                    </div>
                  </div>
                </div>
              </div>
            );
          })
        )}

        {/* 正在输入指示器 */}
        {otherTypingUsers.length > 0 && (
          <div className="typing-indicator">
            <span className="typing-dots">
              <span></span>
              <span></span>
              <span></span>
            </span>
            <span className="typing-text">
              {otherTypingUsers.length === 1
                ? '有人正在输入...'
                : `${otherTypingUsers.length}人正在输入...`}
            </span>
          </div>
        )}

        <div ref={messagesEndRef} />
      </div>

      {/* 回复引用显示 */}
      {replyTo && (
        <div className="reply-preview">
          <div className="reply-info">
            <span className="reply-label">回复</span>
            <span className="reply-user">{replyTo.userName}</span>
            <span className="reply-text">{replyTo.content.slice(0, 50)}</span>
          </div>
          <button className="cancel-reply-btn" onClick={() => setReplyTo(null)}>
            ✕
          </button>
        </div>
      )}

      {/* 输入区域 */}
      <div className="chat-input-area">
        {/* 表情选择器 */}
        {showEmojiPicker && (
          <div className="emoji-picker">
            {EMOJIS.map((emoji) => (
              <button
                key={emoji}
                className="emoji-btn"
                onClick={() => handleEmojiClick(emoji)}
              >
                {emoji}
              </button>
            ))}
          </div>
        )}

        <div className="input-wrapper">
          <button
            className="emoji-toggle-btn"
            onClick={() => setShowEmojiPicker(!showEmojiPicker)}
            title="表情"
          >
            😀
          </button>

          <input
            ref={inputRef}
            type="text"
            value={inputValue}
            onChange={handleInputChange}
            onKeyDown={handleKeyDown}
            placeholder={replyTo ? '回复消息...' : '输入消息...'}
            className="chat-input"
          />

          <button
            className="send-btn"
            onClick={handleSendMessage}
            disabled={!inputValue.trim()}
            title="发送"
          >
            ➤
          </button>
        </div>
      </div>
    </div>
  );
};

export default ChatPanel;
