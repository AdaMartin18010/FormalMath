/**
 * 虚拟导师组件
 * 提供AI数学导师的交互界面
 */

import React, { useState, useRef, useEffect } from 'react';
import { Bot, X, Send, Sparkles, Lightbulb, ThumbsUp, ThumbsDown, MessageCircle } from 'lucide-react';
import type { TutorMessage, TutorPersonality } from '../../../types/gamification';

interface TutorWidgetProps {
  isEnabled: boolean;
  personality: TutorPersonality;
  messages: TutorMessage[];
  onToggle: () => void;
  onSetPersonality: (personality: TutorPersonality) => void;
  onGetHint: () => Promise<void>;
  onGetExplanation: () => Promise<void>;
  onGetMotivation: () => Promise<void>;
  onAskQuestion: (question: string) => Promise<void>;
  onClearMessages: () => void;
}

const personalityConfig: Record<TutorPersonality, { 
  name: string; 
  emoji: string; 
  greeting: string;
  color: string;
}> = {
  encouraging: {
    name: '鼓励型',
    emoji: '🌟',
    greeting: '你好！我相信你一定能掌握这个概念的！',
    color: 'from-yellow-400 to-orange-500',
  },
  strict: {
    name: '严格型',
    emoji: '📚',
    greeting: '开始学习了。记住：数学需要严谨。',
    color: 'from-blue-500 to-indigo-600',
  },
  friendly: {
    name: '友好型',
    emoji: '😊',
    greeting: '嗨！有什么我可以帮你的吗？',
    color: 'from-green-400 to-teal-500',
  },
  scholarly: {
    name: '学者型',
    emoji: '🎓',
    greeting: '欢迎。让我们探讨数学的奥秘。',
    color: 'from-purple-500 to-pink-600',
  },
  mysterious: {
    name: '神秘型',
    emoji: '🔮',
    greeting: '答案就在你心中，让我引导你找到它...',
    color: 'from-indigo-500 to-purple-600',
  },
};

export const TutorWidget: React.FC<TutorWidgetProps> = ({
  isEnabled,
  personality,
  messages,
  onToggle,
  onSetPersonality,
  onGetHint,
  onGetExplanation,
  onGetMotivation,
  onAskQuestion,
  onClearMessages,
}) => {
  const [isOpen, setIsOpen] = useState(false);
  const [question, setQuestion] = useState('');
  const [showSettings, setShowSettings] = useState(false);
  const messagesEndRef = useRef<HTMLDivElement>(null);

  const config = personalityConfig[personality];

  // 自动滚动到底部
  useEffect(() => {
    messagesEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  }, [messages]);

  // 发送问题
  const handleSend = async () => {
    if (!question.trim()) return;
    await onAskQuestion(question);
    setQuestion('');
  };

  if (!isEnabled) {
    return (
      <button
        onClick={onToggle}
        className="fixed bottom-6 right-6 w-14 h-14 bg-gray-400 rounded-full flex items-center justify-center shadow-lg hover:bg-gray-500 transition-colors"
      >
        <Bot className="w-7 h-7 text-white" />
      </button>
    );
  }

  return (
    <>
      {/* 悬浮按钮 */}
      {!isOpen && (
        <button
          onClick={() => setIsOpen(true)}
          className={`fixed bottom-6 right-6 w-14 h-14 bg-gradient-to-r ${config.color} rounded-full flex items-center justify-center shadow-lg hover:shadow-xl transition-all hover:scale-110 z-40`}
        >
          <Bot className="w-7 h-7 text-white" />
          {messages.length > 0 && (
            <div className="absolute -top-1 -right-1 w-5 h-5 bg-red-500 text-white text-xs rounded-full flex items-center justify-center">
              {messages.length}
            </div>
          )}
        </button>
      )}

      {/* 聊天窗口 */}
      {isOpen && (
        <div className="fixed bottom-6 right-6 w-96 bg-white rounded-2xl shadow-2xl z-50 overflow-hidden">
          {/* 头部 */}
          <div className={`bg-gradient-to-r ${config.color} p-4 text-white`}>
            <div className="flex items-center justify-between">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 bg-white/20 rounded-full flex items-center justify-center text-2xl">
                  {config.emoji}
                </div>
                <div>
                  <h3 className="font-bold">MathGuide AI</h3>
                  <p className="text-xs text-white/80">{config.name}导师</p>
                </div>
              </div>
              <div className="flex items-center gap-2">
                <button
                  onClick={() => setShowSettings(!showSettings)}
                  className="p-2 hover:bg-white/20 rounded-lg transition-colors"
                >
                  <Sparkles className="w-5 h-5" />
                </button>
                <button
                  onClick={() => setIsOpen(false)}
                  className="p-2 hover:bg-white/20 rounded-lg transition-colors"
                >
                  <X className="w-5 h-5" />
                </button>
              </div>
            </div>
          </div>

          {/* 设置面板 */}
          {showSettings && (
            <div className="bg-gray-50 p-4 border-b">
              <h4 className="text-sm font-semibold text-gray-700 mb-3">选择导师性格</h4>
              <div className="grid grid-cols-2 gap-2">
                {(Object.keys(personalityConfig) as TutorPersonality[]).map((p) => (
                  <button
                    key={p}
                    onClick={() => {
                      onSetPersonality(p);
                      setShowSettings(false);
                    }}
                    className={`
                      flex items-center gap-2 p-2 rounded-lg text-sm transition-colors
                      ${personality === p
                        ? 'bg-blue-100 text-blue-700 border border-blue-300'
                        : 'bg-white border hover:bg-gray-50'
                      }
                    `}
                  >
                    <span>{personalityConfig[p].emoji}</span>
                    <span>{personalityConfig[p].name}</span>
                  </button>
                ))}
              </div>
              <button
                onClick={onToggle}
                className="w-full mt-3 py-2 text-sm text-red-600 hover:bg-red-50 rounded-lg"
              >
                关闭导师
              </button>
            </div>
          )}

          {/* 消息列表 */}
          <div className="h-80 overflow-y-auto p-4 space-y-4">
            {messages.length === 0 && (
              <div className="text-center text-gray-500 py-8">
                <Bot className="w-12 h-12 mx-auto mb-3 text-gray-300" />
                <p>{config.greeting}</p>
              </div>
            )}

            {messages.map((message) => (
              <div
                key={message.id}
                className={`flex gap-3 ${message.type === 'feedback' ? 'flex-row-reverse' : ''}`}
              >
                <div className={`
                  w-8 h-8 rounded-full flex items-center justify-center flex-shrink-0
                  ${message.type === 'feedback' ? 'bg-gray-200' : `bg-gradient-to-r ${config.color} text-white`}
                `}>
                  {message.type === 'feedback' ? (
                    <MessageCircle className="w-4 h-4 text-gray-600" />
                  ) : (
                    <Bot className="w-4 h-4" />
                  )}
                </div>
                <div className={`
                  max-w-[75%] p-3 rounded-2xl text-sm
                  ${message.type === 'feedback'
                    ? 'bg-blue-100 text-blue-800 rounded-br-none'
                    : 'bg-gray-100 text-gray-800 rounded-bl-none'
                  }
                `}>
                  {message.content}
                </div>
              </div>
            ))}
            <div ref={messagesEndRef} />
          </div>

          {/* 快捷操作 */}
          <div className="px-4 py-2 bg-gray-50 border-t flex gap-2 overflow-x-auto">
            <button
              onClick={onGetHint}
              className="flex items-center gap-1 px-3 py-1.5 bg-yellow-100 text-yellow-700 rounded-full text-xs whitespace-nowrap hover:bg-yellow-200"
            >
              <Lightbulb className="w-3 h-3" />
              提示
            </button>
            <button
              onClick={onGetExplanation}
              className="flex items-center gap-1 px-3 py-1.5 bg-blue-100 text-blue-700 rounded-full text-xs whitespace-nowrap hover:bg-blue-200"
            >
              <Sparkles className="w-3 h-3" />
              解释
            </button>
            <button
              onClick={onGetMotivation}
              className="flex items-center gap-1 px-3 py-1.5 bg-green-100 text-green-700 rounded-full text-xs whitespace-nowrap hover:bg-green-200"
            >
              <ThumbsUp className="w-3 h-3" />
              鼓励
            </button>
          </div>

          {/* 输入框 */}
          <div className="p-4 border-t">
            <div className="flex gap-2">
              <input
                type="text"
                value={question}
                onChange={(e) => setQuestion(e.target.value)}
                onKeyPress={(e) => e.key === 'Enter' && handleSend()}
                placeholder="输入你的问题..."
                className="flex-1 px-4 py-2 border rounded-full focus:ring-2 focus:ring-blue-500 focus:outline-none"
              />
              <button
                onClick={handleSend}
                disabled={!question.trim()}
                className="p-2 bg-blue-600 text-white rounded-full hover:bg-blue-700 disabled:bg-gray-300 transition-colors"
              >
                <Send className="w-5 h-5" />
              </button>
            </div>
          </div>
        </div>
      )}
    </>
  );
};

export default TutorWidget;
