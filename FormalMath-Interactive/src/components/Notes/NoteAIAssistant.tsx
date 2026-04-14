// @ts-nocheck
// ==================== AI笔记助手组件 ====================
import React, { useState, useCallback, useRef, useEffect } from 'react';
import { useNoteStore } from '../../stores/noteStore';
import {
  aiAssistant,
  analyzeNote,
  suggestConceptLinks,
  generateNoteSummary,
  autoTagNote,
} from '../../services/noteService';
import type { NoteAIRequest, NoteAIChatMessage, Note } from '../../types/notes';
import {
  Sparkles,
  Send,
  Loader2,
  Lightbulb,
  FileText,
  Link2,
  Tags,
  BookOpen,
  Wand2,
  X,
  Copy,
  Check,
  RefreshCw,
  Bot,
  User,
  Zap,
  Brain,
  MessageSquare,
} from 'lucide-react';

interface NoteAIAssistantProps {
  note?: Note;
  className?: string;
}

type AIAction = 'chat' | 'summarize' | 'explain' | 'expand' | 'relate' | 'autotag' | 'analyze';

interface AIActionButton {
  id: AIAction;
  label: string;
  icon: React.ReactNode;
  description: string;
}

const aiActions: AIActionButton[] = [
  {
    id: 'summarize',
    label: '智能总结',
    icon: <FileText className="w-4 h-4" />,
    description: '生成笔记核心要点',
  },
  {
    id: 'explain',
    label: '深度解释',
    icon: <BookOpen className="w-4 h-4" />,
    description: '详细解释概念内容',
  },
  {
    id: 'expand',
    label: '内容扩展',
    icon: <Wand2 className="w-4 h-4" />,
    description: '丰富和扩展笔记',
  },
  {
    id: 'relate',
    label: '知识关联',
    icon: <Link2 className="w-4 h-4" />,
    description: '关联相关知识概念',
  },
  {
    id: 'autotag',
    label: '智能标签',
    icon: <Tags className="w-4 h-4" />,
    description: '自动推荐标签',
  },
  {
    id: 'analyze',
    label: '全面分析',
    icon: <Brain className="w-4 h-4" />,
    description: '深度分析笔记内容',
  },
];

export const NoteAIAssistant: React.FC<NoteAIAssistantProps> = ({
  note,
  className = '',
}) => {
  const [chatHistory, setChatHistory] = useState<NoteAIChatMessage[]>([]);
  const [inputMessage, setInputMessage] = useState('');
  const [isProcessing, setIsProcessing] = useState(false);
  const [activeAction, setActiveAction] = useState<AIAction | null>(null);
  const [analysisResult, setAnalysisResult] = useState<any>(null);
  const [suggestedTags, setSuggestedTags] = useState<string[]>([]);
  const [copied, setCopied] = useState(false);
  const chatEndRef = useRef<HTMLDivElement>(null);

  const { editor, setSelectedText } = useNoteStore();
  const { selectedText } = editor;

  // 滚动到最新消息
  useEffect(() => {
    chatEndRef.current?.scrollIntoView({ behavior: 'smooth' });
  }, [chatHistory]);

  // 执行AI操作
  const executeAIAction = useCallback(async (action: AIAction) => {
    if (!note && action !== 'chat') return;

    setIsProcessing(true);
    setActiveAction(action);

    try {
      switch (action) {
        case 'summarize':
          const summaryResponse = await generateNoteSummary(note!.id, 200);
          if (summaryResponse.success) {
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content: `**笔记总结**\n\n${summaryResponse.data}`,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;

        case 'explain':
          const explainResponse = await aiAssistant({
            type: 'explain',
            content: selectedText || note!.content,
            context: { noteId: note!.id, selectedText },
          });
          if (explainResponse.success && explainResponse.data) {
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content: `**深度解释**\n\n${explainResponse.data.result}`,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;

        case 'expand':
          const expandResponse = await aiAssistant({
            type: 'expand',
            content: selectedText || note!.content,
            context: { noteId: note!.id, selectedText },
          });
          if (expandResponse.success && expandResponse.data) {
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content: `**内容扩展建议**\n\n${expandResponse.data.result}`,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;

        case 'relate':
          const linksResponse = await suggestConceptLinks(note!.id);
          if (linksResponse.success && linksResponse.data) {
            const links = linksResponse.data;
            const content = links.length > 0
              ? `**相关概念建议**\n\n${links.map((l) => `- **${l.conceptName}** (${l.relationType}) - 相关度: ${Math.round(l.relevanceScore * 100)}%`).join('\n')}`
              : '**相关概念建议**\n\n暂时未能找到高度相关的概念。建议完善笔记内容后再试。';
            
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;

        case 'autotag':
          const tagsResponse = await autoTagNote(note!.id);
          if (tagsResponse.success && tagsResponse.data) {
            setSuggestedTags(tagsResponse.data);
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content: `**智能标签推荐**\n\n根据笔记内容，推荐以下标签：\n\n${tagsResponse.data.map((tag) => `- #${tag}`).join('\n')}\n\n点击标签可直接添加到笔记中。`,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;

        case 'analyze':
          const analysisResponse = await analyzeNote(note!.id);
          if (analysisResponse.success && analysisResponse.data) {
            setAnalysisResult(analysisResponse.data);
            const data = analysisResponse.data;
            const content = `**笔记分析报告**\n\n📊 **难度等级**: ${data.difficulty || '未评估'}\n\n⏱️ **预计阅读时间**: ${data.estimatedReadTime || '未知'} 分钟\n\n🎯 **关键概念**: ${data.keyConcepts?.join(', ') || '暂无'}\n\n📚 **建议标签**: ${data.suggestedTags?.join(', ') || '暂无'}`;
            
            const message: NoteAIChatMessage = {
              id: Date.now().toString(),
              role: 'assistant',
              content,
              timestamp: new Date().toISOString(),
            };
            setChatHistory((prev) => [...prev, message]);
          }
          break;
      }
    } catch (error) {
      const errorMessage: NoteAIChatMessage = {
        id: Date.now().toString(),
        role: 'assistant',
        content: '❌ 抱歉，AI助手处理过程中出现错误。请稍后重试。',
        timestamp: new Date().toISOString(),
      };
      setChatHistory((prev) => [...prev, errorMessage]);
    } finally {
      setIsProcessing(false);
      setActiveAction(null);
    }
  }, [note, selectedText]);

  // 发送消息
  const sendMessage = useCallback(async () => {
    if (!inputMessage.trim() || isProcessing) return;

    const userMessage: NoteAIChatMessage = {
      id: Date.now().toString(),
      role: 'user',
      content: inputMessage,
      timestamp: new Date().toISOString(),
    };

    setChatHistory((prev) => [...prev, userMessage]);
    setInputMessage('');
    setIsProcessing(true);

    try {
      const response = await aiAssistant({
        type: 'suggest',
        content: inputMessage,
        context: {
          noteId: note?.id,
          selectedText,
        },
      });

      if (response.success && response.data) {
        const assistantMessage: NoteAIChatMessage = {
          id: (Date.now() + 1).toString(),
          role: 'assistant',
          content: response.data.result,
          timestamp: new Date().toISOString(),
        };
        setChatHistory((prev) => [...prev, assistantMessage]);

        // 如果有建议的编辑
        if (response.data.suggestedEdits?.length > 0) {
          const editMessage: NoteAIChatMessage = {
            id: (Date.now() + 2).toString(),
            role: 'assistant',
            content: `💡 **建议修改**\n\n我发现以下可以优化的地方：\n\n${response.data.suggestedEdits.map((edit: any, i: number) => `${i + 1}. ${edit.explanation}`).join('\n')}\n\n您可以选择应用这些修改。`,
            timestamp: new Date().toISOString(),
          };
          setChatHistory((prev) => [...prev, editMessage]);
        }
      }
    } catch (error) {
      const errorMessage: NoteAIChatMessage = {
        id: (Date.now() + 1).toString(),
        role: 'assistant',
        content: '❌ 抱歉，我暂时无法处理您的请求。请检查网络连接或稍后重试。',
        timestamp: new Date().toISOString(),
      };
      setChatHistory((prev) => [...prev, errorMessage]);
    } finally {
      setIsProcessing(false);
    }
  }, [inputMessage, note, selectedText, isProcessing]);

  // 复制内容
  const handleCopy = useCallback((content: string) => {
    navigator.clipboard.writeText(content);
    setCopied(true);
    setTimeout(() => setCopied(false), 2000);
  }, []);

  // 清除历史
  const clearHistory = useCallback(() => {
    setChatHistory([]);
    setAnalysisResult(null);
    setSuggestedTags([]);
  }, []);

  return (
    <div className={`flex flex-col h-full bg-gray-50 ${className}`}>
      {/* 头部 */}
      <div className="px-4 py-3 bg-white border-b border-gray-200">
        <div className="flex items-center justify-between">
          <div className="flex items-center">
            <div className="w-8 h-8 bg-gradient-to-br from-blue-500 to-purple-500 rounded-lg flex items-center justify-center mr-3">
              <Sparkles className="w-5 h-5 text-white" />
            </div>
            <div>
              <h3 className="font-semibold text-gray-800">AI 笔记助手</h3>
              <p className="text-xs text-gray-500">
                {note ? `正在为「${note.title}」提供协助` : '选择笔记开始AI协助'}
              </p>
            </div>
          </div>
          {chatHistory.length > 0 && (
            <button
              onClick={clearHistory}
              className="p-2 text-gray-400 hover:text-gray-600 rounded-lg hover:bg-gray-100"
              title="清除对话"
            >
              <RefreshCw className="w-4 h-4" />
            </button>
          )}
        </div>
      </div>

      {/* AI功能按钮 */}
      {note && (
        <div className="p-3 bg-white border-b border-gray-200">
          <div className="grid grid-cols-3 gap-2">
            {aiActions.map((action) => (
              <button
                key={action.id}
                onClick={() => executeAIAction(action.id)}
                disabled={isProcessing}
                className={`
                  flex flex-col items-center p-2 rounded-lg border transition-all
                  ${activeAction === action.id
                    ? 'bg-blue-50 border-blue-300 text-blue-700'
                    : 'bg-white border-gray-200 text-gray-600 hover:bg-gray-50'
                  }
                  disabled:opacity-50 disabled:cursor-not-allowed
                `}
              >
                <span className={activeAction === action.id ? 'text-blue-500' : 'text-gray-400'}>
                  {action.icon}
                </span>
                <span className="text-xs font-medium mt-1">{action.label}</span>
                <span className="text-[10px] text-gray-400 text-center leading-tight mt-0.5">
                  {action.description}
                </span>
              </button>
            ))}
          </div>
        </div>
      )}

      {/* 聊天历史 */}
      <div className="flex-1 overflow-y-auto p-4 space-y-4">
        {chatHistory.length === 0 ? (
          <div className="text-center py-8">
            <div className="w-16 h-16 bg-blue-100 rounded-full flex items-center justify-center mx-auto mb-4">
              <Bot className="w-8 h-8 text-blue-500" />
            </div>
            <h4 className="text-gray-800 font-medium mb-2">AI助手已就绪</h4>
            <p className="text-sm text-gray-500 max-w-xs mx-auto">
              {note
                ? '选择上方的功能按钮，或在下方输入您的问题，获取AI智能协助'
                : '请先选择或创建一篇笔记，然后使用AI助手功能'}
            </p>
            {selectedText && (
              <div className="mt-4 p-3 bg-blue-50 rounded-lg text-sm text-blue-700">
                <Zap className="w-4 h-4 inline mr-1" />
                检测到选中文本，AI将针对选中内容提供帮助
              </div>
            )}
          </div>
        ) : (
          chatHistory.map((message) => (
            <div
              key={message.id}
              className={`
                flex ${message.role === 'user' ? 'justify-end' : 'justify-start'}
              `}
            >
              <div
                className={`
                  max-w-[85%] rounded-2xl px-4 py-3 relative group
                  ${message.role === 'user'
                    ? 'bg-blue-500 text-white ml-8'
                    : 'bg-white border border-gray-200 text-gray-800 mr-8 shadow-sm'
                  }
                `}
              >
                {/* 头像 */}
                <div
                  className={`
                    absolute top-2 w-6 h-6 rounded-full flex items-center justify-center
                    ${message.role === 'user'
                      ? '-left-8 bg-blue-100'
                      : '-right-8 bg-purple-100'
                    }
                  `}
                >
                  {message.role === 'user' ? (
                    <User className="w-3 h-3 text-blue-600" />
                  ) : (
                    <Bot className="w-3 h-3 text-purple-600" />
                  )}
                </div>

                {/* 内容 */}
                <div className="text-sm whitespace-pre-wrap">
                  {message.content}
                </div>

                {/* 操作按钮 */}
                {message.role === 'assistant' && (
                  <div className="absolute top-2 right-2 opacity-0 group-hover:opacity-100 transition-opacity">
                    <button
                      onClick={() => handleCopy(message.content)}
                      className="p-1 bg-white rounded shadow-sm hover:bg-gray-100"
                      title="复制"
                    >
                      {copied ? (
                        <Check className="w-3 h-3 text-green-500" />
                      ) : (
                        <Copy className="w-3 h-3 text-gray-400" />
                      )}
                    </button>
                  </div>
                )}

                {/* 时间 */}
                <div
                  className={`
                    text-[10px] mt-1
                    ${message.role === 'user' ? 'text-blue-200' : 'text-gray-400'}
                  `}
                >
                  {new Date(message.timestamp).toLocaleTimeString('zh-CN', {
                    hour: '2-digit',
                    minute: '2-digit',
                  })}
                </div>
              </div>
            </div>
          ))
        )}
        <div ref={chatEndRef} />
      </div>

      {/* 输入框 */}
      <div className="p-4 bg-white border-t border-gray-200">
        <div className="flex items-end space-x-2">
          <div className="flex-1 relative">
            <textarea
              value={inputMessage}
              onChange={(e) => setInputMessage(e.target.value)}
              onKeyDown={(e) => {
                if (e.key === 'Enter' && !e.shiftKey) {
                  e.preventDefault();
                  sendMessage();
                }
              }}
              placeholder={note ? '输入问题或请求AI协助...' : '请先选择一篇笔记'}
              disabled={!note || isProcessing}
              rows={1}
              className="
                w-full px-4 py-3 pr-12
                bg-gray-100 border-0 rounded-xl
                resize-none outline-none
                focus:ring-2 focus:ring-blue-500
                disabled:opacity-50
                text-sm
              "
              style={{ minHeight: '48px', maxHeight: '120px' }}
            />
            {inputMessage.length > 0 && (
              <span className="absolute right-3 bottom-3 text-xs text-gray-400">
                ↵
              </span>
            )}
          </div>
          <button
            onClick={sendMessage}
            disabled={!note || !inputMessage.trim() || isProcessing}
            className="
              p-3 bg-blue-500 text-white rounded-xl
              hover:bg-blue-600 disabled:opacity-50 disabled:cursor-not-allowed
              transition-colors
            "
          >
            {isProcessing ? (
              <Loader2 className="w-5 h-5 animate-spin" />
            ) : (
              <Send className="w-5 h-5" />
            )}
          </button>
        </div>
        <p className="text-xs text-gray-400 mt-2 text-center">
          AI助手可以帮助您总结、解释、扩展笔记内容，并关联相关知识概念
        </p>
      </div>
    </div>
  );
};

export default NoteAIAssistant;
