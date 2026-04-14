// @ts-nocheck
// ==================== 笔记编辑器组件 ====================
import React, { useState, useCallback, useEffect, useRef, useMemo } from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { vscDarkPlus } from 'react-syntax-highlighter/dist/esm/styles/prism';
import 'katex/dist/katex.min.css';
import { useNoteStore } from '../../stores/noteStore';
import { aiAssistant, autoSaveNote, updateNote } from '../../services/noteService';
import type { NoteAIChatMessage, NoteAIRequest } from '../../types/notes';
import { LaTeXToolbar } from './LaTeXToolbar';
import { NoteTemplates, defaultTemplates } from './NoteTemplates';
import {
  Save,
  Eye,
  Edit3,
  Columns,
  Sparkles,
  Search,
  Tag,
  Share2,
  Clock,
  MoreVertical,
  Bold,
  Italic,
  Code,
  Link,
  Image,
  List,
  ListOrdered,
  Quote,
  Heading1,
  Heading2,
  Undo,
  Redo,
  Maximize2,
  Minimize2,
  Wand2,
  Loader2,
  Check,
  AlertCircle,
  Calculator,
  Layout,
  FileText,
  X,
  Sigma,
  FunctionSquare,
} from 'lucide-react';

interface NoteEditorProps {
  noteId?: string;
  className?: string;
}

// 工具栏按钮
interface ToolbarButtonProps {
  icon: React.ReactNode;
  label: string;
  onClick: () => void;
  active?: boolean;
  disabled?: boolean;
}

const ToolbarButton: React.FC<ToolbarButtonProps> = ({
  icon,
  label,
  onClick,
  active,
  disabled,
}) => (
  <button
    onClick={onClick}
    disabled={disabled}
    title={label}
    className={`
      p-2 rounded-lg transition-all duration-200
      ${active ? 'bg-blue-500 text-white' : 'hover:bg-gray-100 text-gray-600'}
      ${disabled ? 'opacity-50 cursor-not-allowed' : 'cursor-pointer'}
      focus:outline-none focus:ring-2 focus:ring-blue-400
    `}
  >
    {icon}
  </button>
);

// 分隔线
const ToolbarDivider: React.FC = () => (
  <div className="w-px h-6 bg-gray-200 mx-2" />
);

export const NoteEditor: React.FC<NoteEditorProps> = ({ noteId, className = '' }) => {
  const textareaRef = useRef<HTMLTextAreaElement>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [showAIAssistant, setShowAIAssistant] = useState(false);
  const [aiChatInput, setAiChatInput] = useState('');
  const [localChatHistory, setLocalChatHistory] = useState<NoteAIChatMessage[]>([]);
  const [isAIProcessing, setIsAIProcessing] = useState(false);
  const [showLaTeXToolbar, setShowLaTeXToolbar] = useState(false);
  const [showTemplates, setShowTemplates] = useState(false);
  
  const {
    editor,
    updateEditorContent,
    updateEditorTitle,
    setEditorDirty,
    setEditorSaving,
    setEditorViewMode,
    setSelectedText,
    addNote,
  } = useNoteStore();

  const { currentNote, isDirty, isSaving, viewMode, autoSaveEnabled, selectedText } = editor;

  // 自动保存定时器
  const autoSaveTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  // 格式化时间
  const formatTime = useCallback((date: string) => {
    return new Date(date).toLocaleTimeString('zh-CN', {
      hour: '2-digit',
      minute: '2-digit',
    });
  }, []);

  // 插入Markdown语法
  const insertMarkdown = useCallback((before: string, after: string = '') => {
    const textarea = textareaRef.current;
    if (!textarea) return;

    const start = textarea.selectionStart;
    const end = textarea.selectionEnd;
    const text = currentNote?.content || '';
    const selected = text.substring(start, end);
    
    const newContent = text.substring(0, start) + before + selected + after + text.substring(end);
    updateEditorContent(newContent);
    
    // 恢复焦点和选择
    setTimeout(() => {
      textarea.focus();
      const newCursorPos = start + before.length + selected.length;
      textarea.setSelectionRange(newCursorPos, newCursorPos);
    }, 0);
  }, [currentNote?.content, updateEditorContent]);

  // 工具栏操作
  const toolbarActions = {
    bold: () => insertMarkdown('**', '**'),
    italic: () => insertMarkdown('*', '*'),
    code: () => insertMarkdown('`', '`'),
    codeBlock: () => insertMarkdown('```\n', '\n```'),
    link: () => insertMarkdown('[', '](url)'),
    image: () => insertMarkdown('![alt](', ')'),
    bulletList: () => insertMarkdown('\n- '),
    orderedList: () => insertMarkdown('\n1. '),
    quote: () => insertMarkdown('\n> '),
    heading1: () => insertMarkdown('\n# '),
    heading2: () => insertMarkdown('\n## '),
    inlineMath: () => insertMarkdown('$', '$'),
    blockMath: () => insertMarkdown('$$\n', '\n$$'),
  };

  // 插入LaTeX公式
  const insertLaTeX = useCallback((latex: string) => {
    const textarea = textareaRef.current;
    if (!textarea) return;

    const start = textarea.selectionStart;
    const end = textarea.selectionEnd;
    const text = currentNote?.content || '';
    
    // 检查是否需要行内或块级公式
    const isBlock = latex.includes('\\begin') || latex.includes('\\frac') || latex.includes('\\sum') || latex.includes('\\int');
    const wrapper = isBlock ? '$$' : '$';
    
    const newContent = text.substring(0, start) + wrapper + latex + wrapper + text.substring(end);
    updateEditorContent(newContent);
    
    setTimeout(() => {
      textarea.focus();
      const newCursorPos = start + wrapper.length + latex.length + wrapper.length;
      textarea.setSelectionRange(newCursorPos, newCursorPos);
    }, 0);
  }, [currentNote?.content, updateEditorContent]);

  // 应用模板
  const handleApplyTemplate = useCallback((template: any) => {
    if (!currentNote) return;
    
    if (template.id === 'blank') {
      updateEditorContent('');
    } else {
      updateEditorContent(template.content);
    }
    setShowTemplates(false);
  }, [currentNote, updateEditorContent]);

  // 保存笔记
  const handleSave = useCallback(async () => {
    if (!currentNote || !isDirty) return;
    
    setEditorSaving(true);
    try {
      await updateNote(currentNote.id, {
        title: currentNote.title,
        content: currentNote.content,
      });
      setEditorDirty(false);
    } catch (error) {
      console.error('Save failed:', error);
    } finally {
      setEditorSaving(false);
    }
  }, [currentNote, isDirty, setEditorDirty, setEditorSaving]);

  // 自动保存
  useEffect(() => {
    if (autoSaveEnabled && isDirty && currentNote && !isSaving) {
      if (autoSaveTimerRef.current) {
        clearTimeout(autoSaveTimerRef.current);
      }
      autoSaveTimerRef.current = setTimeout(() => {
        handleSave();
      }, 3000);
    }

    return () => {
      if (autoSaveTimerRef.current) {
        clearTimeout(autoSaveTimerRef.current);
      }
    };
  }, [autoSaveEnabled, isDirty, currentNote, isSaving, handleSave]);

  // 键盘快捷键
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      if ((e.metaKey || e.ctrlKey) && e.key === 's') {
        e.preventDefault();
        handleSave();
      }
      if ((e.metaKey || e.ctrlKey) && e.key === 'b') {
        e.preventDefault();
        toolbarActions.bold();
      }
      if ((e.metaKey || e.ctrlKey) && e.key === 'i') {
        e.preventDefault();
        toolbarActions.italic();
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [handleSave]);

  // 选择文本变化
  const handleSelect = useCallback(() => {
    const textarea = textareaRef.current;
    if (!textarea || !currentNote) return;
    
    const selected = textarea.value.substring(textarea.selectionStart, textarea.selectionEnd);
    setSelectedText(selected || undefined);
  }, [currentNote, setSelectedText]);

  // AI助手处理
  const handleAIRequest = useCallback(async (type: NoteAIRequest['type']) => {
    if (!currentNote) return;
    
    setIsAIProcessing(true);
    const userMessage: NoteAIChatMessage = {
      id: Date.now().toString(),
      role: 'user',
      content: type === 'explain' ? '解释选中的内容' : 
               type === 'summarize' ? '总结这篇笔记' :
               type === 'expand' ? '扩展这个想法' :
               type === 'relate' ? '关联相关知识' : '请协助',
      timestamp: new Date().toISOString(),
    };
    setLocalChatHistory((prev) => [...prev, userMessage]);

    try {
      const response = await aiAssistant({
        type,
        content: selectedText || currentNote.content,
        context: {
          noteId: currentNote.id,
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
        setLocalChatHistory((prev) => [...prev, assistantMessage]);
      }
    } catch (error) {
      const errorMessage: NoteAIChatMessage = {
        id: (Date.now() + 1).toString(),
        role: 'assistant',
        content: '抱歉，AI助手暂时无法处理您的请求。请稍后重试。',
        timestamp: new Date().toISOString(),
      };
      setLocalChatHistory((prev) => [...prev, errorMessage]);
    } finally {
      setIsAIProcessing(false);
    }
  }, [currentNote, selectedText]);

  // 发送AI消息
  const handleSendAIMessage = useCallback(async () => {
    if (!aiChatInput.trim() || !currentNote) return;
    
    setIsAIProcessing(true);
    const userMessage: NoteAIChatMessage = {
      id: Date.now().toString(),
      role: 'user',
      content: aiChatInput,
      timestamp: new Date().toISOString(),
    };
    setLocalChatHistory((prev) => [...prev, userMessage]);
    setAiChatInput('');

    try {
      const response = await aiAssistant({
        type: 'suggest',
        content: aiChatInput,
        context: {
          noteId: currentNote.id,
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
        setLocalChatHistory((prev) => [...prev, assistantMessage]);
      }
    } catch (error) {
      const errorMessage: NoteAIChatMessage = {
        id: (Date.now() + 1).toString(),
        role: 'assistant',
        content: '抱歉，AI助手暂时无法处理您的请求。请稍后重试。',
        timestamp: new Date().toISOString(),
      };
      setLocalChatHistory((prev) => [...prev, errorMessage]);
    } finally {
      setIsAIProcessing(false);
    }
  }, [aiChatInput, currentNote, selectedText]);

  // 渲染Markdown组件
  const MarkdownComponents = useMemo(() => ({
    code({ node, inline, className, children, ...props }: any) {
      const match = /language-(\w+)/.exec(className || '');
      return !inline && match ? (
        <SyntaxHighlighter
          style={vscDarkPlus}
          language={match[1]}
          PreTag="div"
          {...props}
        >
          {String(children).replace(/\n$/, '')}
        </SyntaxHighlighter>
      ) : (
        <code className="bg-gray-100 px-1 py-0.5 rounded text-sm font-mono" {...props}>
          {children}
        </code>
      );
    },
  }), []);

  if (!currentNote) {
    return (
      <div className={`flex items-center justify-center h-full text-gray-400 ${className}`}>
        <div className="text-center">
          <Edit3 className="w-12 h-12 mx-auto mb-4 opacity-50" />
          <p>选择或创建一篇笔记开始编辑</p>
        </div>
      </div>
    );
  }

  return (
    <div
      className={`
        flex flex-col bg-white rounded-xl shadow-sm border border-gray-200
        ${isFullscreen ? 'fixed inset-0 z-50' : 'h-full'}
        ${className}
      `}
    >
      {/* 顶部工具栏 */}
      <div className="flex items-center justify-between px-4 py-2 border-b border-gray-200 bg-gray-50 rounded-t-xl">
        {/* 左侧工具栏 */}
        <div className="flex items-center space-x-1">
          <ToolbarButton
            icon={<Bold size={18} />}
            label="粗体 (Ctrl+B)"
            onClick={toolbarActions.bold}
          />
          <ToolbarButton
            icon={<Italic size={18} />}
            label="斜体 (Ctrl+I)"
            onClick={toolbarActions.italic}
          />
          <ToolbarDivider />
          <ToolbarButton
            icon={<Heading1 size={18} />}
            label="标题1"
            onClick={toolbarActions.heading1}
          />
          <ToolbarButton
            icon={<Heading2 size={18} />}
            label="标题2"
            onClick={toolbarActions.heading2}
          />
          <ToolbarDivider />
          <ToolbarButton
            icon={<List size={18} />}
            label="无序列表"
            onClick={toolbarActions.bulletList}
          />
          <ToolbarButton
            icon={<ListOrdered size={18} />}
            label="有序列表"
            onClick={toolbarActions.orderedList}
          />
          <ToolbarButton
            icon={<Quote size={18} />}
            label="引用"
            onClick={toolbarActions.quote}
          />
          <ToolbarDivider />
          <ToolbarButton
            icon={<Code size={18} />}
            label="代码"
            onClick={toolbarActions.code}
          />
          <ToolbarButton
            icon={<span className="text-xs font-mono">```</span>}
            label="代码块"
            onClick={toolbarActions.codeBlock}
          />
          <ToolbarButton
            icon={<Link size={18} />}
            label="链接"
            onClick={toolbarActions.link}
          />
          <ToolbarButton
            icon={<Image size={18} />}
            label="图片"
            onClick={toolbarActions.image}
          />
          <ToolbarDivider />
          <ToolbarButton
            icon={<Sigma size={18} />}
            label="行内公式"
            onClick={toolbarActions.inlineMath}
          />
          <ToolbarButton
            icon={<FunctionSquare size={18} />}
            label="公式块"
            onClick={toolbarActions.blockMath}
          />
        </div>

        {/* 右侧控制 */}
        <div className="flex items-center space-x-2">
          {/* 视图模式切换 */}
          <div className="flex items-center bg-gray-200 rounded-lg p-1">
            <ToolbarButton
              icon={<Edit3 size={16} />}
              label="编辑模式"
              onClick={() => setEditorViewMode('edit')}
              active={viewMode === 'edit'}
            />
            <ToolbarButton
              icon={<Columns size={16} />}
              label="分屏模式"
              onClick={() => setEditorViewMode('split')}
              active={viewMode === 'split'}
            />
            <ToolbarButton
              icon={<Eye size={16} />}
              label="预览模式"
              onClick={() => setEditorViewMode('preview')}
              active={viewMode === 'preview'}
            />
          </div>

          <ToolbarDivider />

          {/* 模板按钮 */}
          <ToolbarButton
            icon={<Layout size={18} />}
            label="模板"
            onClick={() => setShowTemplates(true)}
          />

          {/* LaTeX工具栏按钮 */}
          <ToolbarButton
            icon={<Calculator size={18} />}
            label="LaTeX公式"
            onClick={() => setShowLaTeXToolbar(!showLaTeXToolbar)}
            active={showLaTeXToolbar}
          />

          {/* AI助手按钮 */}
          <ToolbarButton
            icon={<Sparkles size={18} />}
            label="AI助手"
            onClick={() => setShowAIAssistant(!showAIAssistant)}
            active={showAIAssistant}
          />

          <ToolbarDivider />

          {/* 保存状态 */}
          <div className="flex items-center text-sm text-gray-500">
            {isSaving ? (
              <>
                <Loader2 size={14} className="animate-spin mr-1" />
                保存中...
              </>
            ) : isDirty ? (
              <>
                <AlertCircle size={14} className="mr-1 text-yellow-500" />
                未保存
              </>
            ) : (
              <>
                <Check size={14} className="mr-1 text-green-500" />
                已保存
              </>
            )}
          </div>

          {/* 保存按钮 */}
          <button
            onClick={handleSave}
            disabled={!isDirty || isSaving}
            className="
              flex items-center px-3 py-1.5 bg-blue-500 text-white rounded-lg
              hover:bg-blue-600 disabled:opacity-50 disabled:cursor-not-allowed
              transition-colors
            "
          >
            <Save size={16} className="mr-1" />
            保存
          </button>

          {/* 全屏切换 */}
          <ToolbarButton
            icon={isFullscreen ? <Minimize2 size={18} /> : <Maximize2 size={18} />}
            label={isFullscreen ? '退出全屏' : '全屏'}
            onClick={() => setIsFullscreen(!isFullscreen)}
          />
        </div>
      </div>

      {/* 标题栏 */}
      <div className="px-4 py-3 border-b border-gray-200">
        <input
          type="text"
          value={currentNote.title}
          onChange={(e) => updateEditorTitle(e.target.value)}
          placeholder="笔记标题..."
          className="
            w-full text-2xl font-bold text-gray-800 placeholder-gray-400
            border-none outline-none bg-transparent
            focus:ring-0
          "
        />
        <div className="flex items-center mt-2 text-xs text-gray-400 space-x-4">
          <span>创建于 {formatTime(currentNote.createdAt)}</span>
          <span>更新于 {formatTime(currentNote.updatedAt)}</span>
          <span>{currentNote.wordCount} 字</span>
        </div>
      </div>

      {/* 编辑区域 */}
      <div className="flex flex-1 overflow-hidden">
        {/* 编辑器 */}
        {(viewMode === 'edit' || viewMode === 'split') && (
          <div
            className={`
              ${viewMode === 'split' ? 'w-1/2 border-r border-gray-200' : 'w-full'}
              flex flex-col
            `}
          >
            <textarea
              ref={textareaRef}
              value={currentNote.content}
              onChange={(e) => updateEditorContent(e.target.value)}
              onSelect={handleSelect}
              placeholder="开始编写笔记... 支持 Markdown 和 LaTeX 公式"
              className="
                flex-1 w-full p-4 resize-none outline-none
                font-mono text-sm leading-relaxed
                bg-white text-gray-800
                placeholder-gray-400
              "
              spellCheck={false}
            />
          </div>
        )}

        {/* 预览区 */}
        {(viewMode === 'preview' || viewMode === 'split') && (
          <div
            className={`
              ${viewMode === 'split' ? 'w-1/2' : 'w-full'}
              flex flex-col bg-white
            `}
          >
            <div className="flex-1 p-4 overflow-auto prose prose-slate max-w-none">
              <ReactMarkdown
                remarkPlugins={[remarkMath]}
                rehypePlugins={[rehypeKatex]}
                components={MarkdownComponents}
              >
                {currentNote.content || '_开始编写笔记..._'}
              </ReactMarkdown>
            </div>
          </div>
        )}

        {/* LaTeX工具栏 */}
        {showLaTeXToolbar && (
          <div className="absolute top-16 right-4 z-10 w-96">
            <LaTeXToolbar onInsert={insertLaTeX} />
          </div>
        )}

        {/* AI助手侧边栏 */}
        {showAIAssistant && (
          <div className="w-80 border-l border-gray-200 bg-gray-50 flex flex-col">
            <div className="px-4 py-3 border-b border-gray-200 bg-white">
              <div className="flex items-center text-gray-800 font-medium">
                <Sparkles size={18} className="mr-2 text-blue-500" />
                AI 笔记助手
              </div>
              <p className="text-xs text-gray-500 mt-1">
                选中笔记内容，获取AI智能帮助
              </p>
            </div>

            {/* AI功能按钮 */}
            <div className="p-3 grid grid-cols-2 gap-2 border-b border-gray-200">
              <button
                onClick={() => handleAIRequest('summarize')}
                disabled={isAIProcessing}
                className="flex items-center justify-center px-3 py-2 bg-white border border-gray-200 rounded-lg text-sm hover:bg-gray-50 disabled:opacity-50"
              >
                <Wand2 size={14} className="mr-1" />
                总结
              </button>
              <button
                onClick={() => handleAIRequest('explain')}
                disabled={isAIProcessing}
                className="flex items-center justify-center px-3 py-2 bg-white border border-gray-200 rounded-lg text-sm hover:bg-gray-50 disabled:opacity-50"
              >
                <Search size={14} className="mr-1" />
                解释
              </button>
              <button
                onClick={() => handleAIRequest('expand')}
                disabled={isAIProcessing}
                className="flex items-center justify-center px-3 py-2 bg-white border border-gray-200 rounded-lg text-sm hover:bg-gray-50 disabled:opacity-50"
              >
                <Sparkles size={14} className="mr-1" />
                扩展
              </button>
              <button
                onClick={() => handleAIRequest('relate')}
                disabled={isAIProcessing}
                className="flex items-center justify-center px-3 py-2 bg-white border border-gray-200 rounded-lg text-sm hover:bg-gray-50 disabled:opacity-50"
              >
                <Link size={14} className="mr-1" />
                关联
              </button>
            </div>

            {/* 聊天历史 */}
            <div className="flex-1 overflow-y-auto p-3 space-y-3">
              {localChatHistory.length === 0 ? (
                <div className="text-center text-gray-400 py-8">
                  <Sparkles size={32} className="mx-auto mb-2 opacity-50" />
                  <p className="text-sm">AI助手已就绪</p>
                  <p className="text-xs mt-1">输入问题或选择功能开始对话</p>
                </div>
              ) : (
                localChatHistory.map((msg) => (
                  <div
                    key={msg.id}
                    className={`
                      p-3 rounded-lg text-sm
                      ${msg.role === 'user'
                        ? 'bg-blue-500 text-white ml-4'
                        : 'bg-white border border-gray-200 mr-4'
                      }
                    `}
                  >
                    {msg.content}
                  </div>
                ))
              )}
              {isAIProcessing && (
                <div className="flex items-center justify-center py-2">
                  <Loader2 size={20} className="animate-spin text-blue-500" />
                </div>
              )}
            </div>

            {/* 输入框 */}
            <div className="p-3 border-t border-gray-200 bg-white">
              <div className="flex items-center space-x-2">
                <input
                  type="text"
                  value={aiChatInput}
                  onChange={(e) => setAiChatInput(e.target.value)}
                  onKeyPress={(e) => e.key === 'Enter' && handleSendAIMessage()}
                  placeholder="输入问题..."
                  disabled={isAIProcessing}
                  className="
                    flex-1 px-3 py-2 border border-gray-200 rounded-lg
                    text-sm outline-none focus:ring-2 focus:ring-blue-400
                    disabled:opacity-50
                  "
                />
                <button
                  onClick={handleSendAIMessage}
                  disabled={!aiChatInput.trim() || isAIProcessing}
                  className="
                    px-3 py-2 bg-blue-500 text-white rounded-lg
                    hover:bg-blue-600 disabled:opacity-50
                    transition-colors
                  "
                >
                  发送
                </button>
              </div>
            </div>
          </div>
        )}
      </div>

      {/* 模板选择弹窗 */}
      {showTemplates && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <NoteTemplates
            onSelectTemplate={handleApplyTemplate}
            onClose={() => setShowTemplates(false)}
            className="w-[800px] max-h-[80vh]"
          />
        </div>
      )}
    </div>
  );
};

export default NoteEditor;
