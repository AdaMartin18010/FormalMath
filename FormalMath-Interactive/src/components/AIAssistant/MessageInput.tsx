import React, { useState, useRef, useCallback, useEffect } from 'react';
import { Send, Loader2, Image as ImageIcon, X } from 'lucide-react';

interface MessageInputProps {
  onSend: (message: string) => void;
  onStop?: () => void;
  isLoading?: boolean;
  placeholder?: string;
  disabled?: boolean;
  enableLatexPreview?: boolean;
}

/**
 * 消息输入框组件
 * 
 * 支持：
 * - 多行文本输入
 * - LaTeX公式实时预览
 * - 发送快捷键（Enter发送，Shift+Enter换行）
 * - 输入状态指示
 */
export const MessageInput: React.FC<MessageInputProps> = ({
  onSend,
  onStop,
  isLoading = false,
  placeholder = '输入问题，支持LaTeX公式...',
  disabled = false,
  enableLatexPreview = true,
}) => {
  const [input, setInput] = useState('');
  const [showPreview, setShowPreview] = useState(false);
  const textareaRef = useRef<HTMLTextAreaElement>(null);

  // 自动调整文本框高度
  const adjustTextareaHeight = useCallback(() => {
    const textarea = textareaRef.current;
    if (textarea) {
      textarea.style.height = 'auto';
      textarea.style.height = Math.min(textarea.scrollHeight, 200) + 'px';
    }
  }, []);

  useEffect(() => {
    adjustTextareaHeight();
  }, [input, adjustTextareaHeight]);

  // 处理发送
  const handleSend = useCallback(() => {
    const trimmed = input.trim();
    if (trimmed && !isLoading && !disabled) {
      onSend(trimmed);
      setInput('');
      setShowPreview(false);
      
      // 重置文本框高度
      if (textareaRef.current) {
        textareaRef.current.style.height = 'auto';
      }
    }
  }, [input, isLoading, disabled, onSend]);

  // 处理键盘事件
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault();
      handleSend();
    }
  }, [handleSend]);

  // 提取LaTeX公式进行预览
  const latexPreview = React.useMemo(() => {
    if (!enableLatexPreview || !input) return null;
    
    // 匹配行间公式 $$...$$ 和行内公式 $...$
    const blockFormulas = input.match(/\$\$[\s\S]*?\$\$/g) || [];
    const inlineFormulas = input.match(/\$[^$\n]+\$/g) || [];
    
    return [...blockFormulas, ...inlineFormulas].slice(0, 3); // 最多显示3个
  }, [input, enableLatexPreview]);

  return (
    <div className="border-t border-gray-200 bg-white">
      {/* LaTeX预览区域 */}
      {enableLatexPreview && latexPreview && latexPreview.length > 0 && showPreview && (
        <div className="px-4 py-2 bg-gray-50 border-b border-gray-100">
          <div className="flex items-center justify-between mb-2">
            <span className="text-xs text-gray-500">LaTeX预览</span>
            <button
              onClick={() => setShowPreview(false)}
              className="p-1 hover:bg-gray-200 rounded transition-colors"
            >
              <X className="w-3 h-3 text-gray-400" />
            </button>
          </div>
          <div className="space-y-1">
            {latexPreview.map((formula, index) => (
              <code
                key={index}
                className="block text-xs text-blue-600 bg-blue-50 px-2 py-1 rounded overflow-x-auto"
              >
                {formula}
              </code>
            ))}
          </div>
        </div>
      )}

      {/* 输入区域 */}
      <div className="p-4">
        <div className="relative flex items-end gap-2">
          {/* 文本输入框 */}
          <div className="flex-1 relative">
            <textarea
              ref={textareaRef}
              value={input}
              onChange={(e) => setInput(e.target.value)}
              onKeyDown={handleKeyDown}
              placeholder={placeholder}
              disabled={disabled || isLoading}
              rows={1}
              className="w-full px-4 py-3 pr-10 bg-gray-100 border-0 rounded-xl resize-none
                       focus:ring-2 focus:ring-blue-500 focus:bg-white
                       disabled:opacity-50 disabled:cursor-not-allowed
                       transition-all duration-200"
              style={{ minHeight: '48px', maxHeight: '200px' }}
            />
            
            {/* LaTeX指示器 */}
            {enableLatexPreview && latexPreview && latexPreview.length > 0 && !showPreview && (
              <button
                onClick={() => setShowPreview(true)}
                className="absolute right-3 top-1/2 -translate-y-1/2 p-1 
                         text-gray-400 hover:text-blue-500 transition-colors"
                title="显示LaTeX预览"
              >
                <span className="text-xs font-mono">$\Sigma$</span>
              </button>
            )}
          </div>

          {/* 发送/停止按钮 */}
          {isLoading ? (
            <button
              onClick={onStop}
              className="flex-shrink-0 p-3 bg-red-100 text-red-600 rounded-xl
                       hover:bg-red-200 transition-colors"
              title="停止生成"
            >
              <div className="w-5 h-5 flex items-center justify-center">
                <div className="w-3 h-3 bg-current rounded-sm" />
              </div>
            </button>
          ) : (
            <button
              onClick={handleSend}
              disabled={!input.trim() || disabled}
              className="flex-shrink-0 p-3 bg-blue-600 text-white rounded-xl
                       hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed
                       transition-all duration-200 hover:shadow-lg"
              title="发送消息 (Enter)"
            >
              <Send className="w-5 h-5" />
            </button>
          )}
        </div>

        {/* 提示文字 */}
        <div className="flex items-center justify-between mt-2 text-xs text-gray-400">
          <span>Enter 发送，Shift + Enter 换行</span>
          {isLoading && <span className="flex items-center gap-1"><Loader2 className="w-3 h-3 animate-spin" /> 生成中...</span>}
        </div>
      </div>
    </div>
  );
};

export default MessageInput;
