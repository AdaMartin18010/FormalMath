import React, { useEffect, useRef, useState, useCallback } from 'react';
import { cn } from '@utils/classNames';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';

// 动态导入 KaTeX 以避免 SSR 问题
let katex: typeof import('katex') | null = null;
if (typeof window !== 'undefined') {
  import('katex').then((module) => {
    katex = module;
  });
}

interface MathRendererProps {
  formula: string;
  displayMode?: boolean;
  className?: string;
  onError?: (error: Error) => void;
  onClick?: () => void;
  expandable?: boolean;
  maxMobileWidth?: number;
}

/**
 * 移动端优化的数学公式渲染组件
 * 支持：自动缩放、横向滚动、点击展开
 */
export const MathRenderer: React.FC<MathRendererProps> = ({
  formula,
  displayMode = false,
  className,
  onError,
  onClick,
  expandable = true,
  maxMobileWidth = 320,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const contentRef = useRef<HTMLDivElement>(null);
  const [renderedHtml, setRenderedHtml] = useState<string>('');
  const [isLoading, setIsLoading] = useState(true);
  const [hasError, setHasError] = useState(false);
  const [isExpanded, setIsExpanded] = useState(false);
  const [needsScroll, setNeedsScroll] = useState(false);
  const [scale, setScale] = useState(1);
  const { isMobile, screenWidth } = useMobileDetect();

  // 渲染公式
  useEffect(() => {
    const renderFormula = async () => {
      if (!katex) {
        // 等待 KaTeX 加载
        const checkKatex = setInterval(() => {
          if (katex) {
            clearInterval(checkKatex);
            renderFormula();
          }
        }, 100);
        return;
      }

      setIsLoading(true);
      setHasError(false);

      try {
        const html = katex.renderToString(formula, {
          displayMode,
          throwOnError: false,
          strict: false,
          trust: false,
          macros: {
            // 常用数学宏
            '\R': '\mathbb{R}',
            '\N': '\mathbb{N}',
            '\Z': '\mathbb{Z}',
            '\Q': '\mathbb{Q}',
            '\C': '\mathbb{C}',
          },
        });
        setRenderedHtml(html);
      } catch (err) {
        setHasError(true);
        onError?.(err as Error);
      } finally {
        setIsLoading(false);
      }
    };

    renderFormula();
  }, [formula, displayMode, onError]);

  // 检测是否需要滚动或缩放
  useEffect(() => {
    if (!contentRef.current || !isMobile) return;

    const checkOverflow = () => {
      const content = contentRef.current;
      if (!content) return;

      const contentWidth = content.scrollWidth;
      const containerWidth = content.parentElement?.clientWidth || maxMobileWidth;
      const availableWidth = Math.min(containerWidth, maxMobileWidth);

      if (contentWidth > availableWidth) {
        setNeedsScroll(true);
        // 计算缩放比例，最小缩放到 0.7
        const newScale = Math.max(0.7, availableWidth / contentWidth);
        setScale(newScale);
      } else {
        setNeedsScroll(false);
        setScale(1);
      }
    };

    // 使用 requestAnimationFrame 确保 DOM 已更新
    requestAnimationFrame(checkOverflow);

    // 监听窗口大小变化
    window.addEventListener('resize', checkOverflow);
    return () => window.removeEventListener('resize', checkOverflow);
  }, [renderedHtml, isMobile, maxMobileWidth, screenWidth]);

  const handleClick = useCallback(() => {
    if (expandable && needsScroll) {
      setIsExpanded(!isExpanded);
    }
    onClick?.();
  }, [expandable, needsScroll, isExpanded, onClick]);

  // 处理加载状态
  if (isLoading) {
    return (
      <div
        className={cn(
          'animate-pulse bg-gray-200 dark:bg-slate-700 rounded',
          displayMode ? 'h-16' : 'h-6 inline-block w-20',
          className
        )}
      />
    );
  }

  // 处理错误状态
  if (hasError) {
    return (
      <span
        className={cn(
          'text-red-500 font-mono text-sm bg-red-50 dark:bg-red-900/20 px-2 py-1 rounded',
          className
        )}
        title={formula}
      >
        {displayMode ? '公式渲染错误' : '...'}
      </span>
    );
  }

  return (
    <div
      ref={containerRef}
      className={cn(
        'relative group',
        displayMode ? 'block my-4' : 'inline',
        needsScroll && !isExpanded && 'overflow-x-auto scrollbar-hide',
        needsScroll && isExpanded && 'overflow-visible',
        expandable && needsScroll && 'cursor-pointer',
        className
      )}
      onClick={handleClick}
      style={{
        WebkitOverflowScrolling: 'touch',
      }}
    >
      {/* 展开提示 */}
      {expandable && needsScroll && !isExpanded && (
        <div className="absolute right-0 top-0 bottom-0 w-8 bg-gradient-to-l from-white dark:from-slate-900 to-transparent pointer-events-none flex items-center justify-end pr-1">
          <span className="text-xs text-gray-400 animate-pulse">↔</span>
        </div>
      )}

      {/* 公式内容 */}
      <div
        ref={contentRef}
        className={cn(
          'transition-transform duration-200 origin-left',
          isExpanded && 'scale-100',
          !isExpanded && needsScroll && 'scale-90'
        )}
        style={{
          transform: isExpanded ? 'scale(1)' : `scale(${scale})`,
          transformOrigin: 'left center',
        }}
        dangerouslySetInnerHTML={{ __html: renderedHtml }}
      />

      {/* 展开提示文字 */}
      {expandable && needsScroll && isExpanded && (
        <div className="absolute -bottom-5 left-0 text-xs text-blue-500 animate-fadeIn">
          点击收起
        </div>
      )}

      {/* 移动端优化：触摸时的视觉反馈 */}
      {expandable && needsScroll && (
        <div className="absolute inset-0 bg-blue-500/0 group-active:bg-blue-500/10 transition-colors rounded pointer-events-none" />
      )}
    </div>
  );
};

/**
 * 批量数学公式渲染器
 * 用于渲染包含多个公式的内容块
 */
interface MathContentProps {
  content: string;
  className?: string;
}

export const MathContent: React.FC<MathContentProps> = ({ content, className }) => {
  const { isMobile } = useMobileDetect();
  const containerRef = useRef<HTMLDivElement>(null);
  const [processedContent, setProcessedContent] = useState<React.ReactNode[]>([]);

  useEffect(() => {
    // 解析文本中的数学公式
    // 支持 $...$ 行内公式和 $$...$$ 块级公式
    const parts: React.ReactNode[] = [];
    let lastIndex = 0;

    // 匹配 $$...$$ 块级公式
    const blockRegex = /\$\$([\s\S]*?)\$\$/g;
    let match;

    while ((match = blockRegex.exec(content)) !== null) {
      // 添加公式前的文本
      if (match.index > lastIndex) {
        parts.push(
          <span key={`text-${lastIndex}`}>
            {processInlineMath(content.slice(lastIndex, match.index))}
          </span>
        );
      }

      // 添加块级公式
      parts.push(
        <MathRenderer
          key={`block-${match.index}`}
          formula={match[1].trim()}
          displayMode={true}
          className="my-4"
        />
      );

      lastIndex = match.index + match[0].length;
    }

    // 添加剩余文本
    if (lastIndex < content.length) {
      parts.push(
        <span key={`text-${lastIndex}`}>
          {processInlineMath(content.slice(lastIndex))}
        </span>
      );
    }

    setProcessedContent(parts);
  }, [content]);

  // 处理行内公式 $...$
  const processInlineMath = (text: string): React.ReactNode[] => {
    const parts: React.ReactNode[] = [];
    let lastIndex = 0;
    const inlineRegex = /\$([^$\n]+?)\$/g;
    let match;

    while ((match = inlineRegex.exec(text)) !== null) {
      // 添加公式前的文本
      if (match.index > lastIndex) {
        parts.push(<span key={`inline-text-${lastIndex}`}>{text.slice(lastIndex, match.index)}</span>);
      }

      // 添加行内公式
      parts.push(
        <MathRenderer
          key={`inline-${match.index}`}
          formula={match[1].trim()}
          displayMode={false}
        />
      );

      lastIndex = match.index + match[0].length;
    }

    // 添加剩余文本
    if (lastIndex < text.length) {
      parts.push(<span key={`inline-text-${lastIndex}`}>{text.slice(lastIndex)}</span>);
    }

    return parts.length > 0 ? parts : [text];
  };

  return (
    <div
      ref={containerRef}
      className={cn(
        'math-content',
        isMobile && 'text-sm',
        className
      )}
    >
      {processedContent}
    </div>
  );
};

/**
 * 可交互的数学公式组件
 * 支持点击展开全屏查看
 */
interface InteractiveMathProps extends MathRendererProps {
  title?: string;
}

export const InteractiveMath: React.FC<InteractiveMathProps> = ({
  formula,
  title,
  displayMode = true,
  className,
  ...props
}) => {
  const [isFullscreen, setIsFullscreen] = useState(false);
  const { isMobile } = useMobileDetect();

  return (
    <>
      <div
        className={cn(
          'relative rounded-lg border border-gray-200 dark:border-slate-700',
          'bg-gray-50 dark:bg-slate-800/50',
          'p-4 cursor-pointer hover:border-blue-300 dark:hover:border-blue-700',
          'transition-colors',
          className
        )}
        onClick={() => setIsFullscreen(true)}
      >
        {title && (
          <div className="text-xs text-gray-500 dark:text-gray-400 mb-2 font-medium">
            {title}
          </div>
        )}
        <MathRenderer
          formula={formula}
          displayMode={displayMode}
          expandable={false}
          {...props}
        />
        {isMobile && (
          <div className="absolute top-2 right-2 text-gray-400">
            <svg className="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 8V4m0 0h4M4 4l5 5m11-1V4m0 0h-4m4 0l-5 5M4 16v4m0 0h4m-4 0l5-5m11 5l-5-5m5 5v-4m0 4h-4" />
            </svg>
          </div>
        )}
      </div>

      {/* 全屏弹窗 */}
      {isFullscreen && (
        <div
          className="fixed inset-0 z-50 bg-black/80 backdrop-blur-sm flex items-center justify-center p-4"
          onClick={() => setIsFullscreen(false)}
        >
          <div
            className="bg-white dark:bg-slate-900 rounded-2xl p-8 max-w-4xl w-full max-h-[90vh] overflow-auto"
            onClick={(e) => e.stopPropagation()}
          >
            <div className="flex items-center justify-between mb-4">
              {title && (
                <h3 className="text-lg font-semibold text-gray-900 dark:text-white">
                  {title}
                </h3>
              )}
              <button
                onClick={() => setIsFullscreen(false)}
                className="p-2 text-gray-500 hover:text-gray-700 dark:text-gray-400 dark:hover:text-gray-200 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-800 transition-colors"
              >
                <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
                </svg>
              </button>
            </div>
            <div className="overflow-x-auto">
              <MathRenderer
                formula={formula}
                displayMode={displayMode}
                expandable={false}
              />
            </div>
            <div className="mt-4 text-center">
              <button
                onClick={() => setIsFullscreen(false)}
                className="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
              >
                关闭
              </button>
            </div>
          </div>
        </div>
      )}
    </>
  );
};

export default MathRenderer;
