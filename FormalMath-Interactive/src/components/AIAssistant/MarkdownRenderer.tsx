import React, { useEffect, useRef } from 'react';
import ReactMarkdown from 'react-markdown';
import { Prism as SyntaxHighlighter } from 'react-syntax-highlighter';
import { vscDarkPlus } from 'react-syntax-highlighter/dist/esm/styles/prism';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import 'katex/dist/katex.min.css';

// 扩展CodeLanguage类型
 type CodeLanguage = 'lean4' | 'lean' | 'latex' | 'python' | 'javascript' | 'typescript' | 'markdown' | 'text' | string;

interface MarkdownRendererProps {
  content: string;
  className?: string;
  enableMath?: boolean;
  enableCodeHighlight?: boolean;
}

/**
 * Markdown渲染组件
 * 
 * 功能特性：
 * - 支持标准Markdown语法
 * - 数学公式渲染（KaTeX）
 * - 代码高亮（支持Lean4语法）
 * - 自定义样式
 */
export const MarkdownRenderer: React.FC<MarkdownRendererProps> = ({
  content,
  className = '',
  enableMath = true,
  enableCodeHighlight = true,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);

  // 渲染代码块
  const CodeBlock: React.FC<{
    inline?: boolean;
    className?: string;
    children?: React.ReactNode;
  }> = ({ inline, className, children }) => {
    const match = /language-(\w+)/.exec(className || '');
    const language = (match?.[1] || 'text') as CodeLanguage;
    
    // 处理Lean4语言标识
    const normalizedLang = language === 'lean4' ? 'lean' : language;

    if (inline) {
      return (
        <code className="px-1.5 py-0.5 bg-gray-100 text-gray-800 rounded text-sm font-mono">
          {children}
        </code>
      );
    }

    if (!enableCodeHighlight) {
      return (
        <pre className="bg-gray-900 text-gray-100 p-4 rounded-lg overflow-x-auto">
          <code className="text-sm font-mono">{children}</code>
        </pre>
      );
    }

    return (
      <div className="relative group">
        {/* 语言标签 */}
        <div className="absolute top-0 right-0 px-3 py-1 text-xs text-gray-400 bg-gray-800 rounded-bl-lg">
          {language === 'lean' || language === 'lean4' ? 'Lean 4' : language}
        </div>
        
        {/* 复制按钮 */}
        <button
          onClick={() => {
            const code = String(children).replace(/\n$/, '');
            navigator.clipboard.writeText(code);
          }}
          className="absolute top-0 right-0 mt-8 mr-2 px-2 py-1 text-xs text-gray-400 
                   bg-gray-800 rounded opacity-0 group-hover:opacity-100 
                   hover:text-white transition-opacity"
        >
          复制
        </button>

        <SyntaxHighlighter
          style={vscDarkPlus}
          language={normalizedLang}
          PreTag="div"
          customStyle={{
            margin: 0,
            borderRadius: '0.5rem',
            padding: '1.5rem 1rem 1rem',
            fontSize: '0.875rem',
            lineHeight: '1.5',
          }}
        >
          {String(children).replace(/\n$/, '')}
        </SyntaxHighlighter>
      </div>
    );
  };

  // 自定义链接渲染
  const Link: React.FC<{ href?: string; children?: React.ReactNode }> = ({ href, children }) => {
    const isExternal = href?.startsWith('http');
    return (
      <a
        href={href}
        target={isExternal ? '_blank' : undefined}
        rel={isExternal ? 'noopener noreferrer' : undefined}
        className="text-blue-600 hover:text-blue-800 underline underline-offset-2"
      >
        {children}
      </a>
    );
  };

  // 自定义表格渲染
  const Table: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <div className="overflow-x-auto my-4">
      <table className="min-w-full border-collapse border border-gray-300">
        {children}
      </table>
    </div>
  );

  const TableHead: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <thead className="bg-gray-100">{children}</thead>
  );

  const TableRow: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <tr className="border-b border-gray-200">{children}</tr>
  );

  const TableCell: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <td className="px-4 py-2 border border-gray-200">{children}</td>
  );

  const TableHeader: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <th className="px-4 py-2 border border-gray-200 font-semibold text-left">{children}</th>
  );

  // 自定义列表渲染
  const List: React.FC<{ ordered?: boolean; children?: React.ReactNode }> = ({ ordered, children }) => {
    if (ordered) {
      return <ol className="list-decimal pl-6 my-2 space-y-1">{children}</ol>;
    }
    return <ul className="list-disc pl-6 my-2 space-y-1">{children}</ul>;
  };

  // 自定义标题渲染
  const Heading: React.FC<{ level: number; children?: React.ReactNode }> = ({ level, children }) => {
    const sizes: Record<number, string> = {
      1: 'text-2xl font-bold mt-6 mb-4',
      2: 'text-xl font-bold mt-5 mb-3',
      3: 'text-lg font-semibold mt-4 mb-2',
      4: 'text-base font-semibold mt-3 mb-2',
      5: 'text-sm font-semibold mt-2 mb-1',
      6: 'text-xs font-semibold mt-2 mb-1',
    };
    
    const Tag = `h${level}` as keyof JSX.IntrinsicElements;
    return <Tag className={`${sizes[level]} text-gray-900`}>{children}</Tag>;
  };

  // 自定义段落渲染
  const Paragraph: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <p className="my-3 leading-relaxed text-gray-700">{children}</p>
  );

  // 自定义引用块渲染
  const Blockquote: React.FC<{ children?: React.ReactNode }> = ({ children }) => (
    <blockquote className="border-l-4 border-blue-500 pl-4 my-4 italic text-gray-600 bg-blue-50 py-2 pr-4 rounded-r">
      {children}
    </blockquote>
  );

  // 自定义分割线渲染
  const Divider: React.FC = () => (
    <hr className="my-6 border-gray-200" />
  );

  // 自定义图片渲染
  const Image: React.FC<{ src?: string; alt?: string }> = ({ src, alt }) => (
    <img 
      src={src} 
      alt={alt} 
      className="max-w-full h-auto rounded-lg shadow-md my-4"
      loading="lazy"
    />
  );

  return (
    <div 
      ref={containerRef}
      className={`prose prose-blue max-w-none ${className}`}
    >
      <ReactMarkdown
        remarkPlugins={enableMath ? [remarkMath] : []}
        rehypePlugins={enableMath ? [rehypeKatex] : []}
        components={{
          code: CodeBlock,
          a: Link,
          table: Table,
          thead: TableHead,
          tr: TableRow,
          td: TableCell,
          th: TableHeader,
          ul: (props) => <List {...props} />,
          ol: (props) => <List {...props} ordered />,
          h1: (props) => <Heading {...props} level={1} />,
          h2: (props) => <Heading {...props} level={2} />,
          h3: (props) => <Heading {...props} level={3} />,
          h4: (props) => <Heading {...props} level={4} />,
          h5: (props) => <Heading {...props} level={5} />,
          h6: (props) => <Heading {...props} level={6} />,
          p: Paragraph,
          blockquote: Blockquote,
          hr: Divider,
          img: Image,
        }}
      >
        {content}
      </ReactMarkdown>
    </div>
  );
};

export default MarkdownRenderer;
