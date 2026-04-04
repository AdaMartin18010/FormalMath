import React, { useEffect, useState, useRef } from 'react';
import mermaid from 'mermaid';
import { Loader2, AlertCircle, Download, Copy, Check, RefreshCw } from 'lucide-react';
import { cn } from '@utils/classNames';

interface MermaidChartProps {
  definition: string;
  className?: string;
  theme?: 'default' | 'dark' | 'forest' | 'neutral';
  onNodeClick?: (nodeId: string) => void;
}

export const MermaidChart: React.FC<MermaidChartProps> = ({
  definition,
  className,
  theme = 'default',
  onNodeClick,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const [svg, setSvg] = useState<string>('');
  const [error, setError] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState(true);
  const [isCopied, setIsCopied] = useState(false);

  // 初始化Mermaid
  useEffect(() => {
    mermaid.initialize({
      startOnLoad: false,
      theme,
      securityLevel: 'loose',
      flowchart: {
        useMaxWidth: true,
        htmlLabels: true,
        curve: 'basis',
        padding: 20,
      },
      sequence: {
        useMaxWidth: true,
        diagramMarginX: 50,
        diagramMarginY: 10,
      },
      gantt: {
        useMaxWidth: true,
        leftPadding: 75,
        gridLineStartPadding: 35,
        fontSize: 11,
        sectionFontSize: 24,
        numberSectionStyles: 4,
      },
    });
  }, [theme]);

  // 渲染图表
  useEffect(() => {
    const renderChart = async () => {
      if (!definition.trim()) {
        setSvg('');
        setError(null);
        setIsLoading(false);
        return;
      }

      setIsLoading(true);
      setError(null);

      try {
        // 验证语法
        const valid = await mermaid.parse(definition);
        if (!valid) {
          throw new Error('Invalid Mermaid syntax');
        }

        // 渲染
        const id = `mermaid-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
        const { svg: renderedSvg } = await mermaid.render(id, definition);
        
        setSvg(renderedSvg);
      } catch (err) {
        const message = err instanceof Error ? err.message : 'Failed to render chart';
        setError(message);
        setSvg('');
      } finally {
        setIsLoading(false);
      }
    };

    renderChart();
  }, [definition, theme]);

  // 处理节点点击
  useEffect(() => {
    if (!containerRef.current || !onNodeClick) return;

    const container = containerRef.current;
    const handleClick = (e: MouseEvent) => {
      const target = e.target as HTMLElement;
      const nodeElement = target.closest('.node');
      if (nodeElement) {
        const nodeId = nodeElement.id;
        if (nodeId) {
          onNodeClick(nodeId);
        }
      }
    };

    container.addEventListener('click', handleClick);
    return () => container.removeEventListener('click', handleClick);
  }, [onNodeClick]);

  const handleDownload = () => {
    if (!svg) return;
    const blob = new Blob([svg], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `mermaid-chart-${Date.now()}.svg`;
    link.click();
    URL.revokeObjectURL(url);
  };

  const handleCopy = async () => {
    if (!definition) return;
    try {
      await navigator.clipboard.writeText(definition);
      setIsCopied(true);
      setTimeout(() => setIsCopied(false), 2000);
    } catch (err) {
      console.error('Failed to copy:', err);
    }
  };

  return (
    <div className={cn('relative bg-white rounded-lg border border-gray-200 overflow-hidden', className)}>
      {/* Toolbar */}
      <div className="flex items-center justify-between px-4 py-2 border-b border-gray-200 bg-gray-50">
        <div className="flex items-center gap-2">
          <span className="text-sm font-medium text-gray-700">Mermaid图表</span>
          {isLoading && <Loader2 className="w-4 h-4 animate-spin text-blue-600" />}
        </div>
        <div className="flex items-center gap-1">
          <button
            onClick={handleCopy}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded transition-colors"
            title={isCopied ? '已复制' : '复制代码'}
          >
            {isCopied ? <Check className="w-4 h-4 text-green-600" /> : <Copy className="w-4 h-4" />}
          </button>
          <button
            onClick={handleDownload}
            disabled={!svg}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded transition-colors disabled:opacity-50"
            title="下载SVG"
          >
            <Download className="w-4 h-4" />
          </button>
        </div>
      </div>

      {/* Content */}
      <div className="relative min-h-[300px] p-4">
        {isLoading ? (
          <div className="absolute inset-0 flex items-center justify-center">
            <div className="flex flex-col items-center gap-3">
              <Loader2 className="w-8 h-8 animate-spin text-blue-600" />
              <p className="text-sm text-gray-500">正在渲染图表...</p>
            </div>
          </div>
        ) : error ? (
          <div className="absolute inset-0 flex items-center justify-center p-4">
            <div className="flex flex-col items-center gap-3 text-center">
              <AlertCircle className="w-10 h-10 text-red-500" />
              <div>
                <p className="font-medium text-gray-900">渲染失败</p>
                <p className="text-sm text-gray-500 mt-1">{error}</p>
              </div>
              <div className="mt-2 p-3 bg-gray-50 rounded-lg text-left max-w-lg overflow-auto">
                <pre className="text-xs text-gray-600">{definition}</pre>
              </div>
            </div>
          </div>
        ) : (
          <div
            ref={containerRef}
            className="mermaid-chart flex justify-center"
            dangerouslySetInnerHTML={{ __html: svg }}
          />
        )}
      </div>
    </div>
  );
};

/**
 * 预定义的Mermaid图表模板
 */
export const mermaidTemplates = {
  // 知识图谱模板
  knowledgeGraph: (nodes: Array<{ id: string; label: string }>, edges: Array<{ from: string; to: string; label?: string }>) => {
    const lines = ['graph TD'];
    nodes.forEach(n => lines.push(`  ${n.id}["${n.label}"]`));
    edges.forEach(e => {
      const label = e.label ? `|"${e.label}"|` : '';
      lines.push(`  ${e.from} -->${label} ${e.to}`);
    });
    return lines.join('\n');
  },

  // 思维导图模板
  mindmap: (root: string, branches: Array<{ text: string; subBranches?: string[] }>) => {
    const lines = ['mindmap'];
    lines.push(`  root(("${root}"))`);
    branches.forEach(b => {
      lines.push(`    "${b.text}"`);
      b.subBranches?.forEach(sb => lines.push(`      "${sb}"`));
    });
    return lines.join('\n');
  },

  // 时序图模板
  sequence: (actors: string[], messages: Array<{ from: string; to: string; msg: string }>) => {
    const lines = ['sequenceDiagram'];
    actors.forEach(a => lines.push(`  participant ${a}`));
    messages.forEach(m => lines.push(`  ${m.from}->>${m.to}: ${m.msg}`));
    return lines.join('\n');
  },

  // 甘特图模板
  gantt: (title: string, sections: Array<{ name: string; tasks: Array<{ name: string; start: string; duration: string }> }>) => {
    const lines = ['gantt', `  title ${title}`, '  dateFormat YYYY-MM-DD'];
    sections.forEach(s => {
      lines.push(`  section ${s.name}`);
      s.tasks.forEach(t => lines.push(`  ${t.name} :${t.start}, ${t.duration}`));
    });
    return lines.join('\n');
  },

  // 状态图模板
  stateDiagram: (states: string[], transitions: Array<{ from: string; to: string; event?: string }>) => {
    const lines = ['stateDiagram-v2'];
    transitions.forEach(t => {
      const event = t.event ? ` : ${t.event}` : '';
      lines.push(`  ${t.from} --> ${t.to}${event}`);
    });
    return lines.join('\n');
  },

  // 类图模板
  classDiagram: (classes: Array<{ name: string; attributes?: string[]; methods?: string[] }>, relationships: Array<{ from: string; to: string; type: string }>) => {
    const lines = ['classDiagram'];
    classes.forEach(c => {
      lines.push(`  class ${c.name} {`);
      c.attributes?.forEach(a => lines.push(`    ${a}`));
      c.methods?.forEach(m => lines.push(`    ${m}()`));
      lines.push('  }');
    });
    relationships.forEach(r => {
      lines.push(`  ${r.from} ${r.type} ${r.to}`);
    });
    return lines.join('\n');
  },
};

export default MermaidChart;
