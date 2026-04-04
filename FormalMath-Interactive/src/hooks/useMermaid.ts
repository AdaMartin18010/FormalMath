// ==================== Mermaid图表Hook ====================

import { useState, useCallback, useEffect, useRef } from 'react';
import mermaid from 'mermaid';

interface UseMermaidOptions {
  theme?: 'default' | 'dark' | 'forest' | 'neutral';
  securityLevel?: 'strict' | 'loose' | 'antiscript';
  startOnLoad?: boolean;
}

interface UseMermaidReturn {
  svg: string;
  error: string | null;
  isLoading: boolean;
  render: (definition: string, elementId?: string) => Promise<void>;
  downloadSVG: () => void;
}

// 初始化Mermaid配置
const defaultConfig: UseMermaidOptions = {
  theme: 'default',
  securityLevel: 'loose',
  startOnLoad: false,
};

let mermaidInitialized = false;

function initMermaid(options: UseMermaidOptions = {}) {
  if (mermaidInitialized) return;
  
  mermaid.initialize({
    startOnLoad: options.startOnLoad ?? defaultConfig.startOnLoad,
    theme: options.theme ?? defaultConfig.theme,
    securityLevel: options.securityLevel ?? defaultConfig.securityLevel,
    flowchart: {
      useMaxWidth: true,
      htmlLabels: true,
      curve: 'basis',
    },
    sequence: {
      useMaxWidth: true,
    },
    gantt: {
      useMaxWidth: true,
    },
  });
  
  mermaidInitialized = true;
}

export function useMermaid(options: UseMermaidOptions = {}): UseMermaidReturn {
  const [svg, setSvg] = useState<string>('');
  const [error, setError] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState<boolean>(false);
  const [currentDefinition, setCurrentDefinition] = useState<string>('');
  const containerRef = useRef<HTMLDivElement | null>(null);

  // 初始化
  useEffect(() => {
    initMermaid(options);
  }, []);

  // 渲染图表
  const render = useCallback(async (definition: string, elementId?: string) => {
    setIsLoading(true);
    setError(null);
    setCurrentDefinition(definition);

    try {
      // 使用随机ID确保唯一性
      const id = elementId || `mermaid-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
      
      // 验证语法
      const valid = await mermaid.parse(definition);
      if (!valid) {
        throw new Error('Invalid Mermaid syntax');
      }

      // 渲染
      const { svg: renderedSvg } = await mermaid.render(id, definition);
      setSvg(renderedSvg);
    } catch (err) {
      const errorMessage = err instanceof Error ? err.message : 'Failed to render Mermaid diagram';
      setError(errorMessage);
      setSvg('');
    } finally {
      setIsLoading(false);
    }
  }, []);

  // 下载SVG
  const downloadSVG = useCallback(() => {
    if (!svg) return;

    const blob = new Blob([svg], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `mermaid-diagram-${Date.now()}.svg`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);
  }, [svg]);

  return {
    svg,
    error,
    isLoading,
    render,
    downloadSVG,
  };
}

/**
 * 生成知识图谱的Mermaid定义
 */
export function generateGraphMermaid(
  nodes: Array<{ id: string; label: string; type: string }>,
  edges: Array<{ source: string; target: string; label?: string }>
): string {
  const lines = ['graph TD'];
  
  // 添加节点
  nodes.forEach(node => {
    const safeLabel = node.label.replace(/["[\](){}]/g, '');
    lines.push(`  ${node.id}["${safeLabel}"]`);
  });
  
  // 添加边
  edges.forEach(edge => {
    const line = edge.label 
      ? `  ${edge.source} -->|"${edge.label}"| ${edge.target}`
      : `  ${edge.source} --> ${edge.target}`;
    lines.push(line);
  });
  
  return lines.join('\n');
}

/**
 * 生成思维导图的Mermaid定义
 */
export function generateMindmapMermaid(
  root: { text: string; children?: Array<{ text: string; children?: Array<{ text: string }> }> }
): string {
  const lines = ['mindmap'];
  lines.push(`  root(("${root.text}"))`);
  
  if (root.children) {
    root.children.forEach(child => {
      lines.push(`    "${child.text}"`);
      if (child.children) {
        child.children.forEach(grandchild => {
          lines.push(`      "${grandchild.text}"`);
        });
      }
    });
  }
  
  return lines.join('\n');
}

/**
 * 生成时序图的Mermaid定义
 */
export function generateSequenceMermaid(
  actors: string[],
  messages: Array<{ from: string; to: string; message: string }>
): string {
  const lines = ['sequenceDiagram'];
  
  // 添加参与者
  actors.forEach(actor => {
    lines.push(`  participant ${actor}`);
  });
  
  // 添加消息
  messages.forEach(msg => {
    lines.push(`  ${msg.from}->>${msg.to}: ${msg.message}`);
  });
  
  return lines.join('\n');
}

/**
 * 生成甘特图的Mermaid定义
 */
export function generateGanttMermaid(
  title: string,
  sections: Array<{
    name: string;
    tasks: Array<{ name: string; start: string; duration: string; status?: 'done' | 'active' | 'crit' }>;
  }>
): string {
  const lines = ['gantt'];
  lines.push(`  title ${title}`);
  lines.push('  dateFormat YYYY-MM-DD');
  
  sections.forEach(section => {
    lines.push(`  section ${section.name}`);
    section.tasks.forEach(task => {
      const status = task.status ? `${task.status}, ` : '';
      lines.push(`  ${task.name} :${status}${task.start}, ${task.duration}`);
    });
  });
  
  return lines.join('\n');
}
