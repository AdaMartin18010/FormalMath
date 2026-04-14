// @ts-nocheck
// ==================== 通用工具函数 ====================

import type { GraphNode, GraphEdge, GraphData, NodeType, EdgeType } from '@types';

/**
 * 生成唯一ID
 */
export function generateId(prefix = ''): string {
  return `${prefix}${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
}

/**
 * 深克隆对象
 */
export function deepClone<T>(obj: T): T {
  if (obj === null || typeof obj !== 'object') return obj;
  if (obj instanceof Date) return new Date(obj) as unknown as T;
  if (Array.isArray(obj)) return obj.map(deepClone) as unknown as T;
  const cloned = {} as T;
  for (const key in obj) {
    if (Object.prototype.hasOwnProperty.call(obj, key)) {
      cloned[key] = deepClone(obj[key]);
    }
  }
  return cloned;
}

/**
 * 防抖函数
 */
export function debounce<T extends (...args: unknown[]) => unknown>(
  fn: T,
  delay: number
): (...args: Parameters<T>) => void {
  let timeoutId: ReturnType<typeof setTimeout>;
  return (...args: Parameters<T>) => {
    clearTimeout(timeoutId);
    timeoutId = setTimeout(() => fn(...args), delay);
  };
}

/**
 * 节流函数
 */
export function throttle<T extends (...args: unknown[]) => unknown>(
  fn: T,
  limit: number
): (...args: Parameters<T>) => void {
  let inThrottle = false;
  return (...args: Parameters<T>) => {
    if (!inThrottle) {
      fn(...args);
      inThrottle = true;
      setTimeout(() => (inThrottle = false), limit);
    }
  };
}

/**
 * 格式化日期
 */
export function formatDate(date: Date | string | number, format = 'YYYY-MM-DD'): string {
  const d = new Date(date);
  const year = d.getFullYear();
  const month = String(d.getMonth() + 1).padStart(2, '0');
  const day = String(d.getDate()).padStart(2, '0');
  const hours = String(d.getHours()).padStart(2, '0');
  const minutes = String(d.getMinutes()).padStart(2, '0');
  const seconds = String(d.getSeconds()).padStart(2, '0');

  return format
    .replace('YYYY', String(year))
    .replace('MM', month)
    .replace('DD', day)
    .replace('HH', hours)
    .replace('mm', minutes)
    .replace('ss', seconds);
}

/**
 * 节点类型颜色映射
 */
export function getNodeTypeColor(type: NodeType): string {
  const colors: Record<NodeType, string> = {
    concept: '#3b82f6',      // blue-500
    theorem: '#10b981',      // emerald-500
    proof: '#8b5cf6',        // violet-500
    example: '#f59e0b',      // amber-500
    application: '#ec4899',  // pink-500
    mathematician: '#6366f1', // indigo-500
  };
  return colors[type] || '#6b7280';
}

/**
 * 边类型样式映射
 */
export function getEdgeTypeStyle(type: EdgeType): { color: string; dashed: boolean } {
  const styles: Record<EdgeType, { color: string; dashed: boolean }> = {
    depends_on: { color: '#6b7280', dashed: false },
    proves: { color: '#10b981', dashed: false },
    uses: { color: '#3b82f6', dashed: false },
    extends: { color: '#8b5cf6', dashed: true },
    contradicts: { color: '#ef4444', dashed: true },
    influences: { color: '#f59e0b', dashed: true },
  };
  return styles[type] || { color: '#6b7280', dashed: false };
}

/**
 * 计算图的统计信息
 */
export function calculateGraphStats(data: GraphData) {
  const { nodes, edges } = data;
  const nodeCount = nodes.length;
  const edgeCount = edges.length;
  
  // 计算度数
  const degrees = new Map<string, number>();
  nodes.forEach(n => degrees.set(n.id, 0));
  edges.forEach(e => {
    degrees.set(e.source, (degrees.get(e.source) || 0) + 1);
    degrees.set(e.target, (degrees.get(e.target) || 0) + 1);
  });

  const avgDegree = nodeCount > 0 
    ? Array.from(degrees.values()).reduce((a, b) => a + b, 0) / nodeCount 
    : 0;

  // 密度
  const maxEdges = nodeCount * (nodeCount - 1) / 2;
  const density = maxEdges > 0 ? edgeCount / maxEdges : 0;

  return {
    nodeCount,
    edgeCount,
    avgDegree: Math.round(avgDegree * 100) / 100,
    density: Math.round(density * 100) / 100,
    maxDegree: Math.max(...degrees.values(), 0),
    isolatedNodes: nodes.filter(n => (degrees.get(n.id) || 0) === 0).length,
  };
}

/**
 * 查找连通分量
 */
export function findConnectedComponents(data: GraphData): string[][] {
  const adj = new Map<string, string[]>();
  
  data.nodes.forEach(n => adj.set(n.id, []));
  data.edges.forEach(e => {
    adj.get(e.source)?.push(e.target);
    adj.get(e.target)?.push(e.source);
  });

  const visited = new Set<string>();
  const components: string[][] = [];

  const dfs = (nodeId: string, component: string[]) => {
    visited.add(nodeId);
    component.push(nodeId);
    adj.get(nodeId)?.forEach(neighbor => {
      if (!visited.has(neighbor)) {
        dfs(neighbor, component);
      }
    });
  };

  data.nodes.forEach(n => {
    if (!visited.has(n.id)) {
      const component: string[] = [];
      dfs(n.id, component);
      components.push(component);
    }
  });

  return components;
}

/**
 * 查找最短路径 (BFS)
 */
export function findShortestPath(
  data: GraphData,
  startId: string,
  endId: string
): string[] | null {
  const adj = new Map<string, string[]>();
  
  data.nodes.forEach(n => adj.set(n.id, []));
  data.edges.forEach(e => {
    adj.get(e.source)?.push(e.target);
    if (!e.directed) {
      adj.get(e.target)?.push(e.source);
    }
  });

  const queue: Array<{ node: string; path: string[] }> = [{ node: startId, path: [startId] }];
  const visited = new Set<string>();

  while (queue.length > 0) {
    const { node, path } = queue.shift()!;
    
    if (node === endId) return path;
    
    if (!visited.has(node)) {
      visited.add(node);
      adj.get(node)?.forEach(neighbor => {
        if (!visited.has(neighbor)) {
          queue.push({ node: neighbor, path: [...path, neighbor] });
        }
      });
    }
  }

  return null;
}

/**
 * 计算节点重要性 (度中心性)
 */
export function calculateNodeCentrality(data: GraphData): Map<string, number> {
  const centrality = new Map<string, number>();
  
  data.nodes.forEach(n => centrality.set(n.id, 0));
  
  data.edges.forEach(e => {
    centrality.set(e.source, (centrality.get(e.source) || 0) + 1);
    centrality.set(e.target, (centrality.get(e.target) || 0) + 1);
  });

  return centrality;
}

/**
 * 过滤图数据
 */
export function filterGraphData(
  data: GraphData,
  nodeFilter?: (node: GraphNode) => boolean,
  edgeFilter?: (edge: GraphEdge) => boolean
): GraphData {
  const filteredNodes = nodeFilter ? data.nodes.filter(nodeFilter) : data.nodes;
  const nodeIds = new Set(filteredNodes.map(n => n.id));
  
  const filteredEdges = edgeFilter 
    ? data.edges.filter(e => nodeIds.has(e.source) && nodeIds.has(e.target) && edgeFilter(e))
    : data.edges.filter(e => nodeIds.has(e.source) && nodeIds.has(e.target));

  return { nodes: filteredNodes, edges: filteredEdges };
}

/**
 * 合并多个图数据
 */
export function mergeGraphData(datasets: GraphData[]): GraphData {
  const nodeMap = new Map<string, GraphNode>();
  const edgeMap = new Map<string, GraphEdge>();

  datasets.forEach(data => {
    data.nodes.forEach(n => nodeMap.set(n.id, n));
    data.edges.forEach(e => edgeMap.set(e.id, e));
  });

  return {
    nodes: Array.from(nodeMap.values()),
    edges: Array.from(edgeMap.values()),
  };
}

/**
 * 下载JSON文件
 */
export function downloadJSON(data: unknown, filename: string) {
  const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

/**
 * 解析查询字符串
 */
export function parseQueryString(query: string): Record<string, string> {
  const params = new URLSearchParams(query);
  const result: Record<string, string> = {};
  params.forEach((value, key) => {
    result[key] = value;
  });
  return result;
}

/**
 * 构建查询字符串
 */
export function buildQueryString(params: Record<string, string | number | boolean>): string {
  const searchParams = new URLSearchParams();
  Object.entries(params).forEach(([key, value]) => {
    if (value !== undefined && value !== null && value !== '') {
      searchParams.set(key, String(value));
    }
  });
  const query = searchParams.toString();
  return query ? `?${query}` : '';
}

/**
 * 截断文本
 */
export function truncateText(text: string, maxLength: number, suffix = '...'): string {
  if (text.length <= maxLength) return text;
  return text.substring(0, maxLength - suffix.length) + suffix;
}

/**
 * 随机颜色生成
 */
export function generateRandomColor(): string {
  const hue = Math.floor(Math.random() * 360);
  return `hsl(${hue}, 70%, 50%)`;
}

/**
 * 颜色亮度调整
 */
export function adjustBrightness(color: string, amount: number): string {
  const hex = color.replace('#', '');
  const r = Math.max(0, Math.min(255, parseInt(hex.substring(0, 2), 16) + amount));
  const g = Math.max(0, Math.min(255, parseInt(hex.substring(2, 4), 16) + amount));
  const b = Math.max(0, Math.min(255, parseInt(hex.substring(4, 6), 16) + amount));
  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}
