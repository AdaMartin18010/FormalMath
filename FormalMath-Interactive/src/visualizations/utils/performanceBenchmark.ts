/**
 * 知识图谱可视化性能测试工具
 * Performance Benchmark Utilities for Graph Visualization
 */

import type { GraphData, GraphNode, GraphEdge } from '../types';

// ============================================
// 类型定义
// ============================================

export interface BenchmarkConfig {
  nodeCounts: number[];
  edgeRatio: number; // 边数/节点数 比例
  iterations: number;
  warmupIterations: number;
}

export interface BenchmarkResult {
  nodeCount: number;
  edgeCount: number;
  initializationTime: number;
  firstRenderTime: number;
  averageFrameTime: number;
  fps: number;
  memoryUsage: number;
  success: boolean;
  error?: string;
}

export interface PerformanceReport {
  timestamp: string;
  userAgent: string;
  results: BenchmarkResult[];
  summary: {
    maxNodes: number;
    recommendedMaxNodes: number;
    averageFPS: number;
    bottleneck: 'cpu' | 'memory' | 'gpu' | 'unknown';
  };
}

// ============================================
// 测试数据生成
// ============================================

const NODE_TYPES = ['concept', 'theorem', 'proof', 'example', 'application', 'mathematician'] as const;
const EDGE_TYPES = ['depends_on', 'proves', 'uses', 'extends', 'contradicts', 'influences'] as const;

export function generateTestData(nodeCount: number, edgeRatio: number): GraphData {
  const nodes: GraphNode[] = [];
  const edges: GraphEdge[] = [];
  
  // 生成节点
  for (let i = 0; i < nodeCount; i++) {
    const type = NODE_TYPES[Math.floor(Math.random() * NODE_TYPES.length)];
    nodes.push({
      id: `node-${i}`,
      label: `节点 ${i}`,
      type: type as any,
      data: { status: 'verified' },
      description: `这是节点 ${i} 的描述信息`,
      importance: Math.random(),
      radius: 15 + Math.random() * 15,
    });
  }
  
  // 生成边 (使用小世界网络模型)
  const edgeCount = Math.floor(nodeCount * edgeRatio);
  for (let i = 0; i < edgeCount; i++) {
    const source = `node-${Math.floor(Math.random() * nodeCount)}`;
    let target = `node-${Math.floor(Math.random() * nodeCount)}`;
    
    // 避免自环
    while (target === source) {
      target = `node-${Math.floor(Math.random() * nodeCount)}`;
    }
    
    const type = EDGE_TYPES[Math.floor(Math.random() * EDGE_TYPES.length)];
    edges.push({
      id: `edge-${i}`,
      source,
      target,
      type: type as any,
      weight: 0.5 + Math.random() * 0.5,
    });
  }
  
  return { nodes, edges };
}

// ============================================
// 性能测量工具
// ============================================

export class PerformanceTimer {
  private marks: Map<string, number> = new Map();
  private measures: Map<string, number> = new Map();
  
  mark(name: string): void {
    this.marks.set(name, performance.now());
  }
  
  measure(name: string, startMark: string, endMark?: string): number {
    const start = this.marks.get(startMark);
    const end = endMark ? this.marks.get(endMark) : performance.now();
    
    if (start === undefined) {
      throw new Error(`Mark "${startMark}" not found`);
    }
    
    const duration = (end || performance.now()) - start;
    this.measures.set(name, duration);
    return duration;
  }
  
  getMeasure(name: string): number | undefined {
    return this.measures.get(name);
  }
  
  clear(): void {
    this.marks.clear();
    this.measures.clear();
  }
}

// ============================================
// FPS 监控器
// ============================================

export class FPSMonitor {
  private frameCount = 0;
  private lastTime = performance.now();
  private currentFPS = 60;
  private rafId: number | null = null;
  private callbacks: ((fps: number) => void)[] = [];
  
  start(): void {
    this.rafId = requestAnimationFrame(() => this.measure());
  }
  
  stop(): void {
    if (this.rafId !== null) {
      cancelAnimationFrame(this.rafId);
      this.rafId = null;
    }
  }
  
  private measure(): void {
    this.frameCount++;
    const currentTime = performance.now();
    const delta = currentTime - this.lastTime;
    
    if (delta >= 1000) {
      this.currentFPS = Math.round((this.frameCount * 1000) / delta);
      this.frameCount = 0;
      this.lastTime = currentTime;
      this.callbacks.forEach(cb => cb(this.currentFPS));
    }
    
    this.rafId = requestAnimationFrame(() => this.measure());
  }
  
  getFPS(): number {
    return this.currentFPS;
  }
  
  onUpdate(callback: (fps: number) => void): () => void {
    this.callbacks.push(callback);
    return () => {
      const index = this.callbacks.indexOf(callback);
      if (index > -1) this.callbacks.splice(index, 1);
    };
  }
}

// ============================================
// 内存监控器
// ============================================

export function getMemoryUsage(): number {
  if ('memory' in performance) {
    return (performance as any).memory.usedJSHeapSize;
  }
  return 0;
}

export function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 B';
  const k = 1024;
  const sizes = ['B', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];
}

// ============================================
// 基准测试运行器
// ============================================

export async function runBenchmark(
  config: BenchmarkConfig,
  renderFn: (data: GraphData) => Promise<{ destroy: () => void }>
): Promise<PerformanceReport> {
  const results: BenchmarkResult[] = [];
  const timer = new PerformanceTimer();
  const fpsMonitor = new FPSMonitor();
  
  for (const nodeCount of config.nodeCounts) {
    const edgeCount = Math.floor(nodeCount * config.edgeRatio);
    
    try {
      // 生成测试数据
      timer.mark('data-gen-start');
      const data = generateTestData(nodeCount, config.edgeRatio);
      const dataGenTime = timer.measure('data-generation', 'data-gen-start');
      
      // 预热
      for (let i = 0; i < config.warmupIterations; i++) {
        const warmupData = generateTestData(Math.min(100, nodeCount), config.edgeRatio);
        const warmupResult = await renderFn(warmupData);
        warmupResult.destroy();
      }
      
      // 开始测试
      timer.mark('init-start');
      fpsMonitor.start();
      
      const frameTimes: number[] = [];
      const _startFrame = performance.now();
      
      const result = await renderFn(data);
      
      const initTime = timer.measure('initialization', 'init-start');
      
      // 测量帧时间
      const measureFrames = () => new Promise<void>(resolve => {
        let frameCount = 0;
        const measure = () => {
          const frameStart = performance.now();
          requestAnimationFrame(() => {
            const frameEnd = performance.now();
            frameTimes.push(frameEnd - frameStart);
            frameCount++;
            
            if (frameCount < 60) {
              measure();
            } else {
              resolve();
            }
          });
        };
        measure();
      });
      
      await measureFrames();
      fpsMonitor.stop();
      
      const avgFrameTime = frameTimes.reduce((a, b) => a + b, 0) / frameTimes.length;
      
      // 清理
      result.destroy();
      
      results.push({
        nodeCount,
        edgeCount,
        initializationTime: initTime,
        firstRenderTime: dataGenTime + initTime,
        averageFrameTime: avgFrameTime,
        fps: Math.round(1000 / avgFrameTime),
        memoryUsage: getMemoryUsage(),
        success: true,
      });
      
      // 如果 FPS 太低,停止测试
      if (1000 / avgFrameTime < 10) {
        break;
      }
      
    } catch (error) {
      results.push({
        nodeCount,
        edgeCount,
        initializationTime: 0,
        firstRenderTime: 0,
        averageFrameTime: 0,
        fps: 0,
        memoryUsage: 0,
        success: false,
        error: error instanceof Error ? error.message : 'Unknown error',
      });
      break;
    }
  }
  
  // 生成报告
  const successfulResults = results.filter(r => r.success);
  const averageFPS = successfulResults.length > 0
    ? successfulResults.reduce((a, r) => a + r.fps, 0) / successfulResults.length
    : 0;
  
  const maxNodes = successfulResults.length > 0
    ? successfulResults[successfulResults.length - 1].nodeCount
    : 0;
  
  // 推荐的最大节点数 (FPS >= 30)
  const recommendedMaxNodes = successfulResults
    .filter(r => r.fps >= 30)
    .pop()?.nodeCount || 0;
  
  // 确定瓶颈
  let bottleneck: 'cpu' | 'memory' | 'gpu' | 'unknown' = 'unknown';
  const lastResult = successfulResults[successfulResults.length - 1];
  if (lastResult) {
    if (lastResult.averageFrameTime > 50) {
      bottleneck = 'cpu';
    } else if (lastResult.memoryUsage > 500 * 1024 * 1024) { // 500MB
      bottleneck = 'memory';
    } else if (lastResult.fps < 30 && lastResult.averageFrameTime < 33) {
      bottleneck = 'gpu';
    }
  }
  
  return {
    timestamp: new Date().toISOString(),
    userAgent: navigator.userAgent,
    results,
    summary: {
      maxNodes,
      recommendedMaxNodes,
      averageFPS,
      bottleneck,
    },
  };
}

// ============================================
// 性能优化建议
// ============================================

export function generateOptimizationSuggestions(report: PerformanceReport): string[] {
  const suggestions: string[] = [];
  const { results, summary } = report;
  
  // 检查FPS
  if (summary.averageFPS < 30) {
    suggestions.push('平均帧率较低，建议启用虚拟化渲染');
  }
  
  // 检查内存使用
  const highMemoryResult = results.find(r => r.memoryUsage > 500 * 1024 * 1024);
  if (highMemoryResult) {
    suggestions.push(`在 ${highMemoryResult.nodeCount} 节点时内存使用超过500MB，建议使用数据分页加载`);
  }
  
  // 检查初始化时间
  const slowInitResult = results.find(r => r.initializationTime > 1000);
  if (slowInitResult) {
    suggestions.push(`在 ${slowInitResult.nodeCount} 节点时初始化时间超过1秒，建议使用Web Worker预处理数据`);
  }
  
  // 检查瓶颈
  switch (summary.bottleneck) {
    case 'cpu':
      suggestions.push('CPU 是主要瓶颈，建议减少物理模拟计算量');
      break;
    case 'memory':
      suggestions.push('内存是主要瓶颈，建议启用节点池复用');
      break;
    case 'gpu':
      suggestions.push('GPU 是主要瓶颈，建议简化渲染效果');
      break;
  }
  
  // 通用建议
  if (summary.maxNodes < 1000) {
    suggestions.push('建议对大规模图数据使用聚合视图');
  }
  
  if (results.length > 0) {
    const lastResult = results[results.length - 1];
    if (lastResult.success && lastResult.fps >= 60) {
      suggestions.push('性能良好，可以尝试增加更多视觉效果');
    }
  }
  
  return suggestions;
}

// ============================================
// 导出报告
// ============================================

export function exportBenchmarkReport(report: PerformanceReport): void {
  const blob = new Blob([JSON.stringify(report, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = `benchmark-report-${Date.now()}.json`;
  link.click();
  URL.revokeObjectURL(url);
}

// ============================================
// 默认配置
// ============================================

export const DEFAULT_BENCHMARK_CONFIG: BenchmarkConfig = {
  nodeCounts: [100, 200, 500, 1000, 2000, 5000],
  edgeRatio: 1.5,
  iterations: 5,
  warmupIterations: 2,
};

// ============================================
// 导出
// ============================================

export default {
  generateTestData,
  PerformanceTimer,
  FPSMonitor,
  getMemoryUsage,
  formatBytes,
  runBenchmark,
  generateOptimizationSuggestions,
  exportBenchmarkReport,
  DEFAULT_BENCHMARK_CONFIG,
};
