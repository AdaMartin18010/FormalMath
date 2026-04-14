/**
 * FormalMath 可视化组件性能测试工具
 * 用于测量和报告组件性能指标
 */

// ============================================
// 类型定义
// ============================================

export interface PerformanceTestResult {
  component: string;
  nodeCount: number;
  edgeCount: number;
  renderTime: number;
  fps: number;
  memoryBefore: number;
  memoryAfter: number;
  memoryDelta: number;
  timestamp: number;
}

export interface PerformanceTestSuite {
  name: string;
  results: PerformanceTestResult[];
  averageRenderTime: number;
  averageFPS: number;
  averageMemoryDelta: number;
}

export interface BenchmarkConfig {
  nodeCounts: number[];
  iterations: number;
  warmupIterations: number;
}

// ============================================
// 性能测量工具
// ============================================

export class PerformanceTester {
  private frameCount = 0;
  private lastTime = 0;
  private rafId: number | null = null;

  /**
   * 测量渲染时间
   */
  async measureRenderTime(
    renderFn: () => void | Promise<void>,
    iterations = 10
  ): Promise<number> {
    // 预热
    for (let i = 0; i < 3; i++) {
      await renderFn();
    }

    // 正式测量
    const times: number[] = [];
    
    for (let i = 0; i < iterations; i++) {
      const start = performance.now();
      await renderFn();
      const end = performance.now();
      times.push(end - start);
    }

    // 去除异常值后取平均
    const sorted = [...times].sort((a, b) => a - b);
    const validTimes = sorted.slice(1, -1); // 去掉最高和最低
    return validTimes.reduce((a, b) => a + b, 0) / validTimes.length;
  }

  /**
   * 测量 FPS
   */
  measureFPS(duration = 1000): Promise<number> {
    return new Promise((resolve) => {
      this.frameCount = 0;
      this.lastTime = performance.now();

      const measure = () => {
        this.frameCount++;
        const currentTime = performance.now();
        const elapsed = currentTime - this.lastTime;

        if (elapsed >= duration) {
          const fps = Math.round((this.frameCount * 1000) / elapsed);
          resolve(fps);
        } else {
          this.rafId = requestAnimationFrame(measure);
        }
      };

      this.rafId = requestAnimationFrame(measure);
    });
  }

  /**
   * 测量内存使用
   */
  measureMemory(): number {
    if ('memory' in performance) {
      return (performance as any).memory.usedJSHeapSize;
    }
    return 0;
  }

  /**
   * 运行完整性能测试
   */
  async runBenchmark(
    componentName: string,
    renderFn: (nodeCount: number) => void | Promise<void>,
    config: BenchmarkConfig
  ): Promise<PerformanceTestSuite> {
    const results: PerformanceTestResult[] = [];

    for (const nodeCount of config.nodeCounts) {
      console.log(`[Benchmark] Testing ${componentName} with ${nodeCount} nodes...`);

      const memoryBefore = this.measureMemory();
      
      // 渲染测试
      const renderTime = await this.measureRenderTime(
        () => renderFn(nodeCount),
        config.iterations
      );

      // FPS 测试
      const fps = await this.measureFPS(2000);

      const memoryAfter = this.measureMemory();
      const memoryDelta = memoryAfter - memoryBefore;

      const result: PerformanceTestResult = {
        component: componentName,
        nodeCount,
        edgeCount: Math.floor(nodeCount * 1.5), // 假设边数为节点数的 1.5 倍
        renderTime,
        fps,
        memoryBefore,
        memoryAfter,
        memoryDelta,
        timestamp: Date.now(),
      };

      results.push(result);
      console.log(`[Benchmark] Result:`, result);

      // GC 建议
      if ((globalThis as any).gc) {
        (globalThis as any).gc();
      }
    }

    return {
      name: componentName,
      results,
      averageRenderTime: results.reduce((a, r) => a + r.renderTime, 0) / results.length,
      averageFPS: results.reduce((a, r) => a + r.fps, 0) / results.length,
      averageMemoryDelta: results.reduce((a, r) => a + r.memoryDelta, 0) / results.length,
    };
  }

  /**
   * 生成测试报告
   */
  generateReport(suite: PerformanceTestSuite): string {
    const lines: string[] = [
      `# ${suite.name} 性能测试报告`,
      '',
      `测试时间: ${new Date().toLocaleString()}`,
      '',
      '## 汇总',
      '',
      '| 指标 | 平均值 |',
      '|------|--------|',
      `| 渲染时间 | ${suite.averageRenderTime.toFixed(2)}ms |`,
      `| FPS | ${suite.averageFPS.toFixed(0)} |`,
      `| 内存变化 | ${(suite.averageMemoryDelta / 1024 / 1024).toFixed(2)}MB |`,
      '',
      '## 详细结果',
      '',
      '| 节点数 | 边数 | 渲染时间(ms) | FPS | 内存变化(MB) |',
      '|--------|------|--------------|-----|--------------|',
    ];

    for (const result of suite.results) {
      lines.push(
        `| ${result.nodeCount} | ${result.edgeCount} | ${result.renderTime.toFixed(2)} | ${result.fps} | ${(result.memoryDelta / 1024 / 1024).toFixed(2)} |`
      );
    }

    return lines.join('\n');
  }

  /**
   * 清理资源
   */
  dispose(): void {
    if (this.rafId !== null) {
      cancelAnimationFrame(this.rafId);
    }
  }
}

// ============================================
// 辅助函数
// ============================================

/**
 * 生成测试数据
 */
export function generateTestData(nodeCount: number): { nodes: any[]; edges: any[] } {
  const types = ['concept', 'theorem', 'proof', 'example', 'application'];
  const nodes = Array.from({ length: nodeCount }, (_, i) => ({
    id: `node-${i}`,
    label: `Node ${i}`,
    type: types[Math.floor(Math.random() * types.length)],
    radius: 5 + Math.random() * 15,
    x: Math.random() * 800,
    y: Math.random() * 600,
    importance: Math.random(),
  }));

  const edges = [];
  const edgeCount = Math.floor(nodeCount * 1.5);
  
  for (let i = 0; i < edgeCount; i++) {
    const source = Math.floor(Math.random() * nodeCount);
    let target = Math.floor(Math.random() * nodeCount);
    while (target === source) {
      target = Math.floor(Math.random() * nodeCount);
    }
    
    edges.push({
      id: `edge-${i}`,
      source: `node-${source}`,
      target: `node-${target}`,
      weight: Math.random() * 5,
      type: Math.random() > 0.5 ? 'solid' : 'dashed',
    });
  }

  return { nodes, edges };
}

/**
 * 性能等级评估
 */
export function evaluatePerformance(result: PerformanceTestResult): {
  grade: 'A' | 'B' | 'C' | 'D' | 'F';
  description: string;
} {
  if (result.fps >= 55 && result.renderTime < 16) {
    return { grade: 'A', description: '优秀 - 流畅的 60fps 体验' };
  }
  if (result.fps >= 45 && result.renderTime < 33) {
    return { grade: 'B', description: '良好 - 基本流畅' };
  }
  if (result.fps >= 30 && result.renderTime < 50) {
    return { grade: 'C', description: '可接受 - 略有卡顿' };
  }
  if (result.fps >= 15 && result.renderTime < 100) {
    return { grade: 'D', description: '较差 - 明显卡顿' };
  }
  return { grade: 'F', description: '不可接受 - 需要优化' };
}

/**
 * 对比测试
 */
export function compareResults(
  baseline: PerformanceTestResult,
  current: PerformanceTestResult
): {
  renderTimeDiff: number;
  fpsDiff: number;
  memoryDiff: number;
  improved: boolean;
} {
  const renderTimeDiff = ((current.renderTime - baseline.renderTime) / baseline.renderTime) * 100;
  const fpsDiff = ((current.fps - baseline.fps) / baseline.fps) * 100;
  const memoryDiff = ((current.memoryDelta - baseline.memoryDelta) / baseline.memoryDelta) * 100;

  return {
    renderTimeDiff,
    fpsDiff,
    memoryDiff,
    improved: renderTimeDiff < 0 && fpsDiff > 0,
  };
}

// ============================================
// 默认导出
// ============================================

export default PerformanceTester;
