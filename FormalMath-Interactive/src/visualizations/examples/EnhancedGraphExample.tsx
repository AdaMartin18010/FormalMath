/**
 * EnhancedD3Graph 使用示例
 * 展示增强版图谱可视化组件的功能
 */

import React, { useState, useCallback, useMemo } from 'react';
import { EnhancedD3Graph } from '../EnhancedD3Graph';
import type { GraphNode, GraphEdge } from '../../types';

// ============================================
// 示例数据生成
// ============================================

const NODE_TYPES = ['concept', 'theorem', 'proof', 'example', 'application', 'mathematician', 'axiom', 'lemma'];
const DOMAINS = ['代数', '几何', '分析', '拓扑', '数论', '概率'];

function generateSampleData(nodeCount: number = 100): { nodes: GraphNode[]; edges: GraphEdge[] } {
  const nodes: GraphNode[] = [];
  const edges: GraphEdge[] = [];
  
  // 生成节点
  for (let i = 0; i < nodeCount; i++) {
    const type = NODE_TYPES[Math.floor(Math.random() * NODE_TYPES.length)];
    const domain = DOMAINS[Math.floor(Math.random() * DOMAINS.length)];
    const importance = Math.random();
    
    nodes.push({
      id: `node-${i}`,
      label: `${domain}${type === 'mathematician' ? '数学家' : '概念'} ${i + 1}`,
      type: type as any,
      status: 'verified',
      description: `这是${domain}领域的重要${type}，具有${(importance * 100).toFixed(0)}%的重要性。`,
      importance,
      radius: 15 + importance * 20,
    });
  }
  
  // 生成边 (使用层次化连接)
  const edgeCount = Math.floor(nodeCount * 1.5);
  for (let i = 0; i < edgeCount; i++) {
    const sourceIndex = Math.floor(Math.random() * nodeCount);
    // 优先连接到编号较小的节点 (模拟依赖关系)
    const targetIndex = Math.floor(Math.random() * Math.max(1, sourceIndex));
    
    if (sourceIndex !== targetIndex) {
      const edgeTypes = ['depends_on', 'proves', 'uses', 'extends'];
      const type = edgeTypes[Math.floor(Math.random() * edgeTypes.length)];
      
      edges.push({
        id: `edge-${i}`,
        source: `node-${sourceIndex}`,
        target: `node-${targetIndex}`,
        type: type as any,
        weight: 0.3 + Math.random() * 0.7,
      });
    }
  }
  
  return { nodes, edges };
}

// ============================================
// 示例组件
// ============================================

export const EnhancedGraphExample: React.FC = () => {
  const [nodeCount, setNodeCount] = useState(100);
  const [theme, setTheme] = useState<'light' | 'dark'>('light');
  const [selectedNodes, setSelectedNodes] = useState<string[]>([]);
  const [fps, setFps] = useState(60);
  
  // 生成数据
  const data = useMemo(() => generateSampleData(nodeCount), [nodeCount]);
  
  // 节点点击处理
  const handleNodeClick = useCallback((node: GraphNode) => {
    setSelectedNodes(prev => {
      if (prev.includes(node.id)) {
        return prev.filter(id => id !== node.id);
      }
      return [...prev, node.id];
    });
  }, []);
  
  return (
    <div className="p-6 space-y-6">
      {/* 标题 */}
      <div className="flex items-center justify-between">
        <div>
          <h1 className="text-2xl font-bold text-gray-900">增强版知识图谱可视化</h1>
          <p className="text-gray-600 mt-1">EnhancedD3Graph Component Demo</p>
        </div>
        <div className="flex items-center gap-4">
          <div className="flex items-center gap-2 text-sm">
            <span className="text-gray-600">FPS:</span>
            <span className={`font-mono font-bold ${fps >= 50 ? 'text-green-600' : fps >= 30 ? 'text-yellow-600' : 'text-red-600'}`}>
              {fps}
            </span>
          </div>
          <button
            onClick={() => setTheme(t => t === 'light' ? 'dark' : 'light')}
            className="px-4 py-2 bg-gray-100 hover:bg-gray-200 rounded-lg text-sm transition-colors"
          >
            {theme === 'light' ? '🌙 深色' : '☀️ 浅色'}
          </button>
        </div>
      </div>
      
      {/* 控制面板 */}
      <div className="bg-gray-50 rounded-lg p-4 space-y-4">
        <div className="flex flex-wrap items-center gap-4">
          {/* 节点数量控制 */}
          <div className="flex items-center gap-3">
            <label className="text-sm font-medium text-gray-700">节点数量:</label>
            <input
              type="range"
              min="50"
              max="2000"
              step="50"
              value={nodeCount}
              onChange={(e) => setNodeCount(Number(e.target.value))}
              className="w-48 h-2 bg-gray-200 rounded-lg appearance-none cursor-pointer accent-blue-500"
            />
            <span className="text-sm font-mono bg-white px-2 py-1 rounded border">{nodeCount}</span>
          </div>
          
          {/* 统计数据 */}
          <div className="flex items-center gap-4 text-sm text-gray-600">
            <span>节点: <strong className="text-gray-900">{data.nodes.length}</strong></span>
            <span>连接: <strong className="text-gray-900">{data.edges.length}</strong></span>
            <span>选中: <strong className="text-blue-600">{selectedNodes.length}</strong></span>
          </div>
          
          {/* 操作按钮 */}
          <div className="flex gap-2 ml-auto">
            <button
              onClick={() => setSelectedNodes([])}
              className="px-3 py-1.5 text-sm bg-white border border-gray-300 rounded-lg hover:bg-gray-50 transition-colors"
            >
              清空选择
            </button>
          </div>
        </div>
        
        {/* 功能说明 */}
        <div className="text-xs text-gray-500 flex flex-wrap gap-4">
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 bg-blue-500 rounded-full"></span>
            拖拽节点调整布局
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 bg-green-500 rounded-full"></span>
            滚轮缩放
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 bg-purple-500 rounded-full"></span>
            点击选择节点
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 bg-orange-500 rounded-full"></span>
            使用筛选面板搜索
          </span>
          <span className="flex items-center gap-1">
            <span className="w-2 h-2 bg-pink-500 rounded-full"></span>
            调节力导向参数
          </span>
        </div>
      </div>
      
      {/* 图谱可视化 */}
      <div className="border border-gray-200 rounded-lg overflow-hidden" style={{ height: '600px' }}>
        <EnhancedD3Graph
          data={data}
          width={1200}
          height={600}
          theme={theme}
          config={{
            showLabels: true,
            labelSize: 12,
            nodeSize: 20,
            edgeWidth: 2,
          }}
          selectedNodes={selectedNodes}
          onNodeClick={handleNodeClick}
          enableVirtualization={true}
          maxVisibleNodes={1000}
        />
      </div>
      
      {/* 使用说明 */}
      <div className="grid grid-cols-2 gap-6 text-sm">
        <div className="bg-blue-50 rounded-lg p-4">
          <h3 className="font-semibold text-blue-900 mb-2">性能优化特性</h3>
          <ul className="space-y-1 text-blue-800">
            <li>✓ 虚拟化渲染 (支持5000+节点)</li>
            <li>✓ RAF 节流渲染</li>
            <li>✓ 内存优化</li>
            <li>✓ FPS 监控</li>
            <li>✓ 自适应质量降级</li>
          </ul>
        </div>
        
        <div className="bg-green-50 rounded-lg p-4">
          <h3 className="font-semibold text-green-900 mb-2">交互功能</h3>
          <ul className="space-y-1 text-green-800">
            <li>✓ 力导向参数实时调节</li>
            <li>✓ 节点类型筛选</li>
            <li>✓ 关键词搜索高亮</li>
            <li>✓ 层级聚类显示</li>
            <li>✓ 选中节点聚焦</li>
          </ul>
        </div>
      </div>
    </div>
  );
};

export default EnhancedGraphExample;
