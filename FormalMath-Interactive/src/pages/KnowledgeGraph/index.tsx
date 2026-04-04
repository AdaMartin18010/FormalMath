import React, { useState, useEffect } from 'react';
import { Network, Filter, Download, RefreshCw, Info } from 'lucide-react';
import { D3Graph } from '@visualizations/D3Graph';
import { Sidebar } from '@components/Sidebar';
import { Loading } from '@components/Loading';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '@types';

// 模拟数据
const mockData: GraphData = {
  nodes: [
    { id: '1', label: '微积分', type: 'concept', status: 'verified', description: '研究变化的数学分支' },
    { id: '2', label: '导数', type: 'concept', status: 'verified', description: '瞬时变化率' },
    { id: '3', label: '积分', type: 'concept', status: 'verified', description: '累积量' },
    { id: '4', label: '牛顿-莱布尼兹公式', type: 'theorem', status: 'verified', description: '微积分基本定理' },
    { id: '5', label: '极限', type: 'concept', status: 'verified', description: '趋近过程' },
    { id: '6', label: '连续性', type: 'concept', status: 'verified', description: '无间断' },
    { id: '7', label: '微分中值定理', type: 'theorem', status: 'verified', description: '罗尔定理、拉格朗日定理' },
    { id: '8', label: '泰勒展开', type: 'theorem', status: 'verified', description: '函数的多项式逼近' },
    { id: '9', label: '莱布尼茨', type: 'mathematician', status: 'verified', description: '德国数学家' },
    { id: '10', label: '牛顿', type: 'mathematician', status: 'verified', description: '英国物理学家、数学家' },
    { id: '11', label: '定积分', type: 'concept', status: 'verified', description: '有界区间上的积分' },
    { id: '12', label: '不定积分', type: 'concept', status: 'verified', description: '原函数' },
  ],
  edges: [
    { id: 'e1', source: '1', target: '2', type: 'depends_on', label: '包含' },
    { id: 'e2', source: '1', target: '3', type: 'depends_on', label: '包含' },
    { id: 'e3', source: '4', source: '4', target: '2', type: 'proves', label: '证明' },
    { id: 'e4', source: '4', target: '3', type: 'proves' },
    { id: 'e5', source: '2', target: '5', type: 'depends_on', label: '基于' },
    { id: 'e6', source: '6', target: '5', type: 'depends_on', label: '基于' },
    { id: 'e7', source: '7', target: '2', type: 'uses', label: '应用' },
    { id: 'e8', source: '8', target: '2', type: 'extends', label: '扩展' },
    { id: 'e9', source: '9', target: '4', type: 'influences', label: '发现' },
    { id: 'e10', source: '10', target: '4', type: 'influences', label: '发现' },
    { id: 'e11', source: '3', target: '11', type: 'depends_on', label: '包含' },
    { id: 'e12', source: '3', target: '12', type: 'depends_on', label: '包含' },
  ],
};

export const KnowledgeGraph: React.FC = () => {
  const [data, setData] = useState<GraphData>(mockData);
  const [loading, setLoading] = useState(true);
  const [selectedNodes, setSelectedNodes] = useState<string[]>([]);
  const [highlightPath, setHighlightPath] = useState<string[]>([]);
  const [selectedNode, setSelectedNode] = useState<GraphNode | null>(null);
  const [viewConfig, setViewConfig] = useState<Partial<ViewConfig>>({
    layout: 'force',
    showLabels: true,
    nodeSize: 25,
    edgeWidth: 2,
  });

  useEffect(() => {
    // 模拟加载
    const timer = setTimeout(() => {
      setLoading(false);
    }, 1000);
    return () => clearTimeout(timer);
  }, []);

  const handleNodeClick = (node: GraphNode) => {
    setSelectedNodes([node.id]);
    setSelectedNode(node);
  };

  const handleEdgeClick = (edge: GraphEdge) => {
    console.log('Edge clicked:', edge);
  };

  const handleFilterChange = (filters: Record<string, string[]>) => {
    console.log('Filters changed:', filters);
    // 这里可以实现实际的过滤逻辑
  };

  const exportGraph = () => {
    const dataStr = JSON.stringify(data, null, 2);
    const blob = new Blob([dataStr], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = 'knowledge-graph.json';
    link.click();
    URL.revokeObjectURL(url);
  };

  if (loading) {
    return (
      <div className="flex-1 flex items-center justify-center">
        <Loading message="正在加载知识图谱..." size="lg" />
      </div>
    );
  }

  return (
    <div className="flex-1 flex h-[calc(100vh-64px)]">
      <Sidebar onFilterChange={handleFilterChange} />
      
      <div className="flex-1 flex flex-col min-w-0">
        {/* Toolbar */}
        <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200 bg-white">
          <div className="flex items-center gap-4">
            <div className="flex items-center gap-2">
              <Network className="w-5 h-5 text-blue-600" />
              <h1 className="font-semibold text-gray-900">知识图谱</h1>
            </div>
            <div className="h-4 w-px bg-gray-300" />
            <div className="text-sm text-gray-500">
              {data.nodes.length} 节点 · {data.edges.length} 连接
            </div>
          </div>
          
          <div className="flex items-center gap-2">
            <button
              onClick={exportGraph}
              className="flex items-center gap-1.5 px-3 py-1.5 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
            >
              <Download className="w-4 h-4" />
              导出
            </button>
            <button
              className="flex items-center gap-1.5 px-3 py-1.5 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
              onClick={() => setData(mockData)}
            >
              <RefreshCw className="w-4 h-4" />
              刷新
            </button>
          </div>
        </div>

        {/* Main Content */}
        <div className="flex-1 flex">
          <div className="flex-1 p-4">
            <D3Graph
              data={data}
              width={800}
              height={600}
              config={viewConfig}
              onNodeClick={handleNodeClick}
              onEdgeClick={handleEdgeClick}
              selectedNodes={selectedNodes}
              highlightPath={highlightPath}
              className="w-full h-full"
            />
          </div>

          {/* Right Panel - Node Details */}
          {selectedNode && (
            <div className="w-80 border-l border-gray-200 bg-white p-4 overflow-y-auto">
              <div className="flex items-center justify-between mb-4">
                <h3 className="font-semibold text-gray-900">节点详情</h3>
                <button
                  onClick={() => {
                    setSelectedNode(null);
                    setSelectedNodes([]);
                  }}
                  className="text-gray-400 hover:text-gray-600"
                >
                  ×
                </button>
              </div>
              
              <div className="space-y-4">
                <div>
                  <label className="text-xs font-medium text-gray-500 uppercase">名称</label>
                  <p className="text-lg font-semibold text-gray-900">{selectedNode.label}</p>
                </div>
                
                <div>
                  <label className="text-xs font-medium text-gray-500 uppercase">类型</label>
                  <span className={cn(
                    'inline-block px-2 py-1 text-xs font-medium rounded-full mt-1',
                    selectedNode.type === 'concept' && 'bg-blue-100 text-blue-700',
                    selectedNode.type === 'theorem' && 'bg-green-100 text-green-700',
                    selectedNode.type === 'mathematician' && 'bg-purple-100 text-purple-700',
                  )}>
                    {selectedNode.type}
                  </span>
                </div>
                
                <div>
                  <label className="text-xs font-medium text-gray-500 uppercase">状态</label>
                  <p className="text-sm text-gray-700 mt-1 capitalize">{selectedNode.status}</p>
                </div>
                
                {selectedNode.description && (
                  <div>
                    <label className="text-xs font-medium text-gray-500 uppercase">描述</label>
                    <p className="text-sm text-gray-700 mt-1">{selectedNode.description}</p>
                  </div>
                )}

                <div className="pt-4 border-t border-gray-200">
                  <button className="w-full flex items-center justify-center gap-2 px-4 py-2 bg-blue-600 text-white text-sm font-medium rounded-lg hover:bg-blue-700 transition-colors">
                    <Info className="w-4 h-4" />
                    查看完整信息
                  </button>
                </div>
              </div>
            </div>
          )}
        </div>
      </div>
    </div>
  );
};

export default KnowledgeGraph;
