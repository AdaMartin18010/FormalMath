import React, { useState } from 'react';
import { Brain, Plus, Minus, Share2, Download } from 'lucide-react';
import { MermaidChart, mermaidTemplates } from '@visualizations/MermaidChart';
import { InteractiveTree } from '@visualizations/InteractiveTree';
import { cn } from '@utils/classNames';
import type { MindMapNode } from '@types';

// 模拟思维导图数据
const mindMapData: MindMapNode = {
  id: 'root',
  text: '线性代数',
  style: { backgroundColor: '#3b82f6', textColor: '#ffffff' },
  children: [
    {
      id: 'vec',
      text: '向量',
      style: { backgroundColor: '#10b981', textColor: '#ffffff' },
      children: [
        { id: 'vec-def', text: '定义', children: [
          { id: 'vec-def-1', text: '有大小和方向的量' },
          { id: 'vec-def-2', text: 'n维向量空间' },
        ]},
        { id: 'vec-op', text: '运算', children: [
          { id: 'vec-op-1', text: '加法' },
          { id: 'vec-op-2', text: '数乘' },
          { id: 'vec-op-3', text: '点积' },
          { id: 'vec-op-4', text: '叉积' },
        ]},
        { id: 'vec-norm', text: '范数', children: [
          { id: 'vec-norm-1', text: 'L1范数' },
          { id: 'vec-norm-2', text: 'L2范数' },
          { id: 'vec-norm-3', text: '无穷范数' },
        ]},
      ],
    },
    {
      id: 'mat',
      text: '矩阵',
      style: { backgroundColor: '#8b5cf6', textColor: '#ffffff' },
      children: [
        { id: 'mat-def', text: '定义', children: [
          { id: 'mat-def-1', text: 'm×n 数表' },
          { id: 'mat-def-2', text: '方阵' },
        ]},
        { id: 'mat-op', text: '运算', children: [
          { id: 'mat-op-1', text: '加法' },
          { id: 'mat-op-2', text: '乘法' },
          { id: 'mat-op-3', text: '转置' },
          { id: 'mat-op-4', text: '逆矩阵' },
        ]},
        { id: 'mat-det', text: '行列式', children: [
          { id: 'mat-det-1', text: '几何意义' },
          { id: 'mat-det-2', text: '计算方法' },
        ]},
      ],
    },
    {
      id: 'space',
      text: '向量空间',
      style: { backgroundColor: '#f59e0b', textColor: '#ffffff' },
      children: [
        { id: 'space-def', text: '定义', children: [
          { id: 'space-def-1', text: '8条公理' },
          { id: 'space-def-2', text: '子空间' },
        ]},
        { id: 'space-basis', text: '基与维数', children: [
          { id: 'space-basis-1', text: '线性无关' },
          { id: 'space-basis-2', text: '生成空间' },
          { id: 'space-basis-3', text: '维数定理' },
        ]},
        { id: 'space-transform', text: '线性变换', children: [
          { id: 'space-trans-1', text: '定义' },
          { id: 'space-trans-2', text: '矩阵表示' },
          { id: 'space-trans-3', text: '特征值' },
          { id: 'space-trans-4', text: '特征向量' },
        ]},
      ],
    },
    {
      id: 'app',
      text: '应用',
      style: { backgroundColor: '#ec4899', textColor: '#ffffff' },
      children: [
        { id: 'app-ml', text: '机器学习' },
        { id: 'app-cg', text: '计算机图形学' },
        { id: 'app-crypto', text: '密码学' },
        { id: 'app-quantum', text: '量子计算' },
      ],
    },
  ],
};

export const MindMap: React.FC = () => {
  const [viewMode, setViewMode] = useState<'tree' | 'mermaid'>('mermaid');
  const [zoom, setZoom] = useState(1);
  const [selectedNode, setSelectedNode] = useState<MindMapNode | null>(null);

  // 生成Mermaid思维导图
  const mermaidDefinition = mermaidTemplates.mindmap(
    '线性代数',
    [
      { text: '向量', subBranches: ['定义', '运算', '范数'] },
      { text: '矩阵', subBranches: ['定义', '运算', '行列式'] },
      { text: '向量空间', subBranches: ['定义', '基与维数', '线性变换'] },
      { text: '应用', subBranches: ['机器学习', '图形学', '密码学'] },
    ]
  );

  const renderCustomNode = (node: MindMapNode, isExpanded: boolean) => (
    <div className="flex items-center gap-2">
      <div
        className="w-3 h-3 rounded-full"
        style={{ backgroundColor: node.style?.backgroundColor || '#6b7280' }}
      />
      <span className="font-medium" style={{ color: node.style?.textColor }}>
        {node.text}
      </span>
    </div>
  );

  return (
    <div className="flex-1 flex flex-col h-[calc(100vh-64px)]">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200 bg-white">
        <div className="flex items-center gap-3">
          <Brain className="w-6 h-6 text-purple-600" />
          <div>
            <h1 className="text-xl font-semibold text-gray-900">思维导图</h1>
            <p className="text-sm text-gray-500">层级化组织数学知识结构</p>
          </div>
        </div>
        
        <div className="flex items-center gap-3">
          <div className="flex items-center gap-2 bg-gray-100 p-1 rounded-lg">
            <button
              onClick={() => setViewMode('mermaid')}
              className={cn(
                'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
                viewMode === 'mermaid' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
              )}
            >
              思维导图
            </button>
            <button
              onClick={() => setViewMode('tree')}
              className={cn(
                'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
                viewMode === 'tree' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600'
              )}
            >
              大纲视图
            </button>
          </div>
          
          <div className="flex items-center gap-1">
            <button
              onClick={() => setZoom(z => Math.max(0.5, z - 0.1))}
              className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg"
            >
              <Minus className="w-4 h-4" />
            </button>
            <span className="text-sm text-gray-600 w-12 text-center">
              {Math.round(zoom * 100)}%
            </span>
            <button
              onClick={() => setZoom(z => Math.min(2, z + 0.1))}
              className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg"
            >
              <Plus className="w-4 h-4" />
            </button>
          </div>
          
          <button className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg" title="分享">
            <Share2 className="w-4 h-4" />
          </button>
          <button className="p-2 text-gray-600 hover:bg-gray-100 rounded-lg" title="导出">
            <Download className="w-4 h-4" />
          </button>
        </div>
      </div>

      {/* Content */}
      <div className="flex-1 overflow-auto bg-gray-50 p-6">
        <div style={{ transform: `scale(${zoom})`, transformOrigin: 'top center' }}>
          {viewMode === 'mermaid' ? (
            <MermaidChart
              definition={mermaidDefinition}
              className="max-w-4xl mx-auto bg-white"
            />
          ) : (
            <InteractiveTree
              data={mindMapData}
              onNodeClick={setSelectedNode}
              renderNode={renderCustomNode}
              className="max-w-2xl mx-auto"
            />
          )}
        </div>
      </div>
    </div>
  );
};

export default MindMap;
