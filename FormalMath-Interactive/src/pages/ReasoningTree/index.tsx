import React, { useState } from 'react';
import { GitBranch, ChevronRight, CheckCircle, Circle, HelpCircle } from 'lucide-react';
import { InteractiveTree } from '@visualizations/InteractiveTree';
import { MermaidChart, mermaidTemplates } from '@visualizations/MermaidChart';
import { cn } from '@utils/classNames';
import type { ReasoningNode } from '@types';

// 模拟推理树数据
const reasoningData: ReasoningNode = {
  id: 'root',
  label: '证明：√2 是无理数',
  type: 'root',
  description: '使用反证法证明√2不能表示为两个整数的比',
  confidence: 1,
  depth: 0,
  premises: [],
  conclusion: '√2 是无理数',
  proofSteps: [],
  children: [
    {
      id: 'step1',
      label: '假设：√2 是有理数',
      type: 'branch',
      description: '为使用反证法，先假设结论的反面成立',
      confidence: 1,
      depth: 1,
      premises: [],
      conclusion: '√2 = p/q (p,q互质)',
      proofSteps: [],
      children: [
        {
          id: 'step2',
          label: '推导：2 = p²/q²',
          type: 'branch',
          description: '两边平方得到',
          confidence: 1,
          depth: 2,
          premises: ['√2 = p/q'],
          conclusion: '2q² = p²',
          proofSteps: [],
          children: [
            {
              id: 'step3',
              label: '结论：p² 是偶数',
              type: 'branch',
              description: '因为 p² = 2q²',
              confidence: 1,
              depth: 3,
              premises: ['2q² = p²'],
              conclusion: 'p² ≡ 0 (mod 2)',
              proofSteps: [],
              children: [
                {
                  id: 'step4',
                  label: '引理：p 是偶数',
                  type: 'branch',
                  description: '若p²是偶数，则p必为偶数',
                  confidence: 1,
                  depth: 4,
                  premises: ['p² ≡ 0 (mod 2)'],
                  conclusion: 'p ≡ 0 (mod 2)',
                  proofSteps: [],
                  children: [
                    {
                      id: 'step5',
                      label: '设：p = 2k',
                      type: 'leaf',
                      description: 'k为整数',
                      confidence: 1,
                      depth: 5,
                      premises: ['p ≡ 0 (mod 2)'],
                      conclusion: '∃k∈ℤ, p=2k',
                      proofSteps: [],
                    },
                  ],
                },
              ],
            },
          ],
        },
      ],
    },
  ],
};

export const ReasoningTree: React.FC = () => {
  const [viewMode, setViewMode] = useState<'tree' | 'mermaid'>('tree');
  const [selectedNode, setSelectedNode] = useState<ReasoningNode | null>(null);

  // 生成Mermaid时序图
  const mermaidDefinition = mermaidTemplates.sequence(
    ['假设', '推导', '结论', '矛盾'],
    [
      { from: '假设', to: '推导', msg: '√2 = p/q' },
      { from: '推导', to: '结论', msg: 'p² = 2q²' },
      { from: '结论', to: '矛盾', msg: 'p,q不互质' },
    ]
  );

  const renderCustomNode = (node: ReasoningNode, isExpanded: boolean) => (
    <div className="flex items-center gap-2">
      {node.type === 'root' ? (
        <CheckCircle className="w-4 h-4 text-blue-600" />
      ) : node.type === 'branch' ? (
        <GitBranch className="w-4 h-4 text-green-600" />
      ) : (
        <Circle className="w-4 h-4 text-gray-400" />
      )}
      <div>
        <span className="font-medium">{node.label}</span>
        {node.confidence < 1 && (
          <span className="ml-2 text-xs text-orange-500">
            ({Math.round(node.confidence * 100)}%)
          </span>
        )}
      </div>
    </div>
  );

  return (
    <div className="flex-1 flex flex-col h-[calc(100vh-64px)]">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200 bg-white">
        <div className="flex items-center gap-3">
          <GitBranch className="w-6 h-6 text-green-600" />
          <div>
            <h1 className="text-xl font-semibold text-gray-900">推理树</h1>
            <p className="text-sm text-gray-500">可视化数学证明的逻辑结构</p>
          </div>
        </div>
        
        <div className="flex items-center gap-2 bg-gray-100 p-1 rounded-lg">
          <button
            onClick={() => setViewMode('tree')}
            className={cn(
              'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
              viewMode === 'tree' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600 hover:text-gray-900'
            )}
          >
            树形视图
          </button>
          <button
            onClick={() => setViewMode('mermaid')}
            className={cn(
              'px-4 py-1.5 text-sm font-medium rounded-md transition-colors',
              viewMode === 'mermaid' ? 'bg-white text-gray-900 shadow-sm' : 'text-gray-600 hover:text-gray-900'
            )}
          >
            流程图
          </button>
        </div>
      </div>

      {/* Content */}
      <div className="flex-1 flex">
        <div className="flex-1 p-6 overflow-auto">
          {viewMode === 'tree' ? (
            <InteractiveTree
              data={reasoningData}
              onNodeClick={setSelectedNode}
              onNodeToggle={(node, expanded) => console.log(node.id, expanded)}
              renderNode={renderCustomNode}
              className="max-w-4xl"
            />
          ) : (
            <MermaidChart
              definition={mermaidDefinition}
              className="max-w-4xl mx-auto"
            />
          )}
        </div>

        {/* Right Panel */}
        {selectedNode && (
          <div className="w-96 border-l border-gray-200 bg-white p-6 overflow-y-auto">
            <div className="flex items-center justify-between mb-6">
              <h2 className="text-lg font-semibold text-gray-900">推理详情</h2>
              <button
                onClick={() => setSelectedNode(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                ×
              </button>
            </div>

            <div className="space-y-6">
              <div>
                <label className="text-xs font-medium text-gray-500 uppercase tracking-wide">
                  当前步骤
                </label>
                <h3 className="mt-1 text-lg font-medium text-gray-900">{selectedNode.label}</h3>
                <p className="mt-1 text-sm text-gray-600">{selectedNode.description}</p>
              </div>

              {selectedNode.premises.length > 0 && (
                <div>
                  <label className="text-xs font-medium text-gray-500 uppercase tracking-wide">
                    前提条件
                  </label>
                  <ul className="mt-2 space-y-1">
                    {selectedNode.premises.map((premise, i) => (
                      <li key={i} className="flex items-center gap-2 text-sm text-gray-700">
                        <ChevronRight className="w-4 h-4 text-green-500" />
                        {premise}
                      </li>
                    ))}
                  </ul>
                </div>
              )}

              <div>
                <label className="text-xs font-medium text-gray-500 uppercase tracking-wide">
                  结论
                </label>
                <div className="mt-2 p-3 bg-green-50 border border-green-200 rounded-lg">
                  <p className="text-sm font-medium text-green-800">{selectedNode.conclusion}</p>
                </div>
              </div>

              <div>
                <label className="text-xs font-medium text-gray-500 uppercase tracking-wide">
                  置信度
                </label>
                <div className="mt-2">
                  <div className="flex items-center gap-2">
                    <div className="flex-1 h-2 bg-gray-200 rounded-full overflow-hidden">
                      <div
                        className={cn(
                          'h-full rounded-full transition-all',
                          selectedNode.confidence > 0.8 ? 'bg-green-500' : 'bg-yellow-500'
                        )}
                        style={{ width: `${selectedNode.confidence * 100}%` }}
                      />
                    </div>
                    <span className="text-sm font-medium text-gray-700">
                      {Math.round(selectedNode.confidence * 100)}%
                    </span>
                  </div>
                </div>
              </div>

              {selectedNode.proofSteps && selectedNode.proofSteps.length > 0 && (
                <div>
                  <label className="text-xs font-medium text-gray-500 uppercase tracking-wide">
                    证明步骤
                  </label>
                  <ol className="mt-2 space-y-2">
                    {selectedNode.proofSteps.map((step, i) => (
                      <li key={step.id} className="flex gap-3 text-sm">
                        <span className="flex-shrink-0 w-6 h-6 flex items-center justify-center bg-blue-100 text-blue-700 rounded-full text-xs font-medium">
                          {step.stepNumber}
                        </span>
                        <div>
                          <p className="text-gray-900">{step.statement}</p>
                          <p className="text-xs text-gray-500">{step.justification}</p>
                        </div>
                      </li>
                    ))}
                  </ol>
                </div>
              )}
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default ReasoningTree;
