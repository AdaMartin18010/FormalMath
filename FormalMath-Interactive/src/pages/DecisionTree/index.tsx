import React, { useState } from 'react';
import { Layout, Play, RotateCcw, CheckCircle, XCircle, HelpCircle } from 'lucide-react';
import { MermaidChart } from '@visualizations/MermaidChart';
import { InteractiveTree } from '@visualizations/InteractiveTree';
import { cn } from '@utils/classNames';

// 决策节点类型
interface DecisionNode {
  id: string;
  type: 'decision' | 'result';
  question?: string;
  condition?: string;
  yesText?: string;
  noText?: string;
  result?: string;
  yesBranch?: DecisionNode;
  noBranch?: DecisionNode;
}

// 判断矩阵对角化决策树
const decisionTreeData: DecisionNode = {
  id: 'root',
  type: 'decision',
  question: '判断矩阵是否可对角化',
  condition: '矩阵 A 是 n×n 方阵',
  yesText: '是',
  noText: '否',
  yesBranch: {
    id: 'check-eigen',
    type: 'decision',
    question: '有 n 个线性无关的特征向量？',
    condition: '几何重数 = 代数重数',
    yesText: '是',
    noText: '否',
    yesBranch: {
      id: 'diagonalizable',
      type: 'result',
      result: 'A 可对角化',
    },
    noBranch: {
      id: 'not-diagonalizable',
      type: 'result',
      result: 'A 不可对角化',
    },
  },
  noBranch: {
    id: 'not-square',
    type: 'result',
    result: '非方阵，无法对角化',
  },
};

// 生成Mermaid流程图
const generateMermaidDefinition = (node: DecisionNode, indent = 0): string => {
  const lines: string[] = [];
  const prefix = '  '.repeat(indent);
  
  if (node.type === 'decision') {
    lines.push(`${prefix}${node.id}{${node.question}}`);
    if (node.yesBranch) {
      lines.push(`${prefix}${node.id} -->|${node.yesText || '是'}| ${node.yesBranch.id}`);
      lines.push(generateMermaidDefinition(node.yesBranch, indent));
    }
    if (node.noBranch) {
      lines.push(`${prefix}${node.id} -->|${node.noText || '否'}| ${node.noBranch.id}`);
      lines.push(generateMermaidDefinition(node.noBranch, indent));
    }
  } else {
    lines.push(`${prefix}${node.id}[${node.result}]`);
  }
  
  return lines.join('\n');
};

const mermaidDefinition = `flowchart TD\n${generateMermaidDefinition(decisionTreeData, 1)}`;

export const DecisionTree: React.FC = () => {
  const [currentStep, setCurrentStep] = useState<DecisionNode>(decisionTreeData);
  const [history, setHistory] = useState<DecisionNode[]>([]);
  const [path, setPath] = useState<string[]>([]);

  const handleChoice = (choice: 'yes' | 'no') => {
    const nextNode = choice === 'yes' ? currentStep.yesBranch : currentStep.noBranch;
    if (nextNode) {
      setHistory([...history, currentStep]);
      setPath([...path, choice]);
      setCurrentStep(nextNode);
    }
  };

  const handleReset = () => {
    setCurrentStep(decisionTreeData);
    setHistory([]);
    setPath([]);
  };

  const handleBack = () => {
    if (history.length > 0) {
      const prevNode = history[history.length - 1];
      setHistory(history.slice(0, -1));
      setPath(path.slice(0, -1));
      setCurrentStep(prevNode);
    }
  };

  return (
    <div className="flex-1 flex flex-col h-[calc(100vh-64px)]">
      {/* Header */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200 bg-white">
        <div className="flex items-center gap-3">
          <Layout className="w-6 h-6 text-pink-600" />
          <div>
            <h1 className="text-xl font-semibold text-gray-900">决策树</h1>
            <p className="text-sm text-gray-500">基于条件判断的问题求解向导</p>
          </div>
        </div>
        
        <button
          onClick={handleReset}
          className="flex items-center gap-2 px-4 py-2 text-sm text-gray-600 bg-gray-100 rounded-lg hover:bg-gray-200 transition-colors"
        >
          <RotateCcw className="w-4 h-4" />
          重新开始
        </button>
      </div>

      {/* Content */}
      <div className="flex-1 flex">
        {/* Interactive Decision Panel */}
        <div className="flex-1 p-6 flex items-center justify-center bg-gray-50">
          <div className="max-w-lg w-full">
            {currentStep.type === 'decision' ? (
              <div className="bg-white rounded-2xl shadow-lg p-8">
                {/* Progress */}
                <div className="flex items-center gap-2 mb-6">
                  {path.map((p, i) => (
                    <React.Fragment key={i}>
                      <div className={cn(
                        'w-8 h-8 rounded-full flex items-center justify-center text-sm font-medium',
                        p === 'yes' ? 'bg-green-100 text-green-700' : 'bg-red-100 text-red-700'
                      )}>
                        {p === 'yes' ? 'Y' : 'N'}
                      </div>
                      {i < path.length - 1 && (
                        <div className="w-8 h-0.5 bg-gray-200" />
                      )}
                    </React.Fragment>
                  ))}
                  <div className="w-8 h-8 rounded-full bg-blue-100 text-blue-700 flex items-center justify-center text-sm font-medium">
                    ?
                  </div>
                </div>

                {/* Question */}
                <div className="text-center mb-8">
                  <div className="inline-flex items-center justify-center w-16 h-16 bg-blue-100 rounded-full mb-4">
                    <HelpCircle className="w-8 h-8 text-blue-600" />
                  </div>
                  <h2 className="text-2xl font-bold text-gray-900 mb-2">
                    {currentStep.question}
                  </h2>
                  {currentStep.condition && (
                    <p className="text-gray-500">{currentStep.condition}</p>
                  )}
                </div>

                {/* Choices */}
                <div className="grid grid-cols-2 gap-4">
                  <button
                    onClick={() => handleChoice('yes')}
                    className="flex flex-col items-center gap-3 p-6 border-2 border-green-200 rounded-xl hover:border-green-500 hover:bg-green-50 transition-colors"
                  >
                    <CheckCircle className="w-10 h-10 text-green-500" />
                    <span className="font-medium text-gray-900">{currentStep.yesText || '是'}</span>
                  </button>
                  <button
                    onClick={() => handleChoice('no')}
                    className="flex flex-col items-center gap-3 p-6 border-2 border-red-200 rounded-xl hover:border-red-500 hover:bg-red-50 transition-colors"
                  >
                    <XCircle className="w-10 h-10 text-red-500" />
                    <span className="font-medium text-gray-900">{currentStep.noText || '否'}</span>
                  </button>
                </div>

                {/* Back Button */}
                {history.length > 0 && (
                  <button
                    onClick={handleBack}
                    className="w-full mt-4 py-2 text-sm text-gray-500 hover:text-gray-700 transition-colors"
                  >
                    ← 上一步
                  </button>
                )}
              </div>
            ) : (
              <div className="bg-white rounded-2xl shadow-lg p-8 text-center">
                <div className={cn(
                  'inline-flex items-center justify-center w-20 h-20 rounded-full mb-6',
                  currentStep.result?.includes('不可') ? 'bg-red-100' : 'bg-green-100'
                )}>
                  {currentStep.result?.includes('不可') ? (
                    <XCircle className="w-10 h-10 text-red-600" />
                  ) : (
                    <CheckCircle className="w-10 h-10 text-green-600" />
                  )}
                </div>
                <h2 className="text-2xl font-bold text-gray-900 mb-4">
                  {currentStep.result}
                </h2>
                <button
                  onClick={handleReset}
                  className="px-6 py-3 bg-blue-600 text-white font-medium rounded-xl hover:bg-blue-700 transition-colors"
                >
                  再次尝试
                </button>
              </div>
            )}
          </div>
        </div>

        {/* Diagram Panel */}
        <div className="w-96 border-l border-gray-200 bg-white p-4">
          <h3 className="font-semibold text-gray-900 mb-4">完整决策图</h3>
          <MermaidChart
            definition={mermaidDefinition}
            className="text-xs"
          />
        </div>
      </div>
    </div>
  );
};

export default DecisionTree;
