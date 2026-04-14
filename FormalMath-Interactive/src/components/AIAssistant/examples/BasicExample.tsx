// @ts-nocheck
/**
 * AI助手基础使用示例
 * 
 * 展示如何在页面中集成ChatInterface组件
 */

import React from 'react';
import { ChatInterface } from '../ChatInterface';
import type { PageContext } from '@types/aiAssistant';

// ==================== 示例1: 基础浮动窗口 ====================

export const FloatingExample: React.FC = () => {
  return (
    <div className="min-h-screen bg-gray-50 p-8">
      <h1 className="text-2xl font-bold mb-4">页面内容</h1>
      <p className="text-gray-600">
        这是页面内容区域。AI助手以浮动窗口形式显示在右下角。
      </p>
      
      {/* AI助手 - 浮动窗口模式 */}
      <ChatInterface position="floating" />
    </div>
  );
};

// ==================== 示例2: 带上下文的侧边栏 ====================

export const SidebarWithContext: React.FC = () => {
  const context: PageContext = {
    pageType: 'knowledge-graph',
    currentConcept: '群论基础',
    selectedNode: {
      id: 'group-theory-basics',
      label: '群论基础',
      type: 'concept',
      description: '群论是研究代数结构群的数学分支',
    },
  };

  return (
    <div className="flex min-h-screen">
      {/* 主内容区域 */}
      <div className="flex-1 p-8">
        <h1 className="text-2xl font-bold mb-4">知识图谱</h1>
        <p className="text-gray-600">当前概念: 群论基础</p>
      </div>
      
      {/* AI助手 - 右侧边栏模式 */}
      <ChatInterface 
        position="right" 
        context={context}
        onMessageSend={(msg) => console.log('用户发送:', msg)}
        onClose={() => console.log('AI助手关闭')}
      />
    </div>
  );
};

// ==================== 示例3: 选中公式快捷提问 ====================

export const SelectionExample: React.FC = () => {
  const [selectedFormula, setSelectedFormula] = React.useState<string>('');

  const formulas = [
    { id: 1, latex: '$E = mc^2$', name: '质能方程' },
    { id: 2, latex: '$e^{i\\pi} + 1 = 0$', name: '欧拉恒等式' },
    { id: 3, latex: '$\\int_{-\\infty}^{\\infty} e^{-x^2} dx = \\sqrt{\\pi}$', name: '高斯积分' },
  ];

  const handleAsk = (formula: string, type: 'explain' | 'prove' | 'apply') => {
    setSelectedFormula(formula);
    console.log(`询问 ${type}: ${formula}`);
  };

  return (
    <div className="min-h-screen bg-gray-50 p-8">
      <h1 className="text-2xl font-bold mb-6">数学公式示例</h1>
      
      <div className="space-y-4 mb-8">
        {formulas.map((f) => (
          <div 
            key={f.id} 
            className="p-4 bg-white rounded-lg shadow-sm border border-gray-200"
          >
            <h3 className="font-medium text-gray-700 mb-2">{f.name}</h3>
            <code className="block p-3 bg-gray-100 rounded text-blue-600 mb-3">
              {f.latex}
            </code>
            <div className="flex gap-2">
              <button
                onClick={() => handleAsk(f.latex, 'explain')}
                className="px-3 py-1.5 text-sm bg-blue-100 text-blue-700 rounded hover:bg-blue-200"
              >
                解释
              </button>
              <button
                onClick={() => handleAsk(f.latex, 'prove')}
                className="px-3 py-1.5 text-sm bg-green-100 text-green-700 rounded hover:bg-green-200"
              >
                证明
              </button>
              <button
                onClick={() => handleAsk(f.latex, 'apply')}
                className="px-3 py-1.5 text-sm bg-purple-100 text-purple-700 rounded hover:bg-purple-200"
              >
                应用
              </button>
            </div>
          </div>
        ))}
      </div>

      <ChatInterface position="floating" />
    </div>
  );
};

// ==================== 示例4: 学习路径推荐 ====================

export const LearningPathExample: React.FC = () => {
  const learningPath = ['集合论', '群论', '环论', '域论', '伽罗瓦理论'];
  
  const context: PageContext = {
    pageType: 'knowledge-graph',
    currentConcept: '伽罗瓦理论',
    learningPath,
  };

  return (
    <div className="min-h-screen bg-gray-50 p-8">
      <h1 className="text-2xl font-bold mb-4">学习路径</h1>
      
      <div className="flex items-center gap-2 mb-8">
        {learningPath.map((concept, index) => (
          <React.Fragment key={concept}>
            <span className="px-4 py-2 bg-blue-100 text-blue-800 rounded-lg font-medium">
              {concept}
            </span>
            {index < learningPath.length - 1 && (
              <span className="text-gray-400">→</span>
            )}
          </React.Fragment>
        ))}
      </div>

      <div className="bg-white p-6 rounded-xl shadow-sm border border-gray-200">
        <h2 className="text-lg font-semibold mb-2">为什么这样安排？</h2>
        <p className="text-gray-600 mb-4">
          这个学习路径按照概念依赖关系排列。点击AI助手可以获取详细的学习建议。
        </p>
      </div>

      <ChatInterface 
        position="floating" 
        context={context}
      />
    </div>
  );
};

// ==================== 示例5: 推理树集成 ====================

export const ReasoningTreeExample: React.FC = () => {
  const context: PageContext = {
    pageType: 'reasoning-tree',
    currentConcept: '费马大定理',
    selectedNode: {
      id: 'fermat-last-theorem',
      label: '费马大定理',
      type: 'theorem',
      description: '当整数n > 2时，关于x^n + y^n = z^n没有正整数解',
    },
  };

  return (
    <div className="flex min-h-screen">
      {/* 推理树可视化区域 */}
      <div className="flex-1 p-8">
        <h1 className="text-2xl font-bold mb-4">推理树: 费马大定理的证明</h1>
        
        <div className="bg-white p-6 rounded-xl shadow-sm border border-gray-200">
          <h2 className="text-lg font-semibold mb-4">证明概要</h2>
          <ol className="space-y-3 text-gray-700">
            <li className="flex items-start gap-3">
              <span className="flex-shrink-0 w-6 h-6 bg-blue-100 text-blue-700 rounded-full flex items-center justify-center text-sm font-medium">1</span>
              <span>椭圆曲线与模形式的关系（谷山-志村猜想）</span>
            </li>
            <li className="flex items-start gap-3">
              <span className="flex-shrink-0 w-6 h-6 bg-blue-100 text-blue-700 rounded-full flex items-center justify-center text-sm font-medium">2</span>
              <span>假设费马大定理不成立，构造特定的椭圆曲线</span>
            </li>
            <li className="flex items-start gap-3">
              <span className="flex-shrink-0 w-6 h-6 bg-blue-100 text-blue-700 rounded-full flex items-center justify-center text-sm font-medium">3</span>
              <span>证明该曲线不是模曲线（Ribet定理）</span>
            </li>
            <li className="flex items-start gap-3">
              <span className="flex-shrink-0 w-6 h-6 bg-blue-100 text-blue-700 rounded-full flex items-center justify-center text-sm font-medium">4</span>
              <span>与谷山-志村猜想矛盾，证毕</span>
            </li>
          </ol>
        </div>
      </div>

      {/* AI助手 */}
      <ChatInterface 
        position="right" 
        context={context}
      />
    </div>
  );
};

export default {
  FloatingExample,
  SidebarWithContext,
  SelectionExample,
  LearningPathExample,
  ReasoningTreeExample,
};
