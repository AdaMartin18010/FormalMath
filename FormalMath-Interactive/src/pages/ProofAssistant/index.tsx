/**
 * 定理证明助手页面
 * Theorem Proof Assistant Page
 */

import React, { useState } from 'react';
import { ProofAssistant } from '../../components/ProofAssistant';
import type { ProofConstruction, ProofStep } from '../../types/proofAssistant';

// 预设定理示例
const PRESET_THEOREMS = [
  {
    name: 'add_comm',
    statement: '∀ (m n : ℕ), m + n = n + m',
    description: '自然数加法交换律',
  },
  {
    name: 'mul_assoc',
    statement: '∀ (a b c : ℕ), (a * b) * c = a * (b * c)',
    description: '自然数乘法结合律',
  },
  {
    name: 'true_intro',
    statement: 'True',
    description: '真命题证明',
  },
  {
    name: 'and_comm',
    statement: '∀ (P Q : Prop), P ∧ Q → Q ∧ P',
    description: '合取交换律',
  },
  {
    name: 'or_elim',
    statement: '∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R',
    description: '析取消去',
  },
];

const ProofAssistantPage: React.FC = () => {
  const [selectedTheorem, setSelectedTheorem] = useState(PRESET_THEOREMS[0]);
  const [customName, setCustomName] = useState('');
  const [customStatement, setCustomStatement] = useState('');
  const [useCustom, setUseCustom] = useState(false);
  const [showIntro, setShowIntro] = useState(true);
  const [lastCompletedProof, setLastCompletedProof] = useState<ProofConstruction | null>(null);

  const handleProofComplete = (proof: ProofConstruction) => {
    setLastCompletedProof(proof);
    console.log('证明完成:', proof);
  };

  const handleStepChange = (step: ProofStep) => {
    console.log('步骤变化:', step);
  };

  const getTheoremName = () => {
    return useCustom ? (customName || 'custom_theorem') : selectedTheorem.name;
  };

  const getTheoremStatement = () => {
    return useCustom ? (customStatement || 'True') : selectedTheorem.statement;
  };

  if (showIntro) {
    return (
      <div className="min-h-screen bg-gray-50 py-12 px-4">
        <div className="max-w-4xl mx-auto">
          {/* 标题 */}
          <div className="text-center mb-12">
            <h1 className="text-4xl font-bold text-gray-900 mb-4">
              交互式定理证明助手
            </h1>
            <p className="text-lg text-gray-600">
              基于 Lean4 的直观证明构造工具，支持策略推荐、状态可视化和代码生成
            </p>
          </div>

          {/* 功能特性 */}
          <div className="grid md:grid-cols-3 gap-6 mb-12">
            <div className="bg-white p-6 rounded-xl shadow-sm border border-gray-200">
              <div className="w-12 h-12 bg-blue-100 rounded-lg flex items-center justify-center mb-4">
                <svg className="w-6 h-6 text-blue-600" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9.663 17h4.673M12 3v1m6.364 1.636l-.707.707M21 12h-1M4 12H3m3.343-5.657l-.707-.707m2.828 9.9a5 5 0 117.072 0l-.548.547A3.374 3.374 0 0014 18.469V19a2 2 0 11-4 0v-.531c0-.895-.356-1.754-.988-2.386l-.548-.547z" />
                </svg>
              </div>
              <h3 className="text-lg font-semibold text-gray-900 mb-2">智能策略推荐</h3>
              <p className="text-gray-600">
                根据当前证明状态自动推荐适用策略，帮助您选择最佳的证明路径
              </p>
            </div>

            <div className="bg-white p-6 rounded-xl shadow-sm border border-gray-200">
              <div className="w-12 h-12 bg-green-100 rounded-lg flex items-center justify-center mb-4">
                <svg className="w-6 h-6 text-green-600" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 19v-6a2 2 0 00-2-2H5a2 2 0 00-2 2v6a2 2 0 002 2h2a2 2 0 002-2zm0 0V9a2 2 0 012-2h2a2 2 0 012 2v10m-6 0a2 2 0 002 2h2a2 2 0 002-2m0 0V5a2 2 0 012-2h2a2 2 0 012 2v14a2 2 0 01-2 2h-2a2 2 0 01-2-2z" />
                </svg>
              </div>
              <h3 className="text-lg font-semibold text-gray-900 mb-2">状态可视化</h3>
              <p className="text-gray-600">
                清晰展示证明目标、假设和上下文，让复杂证明变得一目了然
              </p>
            </div>

            <div className="bg-white p-6 rounded-xl shadow-sm border border-gray-200">
              <div className="w-12 h-12 bg-purple-100 rounded-lg flex items-center justify-center mb-4">
                <svg className="w-6 h-6 text-purple-600" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M10 20l4-16m4 4l4 4-4 4M6 16l-4-4 4-4" />
                </svg>
              </div>
              <h3 className="text-lg font-semibold text-gray-900 mb-2">Lean4 代码生成</h3>
              <p className="text-gray-600">
                自动生成符合 Lean4 标准的证明代码，支持验证和导出
              </p>
            </div>
          </div>

          {/* 定理选择 */}
          <div className="bg-white rounded-xl shadow-sm border border-gray-200 p-6">
            <h2 className="text-xl font-semibold text-gray-900 mb-6">选择要证明的定理</h2>

            {/* 预设定理 */}
            <div className="space-y-3 mb-6">
              <h3 className="text-sm font-medium text-gray-500">预设定理</h3>
              {PRESET_THEOREMS.map((theorem) => (
                <label
                  key={theorem.name}
                  className={`
                    flex items-center p-4 border rounded-lg cursor-pointer transition-all
                    ${!useCustom && selectedTheorem.name === theorem.name
                      ? 'border-blue-500 bg-blue-50'
                      : 'border-gray-200 hover:border-blue-300 hover:bg-gray-50'}
                  `}
                >
                  <input
                    type="radio"
                    name="theorem"
                    checked={!useCustom && selectedTheorem.name === theorem.name}
                    onChange={() => {
                      setSelectedTheorem(theorem);
                      setUseCustom(false);
                    }}
                    className="w-4 h-4 text-blue-600 border-gray-300 focus:ring-blue-500"
                  />
                  <div className="ml-3 flex-1">
                    <div className="flex items-center justify-between">
                      <span className="font-mono font-medium text-gray-900">{theorem.name}</span>
                      <span className="text-sm text-gray-500">{theorem.description}</span>
                    </div>
                    <code className="mt-1 block text-sm text-gray-600 bg-gray-100 px-2 py-1 rounded">
                      {theorem.statement}
                    </code>
                  </div>
                </label>
              ))}
            </div>

            {/* 自定义定理 */}
            <div className="space-y-3">
              <label className="flex items-center">
                <input
                  type="radio"
                  name="theorem"
                  checked={useCustom}
                  onChange={() => setUseCustom(true)}
                  className="w-4 h-4 text-blue-600 border-gray-300 focus:ring-blue-500"
                />
                <span className="ml-3 text-sm font-medium text-gray-700">自定义定理</span>
              </label>

              {useCustom && (
                <div className="ml-7 space-y-4">
                  <div>
                    <label className="block text-sm font-medium text-gray-700 mb-1">
                      定理名称
                    </label>
                    <input
                      type="text"
                      value={customName}
                      onChange={(e) => setCustomName(e.target.value)}
                      placeholder="my_theorem"
                      className="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500"
                    />
                  </div>
                  <div>
                    <label className="block text-sm font-medium text-gray-700 mb-1">
                      定理声明
                    </label>
                    <textarea
                      value={customStatement}
                      onChange={(e) => setCustomStatement(e.target.value)}
                      placeholder="∀ (x : ℕ), x = x"
                      rows={3}
                      className="w-full px-3 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500 font-mono"
                    />
                  </div>
                </div>
              )}
            </div>

            {/* 开始按钮 */}
            <div className="mt-8">
              <button
                onClick={() => setShowIntro(false)}
                className="w-full py-3 bg-blue-600 text-white font-semibold rounded-lg hover:bg-blue-700 transition-colors"
              >
                开始证明
              </button>
            </div>
          </div>

          {/* 最近完成的证明 */}
          {lastCompletedProof && (
            <div className="mt-8 bg-white rounded-xl shadow-sm border border-gray-200 p-6">
              <h3 className="text-lg font-semibold text-gray-900 mb-4">最近完成的证明</h3>
              <div className="p-4 bg-green-50 border border-green-200 rounded-lg">
                <div className="flex items-center gap-2 text-green-800 mb-2">
                  <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                  </svg>
                  <span className="font-medium">{lastCompletedProof.theoremName}</span>
                </div>
                <code className="text-sm text-gray-600 block">
                  {lastCompletedProof.theoremStatement}
                </code>
                <div className="mt-2 text-sm text-gray-500">
                  共 {lastCompletedProof.currentState.proofSteps.length} 步
                </div>
              </div>
            </div>
          )}
        </div>
      </div>
    );
  }

  return (
    <div className="h-screen flex flex-col">
      {/* 返回按钮 */}
      <div className="bg-white border-b border-gray-200 px-4 py-2 flex items-center gap-4">
        <button
          onClick={() => setShowIntro(true)}
          className="flex items-center gap-1 text-gray-600 hover:text-gray-900 transition-colors"
        >
          <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M15 19l-7-7 7-7" />
          </svg>
          返回选择
        </button>
        <div className="h-4 w-px bg-gray-300" />
        <span className="font-medium text-gray-800">
          当前定理: <span className="font-mono">{getTheoremName()}</span>
        </span>
      </div>

      {/* 证明助手 */}
      <div className="flex-1 overflow-hidden">
        <ProofAssistant
          initialTheorem={getTheoremName()}
          initialStatement={getTheoremStatement()}
          onProofComplete={handleProofComplete}
          onStepChange={handleStepChange}
          enableSuggestions={true}
          enableAutoVerify={false}
        />
      </div>
    </div>
  );
};

export default ProofAssistantPage;
