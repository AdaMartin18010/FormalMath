// @ts-nocheck
/**
 * 定理证明助手主组件
 * Theorem Proof Assistant Main Component
 */

import React, { useState, useCallback, useEffect } from 'react';
import type { 
  ProofAssistantProps, 
  ProofConstruction, 
  ProofState,
  Tactic,
  TacticSuggestion,
  VerificationResult,
  Lean4Code,
  ProofCheckpoint,
} from '../../types/proofAssistant';
import { ProofConstructionService } from '../../services/proofConstruction';
import { proofStrategyEngine } from '../../services/proofStrategy';
import { leanCodeGenerator } from '../../services/leanCodeGenerator';
import { proofVerifier } from '../../services/proofVerifier';

// 子组件
import { ProofStateView } from './ProofStateView';
import { TacticPanel } from './TacticPanel';
import { LeanCodeEditor } from './LeanCodeEditor';

// 主组件
export const ProofAssistant: React.FC<ProofAssistantProps> = ({
  initialTheorem,
  initialStatement,
  onProofComplete,
  onStepChange,
  enableSuggestions = true,
  enableAutoVerify = false,
}) => {
  // 服务实例
  const [service, setService] = useState<ProofConstructionService | null>(null);
  
  // 状态
  const [construction, setConstruction] = useState<ProofConstruction | null>(null);
  const [suggestions, setSuggestions] = useState<TacticSuggestion[]>([]);
  const [verificationResult, setVerificationResult] = useState<VerificationResult | null>(null);
  const [isVerifying, setIsVerifying] = useState(false);
  const [leanCode, setLeanCode] = useState<Lean4Code | null>(null);
  const [isApplyingTactic, setIsApplyingTactic] = useState(false);
  const [error, setError] = useState<string | null>(null);

  // 初始化
  useEffect(() => {
    const theoremName = initialTheorem || 'my_theorem';
    const theoremStatement = initialStatement || 'True';
    
    const newService = new ProofConstructionService(theoremName, theoremStatement);
    setService(newService);
    
    const initialConstruction = newService.getConstruction();
    setConstruction(initialConstruction);
    
    // 生成初始建议
    const initialSuggestions = proofStrategyEngine.getSuggestions(initialConstruction.currentState);
    setSuggestions(initialSuggestions);
    
    // 生成初始 Lean 代码
    const code = leanCodeGenerator.generate(initialConstruction);
    setLeanCode(code);

    // 订阅状态变化
    const unsubscribe = newService.subscribe((newConstruction) => {
      setConstruction(newConstruction);
      
      // 更新建议
      if (enableSuggestions) {
        const newSuggestions = proofStrategyEngine.getSuggestions(newConstruction.currentState);
        setSuggestions(newSuggestions);
      }
      
      // 更新 Lean 代码
      const newCode = leanCodeGenerator.generate(newConstruction);
      setLeanCode(newCode);
      
      // 检查证明是否完成
      if (newService.isComplete()) {
        onProofComplete?.(newConstruction);
      }
      
      // 通知步骤变化
      const lastStep = newConstruction.currentState.proofSteps[newConstruction.currentState.proofSteps.length - 1];
      if (lastStep) {
        onStepChange?.(lastStep);
      }
      
      // 自动验证
      if (enableAutoVerify) {
        handleVerify();
      }
    });

    return () => {
      unsubscribe();
    };
  }, [initialTheorem, initialStatement]);

  // 应用策略
  const handleApplyTactic = useCallback(async (tactic: Tactic, params: Record<string, string>) => {
    if (!service || isApplyingTactic) return;
    
    setIsApplyingTactic(true);
    setError(null);
    
    try {
      const success = await service.applyTactic(tactic, params);
      if (!success) {
        setError('应用策略失败');
      }
    } catch (err) {
      setError(err instanceof Error ? err.message : '应用策略时发生错误');
    } finally {
      setIsApplyingTactic(false);
    }
  }, [service, isApplyingTactic]);

  // 撤销
  const handleUndo = useCallback(() => {
    if (!service) return;
    const success = service.undo();
    if (!success) {
      setError('没有可以撤销的步骤');
    }
  }, [service]);

  // 验证证明
  const handleVerify = useCallback(async () => {
    if (!service || !construction || isVerifying) return;
    
    setIsVerifying(true);
    setError(null);
    
    try {
      const result = await proofVerifier.verifyProof(construction);
      setVerificationResult(result);
      return result;
    } catch (err) {
      setError(err instanceof Error ? err.message : '验证时发生错误');
      return null;
    } finally {
      setIsVerifying(false);
    }
  }, [service, construction, isVerifying]);

  // 验证 Lean 代码
  const handleVerifyCode = useCallback(async () => {
    if (!leanCode || isVerifying) return;
    
    setIsVerifying(true);
    
    try {
      const result = await proofVerifier.verifyLeanCode(leanCode);
      setVerificationResult(result);
      return result;
    } catch (err) {
      setError(err instanceof Error ? err.message : '验证代码时发生错误');
      return null;
    } finally {
      setIsVerifying(false);
    }
  }, [leanCode, isVerifying]);

  // 处理目标选择
  const handleGoalSelect = useCallback((goalId: string) => {
    if (!service) return;
    service.switchGoal(goalId);
  }, [service]);

  // 处理假设点击
  const handleHypothesisClick = useCallback((hypothesis: any) => {
    // 可以在这里添加假设相关的操作，如显示详情、添加到策略参数等
    console.log('假设被点击:', hypothesis);
  }, []);

  // 如果没有初始化完成，显示加载状态
  if (!construction || !leanCode) {
    return (
      <div className="flex items-center justify-center h-96">
        <div className="text-center">
          <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto mb-4"></div>
          <p className="text-gray-600">正在初始化证明助手...</p>
        </div>
      </div>
    );
  }

  return (
    <div className="flex flex-col h-screen bg-gray-50">
      {/* 顶部工具栏 */}
      <div className="bg-white border-b border-gray-200 px-4 py-3">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-4">
            <h1 className="text-xl font-bold text-gray-800">
              定理证明助手
            </h1>
            <span className="text-sm text-gray-500 font-mono">
              {construction.theoremName}
            </span>
          </div>
          
          <div className="flex items-center gap-2">
            {/* 撤销按钮 */}
            <button
              onClick={handleUndo}
              disabled={construction.currentState.proofSteps.length === 0}
              className="px-3 py-1.5 text-sm bg-gray-100 text-gray-700 rounded hover:bg-gray-200 disabled:opacity-50 disabled:cursor-not-allowed transition-colors flex items-center gap-1"
            >
              <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M3 10h10a8 8 0 018 8v2M3 10l6 6m-6-6l6-6" />
              </svg>
              撤销
            </button>

            {/* 验证按钮 */}
            <button
              onClick={handleVerify}
              disabled={isVerifying || construction.currentState.proofSteps.length === 0}
              className="px-3 py-1.5 text-sm bg-green-600 text-white rounded hover:bg-green-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors flex items-center gap-1"
            >
              {isVerifying ? (
                <>
                  <svg className="animate-spin h-4 w-4" fill="none" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                  </svg>
                  验证中...
                </>
              ) : (
                <>
                  <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                  </svg>
                  验证证明
                </>
              )}
            </button>

            {/* 完成状态 */}
            {service?.isComplete() && (
              <span className="px-3 py-1.5 bg-green-100 text-green-800 rounded-full text-sm font-medium flex items-center gap-1">
                <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                </svg>
                证明完成
              </span>
            )}
          </div>
        </div>

        {/* 错误提示 */}
        {error && (
          <div className="mt-2 p-2 bg-red-50 border border-red-200 rounded text-sm text-red-700 flex items-center gap-2">
            <svg className="h-4 w-4 flex-shrink-0" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
            </svg>
            {error}
            <button 
              onClick={() => setError(null)}
              className="ml-auto text-red-500 hover:text-red-700"
            >
              <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>
        )}
      </div>

      {/* 主内容区 */}
      <div className="flex-1 overflow-hidden">
        <div className="h-full grid grid-cols-12 gap-4 p-4">
          {/* 左侧：证明状态 */}
          <div className="col-span-3 bg-white rounded-lg shadow-sm border border-gray-200 overflow-hidden flex flex-col">
            <div className="px-4 py-3 border-b border-gray-200 bg-gray-50">
              <h2 className="font-semibold text-gray-800">证明状态</h2>
              <p className="text-xs text-gray-500 mt-1">
                {construction.currentState.proofSteps.length} 步 | 
                {service?.getPendingGoals().length || 0} 个待证明目标
              </p>
            </div>
            <div className="flex-1 overflow-auto p-4">
              <ProofStateView
                proofState={construction.currentState}
                onGoalSelect={handleGoalSelect}
                onHypothesisClick={handleHypothesisClick}
              />
            </div>
          </div>

          {/* 中间：策略面板 */}
          <div className="col-span-3 bg-white rounded-lg shadow-sm border border-gray-200 overflow-hidden flex flex-col">
            <TacticPanel
              suggestions={suggestions}
              onTacticSelect={handleApplyTactic}
              proofState={construction.currentState}
            />
          </div>

          {/* 右侧：Lean 代码编辑器 */}
          <div className="col-span-6 bg-white rounded-lg shadow-sm border border-gray-200 overflow-hidden flex flex-col">
            <div className="flex-1 p-4 overflow-auto">
              <LeanCodeEditor
                code={leanCode}
                onChange={setLeanCode}
                onVerify={handleVerifyCode}
                verificationResult={verificationResult}
                height="100%"
              />
            </div>
          </div>
        </div>
      </div>

      {/* 底部状态栏 */}
      <div className="bg-white border-t border-gray-200 px-4 py-2 text-sm text-gray-600 flex justify-between">
        <div className="flex items-center gap-4">
          <span>定理: <span className="font-mono">{construction.theoremName}</span></span>
          <span>步骤: {construction.currentState.proofSteps.length}</span>
          <span>目标: {construction.currentState.goals.length}</span>
        </div>
        <div className="flex items-center gap-4">
          {verificationResult && (
            <span className={verificationResult.success ? 'text-green-600' : 'text-red-600'}>
              {verificationResult.success ? '✓ 验证通过' : `✗ ${verificationResult.errors.length} 个错误`}
            </span>
          )}
          <span className="text-gray-400">Lean4 证明助手</span>
        </div>
      </div>
    </div>
  );
};

// 导出所有子组件和类型
export { ProofStateView } from './ProofStateView';
export { TacticPanel } from './TacticPanel';
export { LeanCodeEditor } from './LeanCodeEditor';

// 导出默认组件
export default ProofAssistant;
