/**
 * Lean4 代码编辑器组件
 * Lean4 Code Editor Component
 */

import React, { useState, useCallback } from 'react';
import type { Lean4Code, VerificationResult } from '../../types/proofAssistant';

interface LeanCodeEditorProps {
  code: Lean4Code;
  onChange?: (code: Lean4Code) => void;
  readOnly?: boolean;
  showLineNumbers?: boolean;
  height?: string;
  onVerify?: () => Promise<VerificationResult>;
  verificationResult?: VerificationResult | null;
  className?: string;
}

export const LeanCodeEditor: React.FC<LeanCodeEditorProps> = ({
  code,
  onChange,
  readOnly = false,
  showLineNumbers = true,
  height = '400px',
  onVerify,
  verificationResult,
  className = '',
}) => {
  const [activeTab, setActiveTab] = useState<'complete' | 'statement' | 'proof'>('complete');
  const [isVerifying, setIsVerifying] = useState(false);
  const [copySuccess, setCopySuccess] = useState(false);

  // 获取要显示的代码
  const getDisplayCode = useCallback(() => {
    switch (activeTab) {
      case 'statement':
        return code.statement;
      case 'proof':
        return code.proof;
      case 'complete':
      default:
        return code.complete;
    }
  }, [code, activeTab]);

  // 处理代码编辑
  const handleCodeChange = (newCode: string) => {
    if (readOnly || !onChange) return;

    const updatedCode = { ...code };
    switch (activeTab) {
      case 'statement':
        updatedCode.statement = newCode;
        break;
      case 'proof':
        updatedCode.proof = newCode;
        break;
      case 'complete':
        updatedCode.complete = newCode;
        break;
    }
    onChange(updatedCode);
  };

  // 复制代码
  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(getDisplayCode());
      setCopySuccess(true);
      setTimeout(() => setCopySuccess(false), 2000);
    } catch (err) {
      console.error('复制失败:', err);
    }
  };

  // 下载代码
  const handleDownload = () => {
    const blob = new Blob([code.complete], { type: 'text/plain;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `${code.theorem || 'theorem'}.lean`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  // 验证代码
  const handleVerify = async () => {
    if (!onVerify || isVerifying) return;
    
    setIsVerifying(true);
    try {
      await onVerify();
    } finally {
      setIsVerifying(false);
    }
  };

  // 渲染行号
  const renderLineNumbers = (code: string) => {
    const lines = code.split('\n');
    return (
      <div className="select-none text-right pr-4 text-gray-400 text-sm font-mono leading-6">
        {lines.map((_, i) => (
          <div key={i} className="h-6">
            {i + 1}
          </div>
        ))}
      </div>
    );
  };

  // 渲染代码高亮（简化版）
  const renderHighlightedCode = (code: string) => {
    const lines = code.split('\n');
    
    return lines.map((line, i) => {
      // 简单的高亮规则
      const highlightedLine = line
        // 关键字
        .replace(/\b(import|theorem|lemma|example|def|variable|variables|open|namespace|end|by|have|let|show|suffices|where)\b/g, 
          '<span class="text-purple-600 font-semibold">$1</span>')
        // 策略
        .replace(/\b(intro|intros|apply|exact|refine|constructor|split|left|right|exists|cases|induction|rw|rewrite|simp|simp_all|linarith|nlinarith|omega|ring|field|norm_num|tauto|aesop|by_contra|exfalso|contradiction|assumption|clear|done|sorry|admit)\b/g, 
          '<span class="text-blue-600 font-semibold">$1</span>')
        // 注释
        .replace(/(--.*$|\/-[\s\S]*?-\/)/g, '<span class="text-green-600 italic">$1</span>')
        // 字符串
        .replace(/"([^"]*)"/g, '<span class="text-amber-600">"$1"</span>')
        // 数字
        .replace(/\b(\d+)\b/g, '<span class="text-orange-600">$1</span>');

      return (
        <div 
          key={i} 
          className="h-6 whitespace-pre font-mono text-sm leading-6"
          dangerouslySetInnerHTML={{ __html: highlightedLine || ' ' }}
        />
      );
    });
  };

  // 获取验证状态样式
  const getVerificationStatus = () => {
    if (!verificationResult) return null;
    
    if (isVerifying) {
      return (
        <span className="flex items-center gap-1 text-blue-600">
          <svg className="animate-spin h-4 w-4" fill="none" viewBox="0 0 24 24">
            <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" />
            <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
          </svg>
          验证中...
        </span>
      );
    }

    if (verificationResult.success) {
      return (
        <span className="flex items-center gap-1 text-green-600">
          <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
          </svg>
          验证通过 ({verificationResult.elapsed}ms)
        </span>
      );
    }

    return (
      <span className="flex items-center gap-1 text-red-600">
        <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
        </svg>
        验证失败 ({verificationResult.errors.length} 个错误)
      </span>
    );
  };

  const displayCode = getDisplayCode();

  return (
    <div className={`flex flex-col border border-gray-200 rounded-lg overflow-hidden ${className}`}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-2 bg-gray-50 border-b border-gray-200">
        <div className="flex items-center gap-2">
          <span className="text-sm font-medium text-gray-700">Lean4 代码</span>
          {getVerificationStatus()}
        </div>
        <div className="flex items-center gap-2">
          {/* 验证按钮 */}
          {onVerify && (
            <button
              onClick={handleVerify}
              disabled={isVerifying}
              className="px-3 py-1.5 text-sm bg-green-600 text-white rounded hover:bg-green-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors flex items-center gap-1"
            >
              {isVerifying ? (
                <>
                  <svg className="animate-spin h-4 w-4" fill="none" viewBox="0 0 24 24">
                    <circle className="opacity-25" cx="12" cy="12" r="10" stroke="currentColor" strokeWidth="4" />
                    <path className="opacity-75" fill="currentColor" d="M4 12a8 8 0 018-8V0C5.373 0 0 5.373 0 12h4zm2 5.291A7.962 7.962 0 014 12H0c0 3.042 1.135 5.824 3 7.938l3-2.647z" />
                  </svg>
                  验证中
                </>
              ) : (
                <>
                  <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                  </svg>
                  验证
                </>
              )}
            </button>
          )}

          {/* 复制按钮 */}
          <button
            onClick={handleCopy}
            className="px-3 py-1.5 text-sm bg-white border border-gray-300 text-gray-700 rounded hover:bg-gray-50 transition-colors flex items-center gap-1"
          >
            {copySuccess ? (
              <>
                <svg className="h-4 w-4 text-green-600" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
                </svg>
                已复制
              </>
            ) : (
              <>
                <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
                </svg>
                复制
              </>
            )}
          </button>

          {/* 下载按钮 */}
          <button
            onClick={handleDownload}
            className="px-3 py-1.5 text-sm bg-white border border-gray-300 text-gray-700 rounded hover:bg-gray-50 transition-colors flex items-center gap-1"
          >
            <svg className="h-4 w-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M4 16v1a3 3 0 003 3h10a3 3 0 003-3v-1m-4-4l-4 4m0 0l-4-4m4 4V4" />
            </svg>
            下载
          </button>
        </div>
      </div>

      {/* 标签页 */}
      <div className="flex items-center px-4 border-b border-gray-200 bg-white">
        {[
          { key: 'complete', label: '完整代码' },
          { key: 'statement', label: '定理声明' },
          { key: 'proof', label: '证明体' },
        ].map(tab => (
          <button
            key={tab.key}
            onClick={() => setActiveTab(tab.key as any)}
            className={`
              px-4 py-2 text-sm font-medium border-b-2 transition-colors
              ${activeTab === tab.key
                ? 'border-blue-500 text-blue-600'
                : 'border-transparent text-gray-600 hover:text-gray-800'}
            `}
          >
            {tab.label}
          </button>
        ))}
      </div>

      {/* 编辑器主体 */}
      <div 
        className="flex bg-white overflow-auto"
        style={{ height }}
      >
        {/* 行号 */}
        {showLineNumbers && (
          <div className="py-4 bg-gray-50 border-r border-gray-200">
            {renderLineNumbers(displayCode)}
          </div>
        )}

        {/* 代码区域 */}
        <div className="flex-1 relative">
          {readOnly ? (
            <div className="p-4">
              {renderHighlightedCode(displayCode)}
            </div>
          ) : (
            <textarea
              value={displayCode}
              onChange={(e) => handleCodeChange(e.target.value)}
              className="w-full h-full p-4 font-mono text-sm resize-none focus:outline-none leading-6"
              spellCheck={false}
              style={{ tabSize: 2 }}
            />
          )}
        </div>
      </div>

      {/* 验证结果面板 */}
      {verificationResult && !verificationResult.success && verificationResult.errors.length > 0 && (
        <div className="border-t border-red-200 bg-red-50 p-4 max-h-48 overflow-auto">
          <h4 className="text-sm font-semibold text-red-800 mb-2">
            错误 ({verificationResult.errors.length})
          </h4>
          <div className="space-y-2">
            {verificationResult.errors.map((error, i) => (
              <div key={i} className="text-sm text-red-700">
                {error.stepNumber && <span className="font-mono">步骤 {error.stepNumber}: </span>}
                <span>{error.message}</span>
                {error.suggestions && error.suggestions.length > 0 && (
                  <ul className="mt-1 ml-4 text-xs text-red-600 list-disc">
                    {error.suggestions.map((s, j) => (
                      <li key={j}>{s}</li>
                    ))}
                  </ul>
                )}
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 警告面板 */}
      {verificationResult && verificationResult.warnings.length > 0 && (
        <div className="border-t border-yellow-200 bg-yellow-50 p-4 max-h-32 overflow-auto">
          <h4 className="text-sm font-semibold text-yellow-800 mb-2">
            警告 ({verificationResult.warnings.length})
          </h4>
          <div className="space-y-1">
            {verificationResult.warnings.map((warning, i) => (
              <div key={i} className="text-sm text-yellow-700">
                {warning.stepNumber && <span className="font-mono">步骤 {warning.stepNumber}: </span>}
                <span>{warning.message}</span>
              </div>
            ))}
          </div>
        </div>
      )}

      {/* 底部信息栏 */}
      <div className="px-4 py-2 bg-gray-50 border-t border-gray-200 text-xs text-gray-500 flex justify-between">
        <span>{displayCode.split('\n').length} 行</span>
        <span>{displayCode.length} 字符</span>
      </div>
    </div>
  );
};

export default LeanCodeEditor;
