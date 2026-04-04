/**
 * 策略面板组件
 * Tactic Panel Component
 */

import React, { useState, useMemo } from 'react';
import type { 
  Tactic, 
  TacticSuggestion, 
  TacticCategory, 
  ProofState 
} from '../../types/proofAssistant';
import { proofStrategyEngine } from '../../services/proofStrategy';

interface TacticPanelProps {
  suggestions: TacticSuggestion[];
  onTacticSelect: (tactic: Tactic, params: Record<string, string>) => void;
  onTacticSearch?: (query: string) => void;
  proofState: ProofState;
  selectedCategory?: TacticCategory;
  showPreview?: boolean;
  className?: string;
}

const categoryColors: Record<TacticCategory, string> = {
  introduction: 'bg-blue-100 text-blue-800 border-blue-200',
  elimination: 'bg-green-100 text-green-800 border-green-200',
  rewriting: 'bg-purple-100 text-purple-800 border-purple-200',
  automation: 'bg-amber-100 text-amber-800 border-amber-200',
  induction: 'bg-indigo-100 text-indigo-800 border-indigo-200',
  arithmetic: 'bg-cyan-100 text-cyan-800 border-cyan-200',
  logic: 'bg-rose-100 text-rose-800 border-rose-200',
  equality: 'bg-teal-100 text-teal-800 border-teal-200',
  custom: 'bg-gray-100 text-gray-800 border-gray-200',
};

const categoryIcons: Record<TacticCategory, string> = {
  introduction: '→',
  elimination: '×',
  rewriting: '⟲',
  automation: '⚡',
  induction: '↻',
  arithmetic: '∑',
  logic: '⊤',
  equality: '=',
  custom: '⚙',
};

const difficultyColors = {
  easy: 'text-green-600',
  medium: 'text-yellow-600',
  hard: 'text-orange-600',
  expert: 'text-red-600',
};

export const TacticPanel: React.FC<TacticPanelProps> = ({
  suggestions,
  onTacticSelect,
  onTacticSearch,
  proofState,
  selectedCategory,
  showPreview = true,
  className = '',
}) => {
  const [searchQuery, setSearchQuery] = useState('');
  const [activeCategory, setActiveCategory] = useState<TacticCategory | 'all'>('all');
  const [selectedTactic, setSelectedTactic] = useState<Tactic | null>(null);
  const [tacticParams, setTacticParams] = useState<Record<string, string>>({});
  const [showAllTactics, setShowAllTactics] = useState(false);

  // 获取分类列表
  const categories = useMemo(() => proofStrategyEngine.getCategories(), []);

  // 获取所有策略
  const allTactics = useMemo(() => proofStrategyEngine.getAllTactics(), []);

  // 过滤策略
  const filteredTactics = useMemo(() => {
    let tactics = showAllTactics ? allTactics : suggestions.map(s => s.tactic);
    
    if (activeCategory !== 'all') {
      tactics = tactics.filter(t => t.category === activeCategory);
    }

    if (searchQuery.trim()) {
      const query = searchQuery.toLowerCase();
      tactics = tactics.filter(t =>
        t.name.toLowerCase().includes(query) ||
        t.description.toLowerCase().includes(query)
      );
    }

    return tactics;
  }, [allTactics, suggestions, activeCategory, searchQuery, showAllTactics]);

  // 获取建议的置信度
  const getSuggestionConfidence = (tactic: Tactic): number => {
    const suggestion = suggestions.find(s => s.tactic.id === tactic.id);
    return suggestion?.confidence || 0;
  };

  // 获取建议原因
  const getSuggestionReason = (tactic: Tactic): string | undefined => {
    const suggestion = suggestions.find(s => s.tactic.id === tactic.id);
    return suggestion?.reason;
  };

  // 处理策略选择
  const handleTacticClick = (tactic: Tactic) => {
    setSelectedTactic(tactic);
    setTacticParams({});
  };

  // 处理参数变化
  const handleParamChange = (name: string, value: string) => {
    setTacticParams(prev => ({ ...prev, [name]: value }));
  };

  // 应用策略
  const handleApplyTactic = () => {
    if (selectedTactic) {
      onTacticSelect(selectedTactic, tacticParams);
      setSelectedTactic(null);
      setTacticParams({});
    }
  };

  // 渲染策略卡片
  const renderTacticCard = (tactic: Tactic) => {
    const confidence = getSuggestionConfidence(tactic);
    const reason = getSuggestionReason(tactic);
    const isSelected = selectedTactic?.id === tactic.id;

    return (
      <div
        key={tactic.id}
        onClick={() => handleTacticClick(tactic)}
        className={`
          p-3 rounded-lg border cursor-pointer transition-all duration-200
          ${isSelected 
            ? 'border-blue-500 bg-blue-50 ring-2 ring-blue-200' 
            : 'border-gray-200 hover:border-blue-300 hover:bg-gray-50'}
        `}
      >
        <div className="flex items-start justify-between">
          <div className="flex items-center gap-2">
            <span className={`
              w-6 h-6 rounded flex items-center justify-center text-xs font-bold
              ${categoryColors[tactic.category].split(' ')[0]}
            `}>
              {categoryIcons[tactic.category]}
            </span>
            <span className="font-mono font-semibold text-gray-800">{tactic.name}</span>
          </div>
          <div className="flex items-center gap-2">
            {confidence > 0 && (
              <span className={`
                text-xs px-2 py-0.5 rounded-full font-medium
                ${confidence > 0.7 ? 'bg-green-100 text-green-700' :
                  confidence > 0.4 ? 'bg-yellow-100 text-yellow-700' :
                  'bg-gray-100 text-gray-600'}
              `}>
                {Math.round(confidence * 100)}%
              </span>
            )}
            <span className={`text-xs font-medium ${difficultyColors[tactic.difficulty]}`}>
              {tactic.difficulty === 'easy' ? '简单' :
               tactic.difficulty === 'medium' ? '中等' :
               tactic.difficulty === 'hard' ? '困难' : '专家'}
            </span>
          </div>
        </div>

        <p className="mt-2 text-sm text-gray-600 line-clamp-2">{tactic.description}</p>

        {reason && (
          <p className="mt-1 text-xs text-blue-600 italic">{reason}</p>
        )}

        {showPreview && (
          <div className="mt-2 p-2 bg-gray-100 rounded font-mono text-xs text-gray-700">
            {tactic.syntax}
          </div>
        )}
      </div>
    );
  };

  // 渲染参数输入
  const renderParamInput = (tactic: Tactic) => {
    if (!tactic.parameters || tactic.parameters.length === 0) {
      return (
        <div className="text-sm text-gray-500 italic">
          此策略不需要参数
        </div>
      );
    }

    return (
      <div className="space-y-3">
        {tactic.parameters.map(param => (
          <div key={param.name}>
            <label className="block text-sm font-medium text-gray-700 mb-1">
              {param.name}
              {param.required && <span className="text-red-500 ml-1">*</span>}
            </label>
            <input
              type="text"
              value={tacticParams[param.name] || ''}
              onChange={(e) => handleParamChange(param.name, e.target.value)}
              placeholder={param.defaultValue || `${param.description} (${param.type})`}
              className="w-full px-3 py-2 border border-gray-300 rounded-md focus:ring-2 focus:ring-blue-500 focus:border-blue-500"
            />
            <p className="mt-1 text-xs text-gray-500">{param.description}</p>
          </div>
        ))}
      </div>
    );
  };

  return (
    <div className={`flex flex-col h-full ${className}`}>
      {/* 搜索栏 */}
      <div className="p-4 border-b border-gray-200">
        <div className="relative">
          <input
            type="text"
            value={searchQuery}
            onChange={(e) => {
              setSearchQuery(e.target.value);
              onTacticSearch?.(e.target.value);
            }}
            placeholder="搜索策略..."
            className="w-full pl-10 pr-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500"
          />
          <svg
            className="absolute left-3 top-2.5 w-5 h-5 text-gray-400"
            fill="none"
            viewBox="0 0 24 24"
            stroke="currentColor"
          >
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
          </svg>
        </div>
      </div>

      {/* 分类过滤器 */}
      <div className="px-4 py-3 border-b border-gray-200">
        <div className="flex flex-wrap gap-2">
          <button
            onClick={() => setActiveCategory('all')}
            className={`
              px-3 py-1.5 rounded-full text-xs font-medium transition-colors
              ${activeCategory === 'all'
                ? 'bg-blue-600 text-white'
                : 'bg-gray-100 text-gray-700 hover:bg-gray-200'}
            `}
          >
            全部
          </button>
          {categories.map(cat => (
            <button
              key={cat.id}
              onClick={() => setActiveCategory(cat.id)}
              className={`
                px-3 py-1.5 rounded-full text-xs font-medium transition-colors flex items-center gap-1
                ${activeCategory === cat.id
                  ? 'bg-blue-600 text-white'
                  : `${categoryColors[cat.id]} hover:opacity-80`}
              `}
            >
              <span>{cat.icon}</span>
              <span>{cat.name}</span>
            </button>
          ))}
        </div>
      </div>

      {/* 切换显示模式 */}
      <div className="px-4 py-2 border-b border-gray-200 bg-gray-50">
        <label className="flex items-center gap-2 text-sm text-gray-700">
          <input
            type="checkbox"
            checked={showAllTactics}
            onChange={(e) => setShowAllTactics(e.target.checked)}
            className="rounded border-gray-300 text-blue-600 focus:ring-blue-500"
          />
          显示所有策略（不仅推荐）
        </label>
      </div>

      {/* 策略列表 */}
      <div className="flex-1 overflow-y-auto p-4">
        {filteredTactics.length > 0 ? (
          <div className="space-y-3">
            {filteredTactics.map(renderTacticCard)}
          </div>
        ) : (
          <div className="text-center py-8 text-gray-500">
            <svg className="w-12 h-12 mx-auto mb-3 text-gray-300" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M9.172 16.172a4 4 0 015.656 0M9 10h.01M15 10h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z" />
            </svg>
            <p>没有找到匹配的策略</p>
            <p className="text-sm mt-1">尝试调整搜索词或分类</p>
          </div>
        )}
      </div>

      {/* 策略详情面板 */}
      {selectedTactic && (
        <div className="border-t border-gray-200 p-4 bg-gray-50">
          <div className="flex items-center justify-between mb-3">
            <h3 className="font-semibold text-gray-800 flex items-center gap-2">
              <span className={`px-2 py-0.5 rounded text-xs ${categoryColors[selectedTactic.category]}`}>
                {categoryIcons[selectedTactic.category]} {selectedTactic.category}
              </span>
              {selectedTactic.name}
            </h3>
            <button
              onClick={() => setSelectedTactic(null)}
              className="text-gray-400 hover:text-gray-600"
            >
              <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M6 18L18 6M6 6l12 12" />
              </svg>
            </button>
          </div>

          <p className="text-sm text-gray-600 mb-4">{selectedTactic.description}</p>

          {selectedTactic.examples.length > 0 && (
            <div className="mb-4">
              <h4 className="text-xs font-semibold text-gray-500 mb-2">示例</h4>
              <div className="space-y-1">
                {selectedTactic.examples.map((ex, i) => (
                  <code key={i} className="block text-xs bg-gray-100 px-2 py-1 rounded font-mono">
                    {ex}
                  </code>
                ))}
              </div>
            </div>
          )}

          <div className="mb-4">
            <h4 className="text-xs font-semibold text-gray-500 mb-2">参数</h4>
            {renderParamInput(selectedTactic)}
          </div>

          <button
            onClick={handleApplyTactic}
            className="w-full py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors font-medium"
          >
            应用策略
          </button>
        </div>
      )}
    </div>
  );
};

export default TacticPanel;
