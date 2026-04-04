import React, { useState, useCallback, useRef, useEffect, useMemo } from 'react';
import { Search, X, History, TrendingUp, ArrowRight } from 'lucide-react';
import { cn } from '@utils/classNames';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';

export interface MobileSearchProps {
  onSearch: (query: string) => void;
  onFocus?: () => void;
  onBlur?: () => void;
  suggestions?: string[];
  recentSearches?: string[];
  popularSearches?: string[];
  placeholder?: string;
  className?: string;
  showHistory?: boolean;
}

/**
 * 移动端搜索组件
 * 支持：搜索建议、历史记录、热门搜索、动画效果
 */
export const MobileSearch: React.FC<MobileSearchProps> = ({
  onSearch,
  onFocus,
  onBlur,
  suggestions = [],
  recentSearches = [],
  popularSearches = [],
  placeholder = '搜索...',
  className,
  showHistory = true,
}) => {
  const { isMobile } = useMobileDetect();
  const inputRef = useRef<HTMLInputElement>(null);
  const [query, setQuery] = useState('');
  const [isFocused, setIsFocused] = useState(false);
  const [showSuggestions, setShowSuggestions] = useState(false);
  const [activeIndex, setActiveIndex] = useState(-1);

  // 过滤建议
  const filteredSuggestions = useMemo(() => {
    if (!query.trim()) return [];
    return suggestions.filter(s => 
      s.toLowerCase().includes(query.toLowerCase())
    ).slice(0, 5);
  }, [query, suggestions]);

  // 处理输入
  const handleInputChange = useCallback((e: React.ChangeEvent<HTMLInputElement>) => {
    setQuery(e.target.value);
    setShowSuggestions(true);
    setActiveIndex(-1);
  }, []);

  // 处理搜索
  const handleSearch = useCallback((searchQuery: string) => {
    if (!searchQuery.trim()) return;
    
    onSearch(searchQuery);
    setQuery(searchQuery);
    setShowSuggestions(false);
    setIsFocused(false);
    inputRef.current?.blur();

    // 保存到本地历史
    if (showHistory) {
      const history = JSON.parse(localStorage.getItem('search-history') || '[]');
      const newHistory = [searchQuery, ...history.filter((h: string) => h !== searchQuery)].slice(0, 10);
      localStorage.setItem('search-history', JSON.stringify(newHistory));
    }
  }, [onSearch, showHistory]);

  // 处理提交
  const handleSubmit = useCallback((e: React.FormEvent) => {
    e.preventDefault();
    handleSearch(query);
  }, [query, handleSearch]);

  // 处理清除
  const handleClear = useCallback(() => {
    setQuery('');
    setShowSuggestions(false);
    inputRef.current?.focus();
  }, []);

  // 处理聚焦
  const handleFocus = useCallback(() => {
    setIsFocused(true);
    setShowSuggestions(true);
    onFocus?.();
  }, [onFocus]);

  // 处理失焦
  const handleBlur = useCallback(() => {
    // 延迟关闭，允许点击建议项
    setTimeout(() => {
      setIsFocused(false);
      setShowSuggestions(false);
      onBlur?.();
    }, 200);
  }, [onBlur]);

  // 处理键盘导航
  const handleKeyDown = useCallback((e: React.KeyboardEvent) => {
    const allSuggestions = [...filteredSuggestions, ...recentSearches];
    
    switch (e.key) {
      case 'ArrowDown':
        e.preventDefault();
        setActiveIndex(prev => 
          prev < allSuggestions.length - 1 ? prev + 1 : prev
        );
        break;
      case 'ArrowUp':
        e.preventDefault();
        setActiveIndex(prev => prev > 0 ? prev - 1 : -1);
        break;
      case 'Enter':
        if (activeIndex >= 0 && allSuggestions[activeIndex]) {
          handleSearch(allSuggestions[activeIndex]);
        } else {
          handleSubmit(e as any);
        }
        break;
      case 'Escape':
        setShowSuggestions(false);
        inputRef.current?.blur();
        break;
    }
  }, [filteredSuggestions, recentSearches, activeIndex, handleSearch, handleSubmit]);

  // 清除历史
  const clearHistory = useCallback(() => {
    localStorage.removeItem('search-history');
  }, []);

  // 加载本地历史
  const [localHistory, setLocalHistory] = useState<string[]>([]);
  useEffect(() => {
    if (showHistory) {
      const history = JSON.parse(localStorage.getItem('search-history') || '[]');
      setLocalHistory(history);
    }
  }, [showHistory, isFocused]);

  const displayHistory = recentSearches.length > 0 ? recentSearches : localHistory;

  return (
    <div className={cn('relative', className)}>
      {/* 搜索框 */}
      <form onSubmit={handleSubmit} className="relative">
        <div className={cn(
          'flex items-center gap-2 px-4 py-2.5 rounded-xl transition-all duration-200',
          'bg-gray-100 dark:bg-slate-800',
          isFocused && 'bg-white dark:bg-slate-700 ring-2 ring-blue-500 shadow-lg'
        )}>
          <Search className={cn(
            'w-5 h-5 transition-colors',
            isFocused ? 'text-blue-500' : 'text-gray-400'
          )} />
          
          <input
            ref={inputRef}
            type="text"
            value={query}
            onChange={handleInputChange}
            onFocus={handleFocus}
            onBlur={handleBlur}
            onKeyDown={handleKeyDown}
            placeholder={placeholder}
            className="flex-1 bg-transparent border-none outline-none text-gray-900 dark:text-white placeholder-gray-400"
          />
          
          {query && (
            <button
              type="button"
              onClick={handleClear}
              className="p-1 text-gray-400 hover:text-gray-600 dark:hover:text-gray-200 rounded-full hover:bg-gray-200 dark:hover:bg-slate-600 transition-colors"
            >
              <X className="w-4 h-4" />
            </button>
          )}
        </div>
      </form>

      {/* 建议面板 */}
      {showSuggestions && (isFocused || query) && (
        <div className={cn(
          'absolute top-full left-0 right-0 mt-2 bg-white dark:bg-slate-800 rounded-xl shadow-xl border border-gray-100 dark:border-slate-700 overflow-hidden z-50',
          'animate-fadeIn'
        )}>
          {/* 搜索建议 */}
          {filteredSuggestions.length > 0 && (
            <div className="py-2">
              <div className="px-4 py-1.5 text-xs font-medium text-gray-400 uppercase tracking-wider">
                搜索建议
              </div>
              {filteredSuggestions.map((suggestion, index) => (
                <button
                  key={suggestion}
                  onClick={() => handleSearch(suggestion)}
                  className={cn(
                    'w-full flex items-center gap-3 px-4 py-2.5 text-left transition-colors',
                    activeIndex === index 
                      ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600' 
                      : 'text-gray-700 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-slate-700'
                  )}
                >
                  <Search className="w-4 h-4 text-gray-400" />
                  <span className="flex-1">{suggestion}</span>
                  <ArrowRight className="w-4 h-4 text-gray-300" />
                </button>
              ))}
            </div>
          )}

          {/* 搜索历史 */}
          {showHistory && displayHistory.length > 0 && !query && (
            <div className="py-2 border-t border-gray-100 dark:border-slate-700">
              <div className="flex items-center justify-between px-4 py-1.5">
                <span className="text-xs font-medium text-gray-400 uppercase tracking-wider">
                  搜索历史
                </span>
                <button
                  onClick={clearHistory}
                  className="text-xs text-blue-500 hover:text-blue-600"
                >
                  清除
                </button>
              </div>
              {displayHistory.map((item, index) => (
                <button
                  key={item}
                  onClick={() => handleSearch(item)}
                  className={cn(
                    'w-full flex items-center gap-3 px-4 py-2.5 text-left transition-colors',
                    activeIndex === index 
                      ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600' 
                      : 'text-gray-700 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-slate-700'
                  )}
                >
                  <History className="w-4 h-4 text-gray-400" />
                  <span className="flex-1 truncate">{item}</span>
                </button>
              ))}
            </div>
          )}

          {/* 热门搜索 */}
          {popularSearches.length > 0 && !query && (
            <div className="py-2 border-t border-gray-100 dark:border-slate-700">
              <div className="px-4 py-1.5 text-xs font-medium text-gray-400 uppercase tracking-wider">
                热门搜索
              </div>
              <div className="px-4 py-2 flex flex-wrap gap-2">
                {popularSearches.map((item) => (
                  <button
                    key={item}
                    onClick={() => handleSearch(item)}
                    className="px-3 py-1.5 bg-gray-100 dark:bg-slate-700 text-gray-700 dark:text-gray-300 rounded-lg text-sm hover:bg-gray-200 dark:hover:bg-slate-600 transition-colors"
                  >
                    {item}
                  </button>
                ))}
              </div>
            </div>
          )}

          {/* 无结果 */}
          {query && filteredSuggestions.length === 0 && (
            <div className="py-8 text-center text-gray-400">
              <Search className="w-12 h-12 mx-auto mb-2 opacity-30" />
              <p className="text-sm">未找到相关建议</p>
            </div>
          )}
        </div>
      )}

      {/* 遮罩层 */}
      {isFocused && isMobile && (
        <div 
          className="fixed inset-0 bg-black/20 z-40"
          onClick={() => {
            setIsFocused(false);
            setShowSuggestions(false);
          }}
          style={{ top: '60px' }}
        />
      )}
    </div>
  );
};

export default MobileSearch;
