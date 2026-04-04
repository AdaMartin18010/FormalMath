// ==================== 笔记搜索和标签管理组件 ====================
import React, { useState, useCallback, useEffect, useRef } from 'react';
import { useNoteStore } from '../../stores/noteStore';
import { searchNotes, advancedSearch } from '../../services/noteService';
import type { NoteSearchFilter, NoteSortOption, NoteTag } from '../../types/notes';
import {
  Search,
  X,
  Filter,
  Tag,
  Calendar,
  Type,
  SortAsc,
  SortDesc,
  Clock,
  FileText,
  ChevronDown,
  Plus,
  Hash,
  Star,
  MoreHorizontal,
} from 'lucide-react';

interface NoteSearchProps {
  onSearch?: (results: any[]) => void;
  className?: string;
}

// 排序选项
const sortOptions: { value: NoteSortOption; label: string; icon: React.ReactNode }[] = [
  { value: 'updatedAt_desc', label: '最近更新', icon: <Clock className="w-4 h-4" /> },
  { value: 'updatedAt_asc', label: '最早更新', icon: <Clock className="w-4 h-4" /> },
  { value: 'createdAt_desc', label: '最近创建', icon: <FileText className="w-4 h-4" /> },
  { value: 'createdAt_asc', label: '最早创建', icon: <FileText className="w-4 h-4" /> },
  { value: 'title_asc', label: '标题 A-Z', icon: <SortAsc className="w-4 h-4" /> },
  { value: 'title_desc', label: '标题 Z-A', icon: <SortDesc className="w-4 h-4" /> },
];

// 笔记类型选项
const noteTypes = [
  { value: 'concept', label: '概念', emoji: '💡' },
  { value: 'theorem', label: '定理', emoji: '📐' },
  { value: 'proof', label: '证明', emoji: '✓' },
  { value: 'example', label: '示例', emoji: '📝' },
  { value: 'exercise', label: '练习', emoji: '🎯' },
  { value: 'general', label: '一般', emoji: '📄' },
];

// 笔记状态选项
const noteStatuses = [
  { value: 'draft', label: '草稿', color: 'bg-yellow-100 text-yellow-700' },
  { value: 'published', label: '已发布', color: 'bg-green-100 text-green-700' },
  { value: 'archived', label: '已归档', color: 'bg-gray-100 text-gray-700' },
  { value: 'shared', label: '已分享', color: 'bg-blue-100 text-blue-700' },
];

export const NoteSearch: React.FC<NoteSearchProps> = ({
  onSearch,
  className = '',
}) => {
  const {
    tags,
    searchFilter,
    sortOption,
    setSearchFilter,
    setSortOption,
    setSearchResults,
    setIsSearching,
  } = useNoteStore();

  const [query, setQuery] = useState('');
  const [showFilters, setShowFilters] = useState(false);
  const [isSearchingLocal, setIsSearchingLocal] = useState(false);
  const [showTagManager, setShowTagManager] = useState(false);
  const [newTagName, setNewTagName] = useState('');
  const [newTagColor, setNewTagColor] = useState('#3B82F6');
  const searchTimeoutRef = useRef<NodeJS.Timeout>();

  // 预设颜色
  const presetColors = [
    '#EF4444', '#F97316', '#F59E0B', '#84CC16', '#10B981',
    '#06B6D4', '#3B82F6', '#6366F1', '#8B5CF6', '#EC4899',
  ];

  // 执行搜索
  const performSearch = useCallback(async () => {
    if (!query.trim() && !hasActiveFilters()) return;

    setIsSearchingLocal(true);
    setIsSearching(true);

    try {
      const response = await searchNotes(query, searchFilter, {
        fuzzy: true,
        highlight: true,
        limit: 50,
      });

      if (response.success && response.data) {
        setSearchResults(response.data);
        onSearch?.(response.data);
      }
    } catch (error) {
      console.error('Search failed:', error);
    } finally {
      setIsSearchingLocal(false);
      setIsSearching(false);
    }
  }, [query, searchFilter, setSearchResults, setIsSearching, onSearch]);

  // 检查是否有活动过滤器
  const hasActiveFilters = () => {
    return (
      searchFilter.type ||
      searchFilter.status ||
      (searchFilter.tags && searchFilter.tags.length > 0) ||
      searchFilter.dateRange
    );
  };

  // 延迟搜索
  useEffect(() => {
    if (searchTimeoutRef.current) {
      clearTimeout(searchTimeoutRef.current);
    }

    searchTimeoutRef.current = setTimeout(() => {
      if (query.trim() || hasActiveFilters()) {
        performSearch();
      } else {
        setSearchResults([]);
      }
    }, 300);

    return () => {
      if (searchTimeoutRef.current) {
        clearTimeout(searchTimeoutRef.current);
      }
    };
  }, [query, searchFilter, performSearch, setSearchResults]);

  // 清除搜索
  const handleClearSearch = () => {
    setQuery('');
    setSearchFilter({});
    setSearchResults([]);
  };

  // 切换类型过滤器
  const toggleTypeFilter = (type: string) => {
    setSearchFilter({
      ...searchFilter,
      type: searchFilter.type === type ? undefined : type as any,
    });
  };

  // 切换状态过滤器
  const toggleStatusFilter = (status: string) => {
    setSearchFilter({
      ...searchFilter,
      status: searchFilter.status === status ? undefined : status as any,
    });
  };

  // 切换标签过滤器
  const toggleTagFilter = (tagId: string) => {
    const currentTags = searchFilter.tags || [];
    const newTags = currentTags.includes(tagId)
      ? currentTags.filter((id) => id !== tagId)
      : [...currentTags, tagId];
    
    setSearchFilter({
      ...searchFilter,
      tags: newTags.length > 0 ? newTags : undefined,
    });
  };

  // 添加新标签
  const handleAddTag = () => {
    if (!newTagName.trim()) return;
    
    // 这里应该调用API创建标签
    console.log('Creating tag:', { name: newTagName, color: newTagColor });
    setNewTagName('');
    setShowTagManager(false);
  };

  // 获取活动过滤器数量
  const getActiveFilterCount = () => {
    let count = 0;
    if (searchFilter.type) count++;
    if (searchFilter.status) count++;
    if (searchFilter.tags?.length) count += searchFilter.tags.length;
    if (searchFilter.dateRange) count++;
    return count;
  };

  return (
    <div className={`flex flex-col ${className}`}>
      {/* 搜索栏 */}
      <div className="flex items-center space-x-2 mb-4">
        <div className="relative flex-1">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
          <input
            type="text"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="搜索笔记..."
            className="
              w-full pl-10 pr-10 py-2.5
              border border-gray-200 rounded-xl
              focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-transparent
              transition-all
            "
          />
          {query && (
            <button
              onClick={handleClearSearch}
              className="absolute right-3 top-1/2 -translate-y-1/2 text-gray-400 hover:text-gray-600"
            >
              <X className="w-5 h-5" />
            </button>
          )}
          {isSearchingLocal && (
            <div className="absolute right-10 top-1/2 -translate-y-1/2">
              <div className="w-4 h-4 border-2 border-blue-500 border-t-transparent rounded-full animate-spin" />
            </div>
          )}
        </div>

        {/* 过滤器按钮 */}
        <button
          onClick={() => setShowFilters(!showFilters)}
          className={`
            flex items-center px-4 py-2.5 rounded-xl border transition-all
            ${showFilters || getActiveFilterCount() > 0
              ? 'bg-blue-50 border-blue-200 text-blue-700'
              : 'bg-white border-gray-200 text-gray-600 hover:bg-gray-50'
            }
          `}
        >
          <Filter className="w-5 h-5 mr-2" />
          筛选
          {getActiveFilterCount() > 0 && (
            <span className="ml-2 px-2 py-0.5 bg-blue-500 text-white text-xs rounded-full">
              {getActiveFilterCount()}
            </span>
          )}
        </button>

        {/* 排序下拉菜单 */}
        <div className="relative">
          <select
            value={sortOption}
            onChange={(e) => setSortOption(e.target.value as NoteSortOption)}
            className="
              appearance-none px-4 py-2.5 pr-10
              bg-white border border-gray-200 rounded-xl
              text-gray-700 cursor-pointer
              focus:outline-none focus:ring-2 focus:ring-blue-500
            "
          >
            {sortOptions.map((opt) => (
              <option key={opt.value} value={opt.value}>
                {opt.label}
              </option>
            ))}
          </select>
          <ChevronDown className="absolute right-3 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400 pointer-events-none" />
        </div>
      </div>

      {/* 过滤器面板 */}
      {showFilters && (
        <div className="bg-gray-50 rounded-xl p-4 mb-4 space-y-4">
          {/* 类型过滤器 */}
          <div>
            <h4 className="text-sm font-medium text-gray-700 mb-2 flex items-center">
              <Type className="w-4 h-4 mr-1" />
              笔记类型
            </h4>
            <div className="flex flex-wrap gap-2">
              {noteTypes.map((type) => (
                <button
                  key={type.value}
                  onClick={() => toggleTypeFilter(type.value)}
                  className={`
                    px-3 py-1.5 rounded-lg text-sm transition-all
                    ${searchFilter.type === type.value
                      ? 'bg-blue-500 text-white'
                      : 'bg-white border border-gray-200 text-gray-600 hover:bg-gray-100'
                    }
                  `}
                >
                  <span className="mr-1">{type.emoji}</span>
                  {type.label}
                </button>
              ))}
            </div>
          </div>

          {/* 状态过滤器 */}
          <div>
            <h4 className="text-sm font-medium text-gray-700 mb-2 flex items-center">
              <FileText className="w-4 h-4 mr-1" />
              笔记状态
            </h4>
            <div className="flex flex-wrap gap-2">
              {noteStatuses.map((status) => (
                <button
                  key={status.value}
                  onClick={() => toggleStatusFilter(status.value)}
                  className={`
                    px-3 py-1.5 rounded-lg text-sm transition-all
                    ${searchFilter.status === status.value
                      ? 'bg-blue-500 text-white'
                      : `${status.color} hover:opacity-80`
                    }
                  `}
                >
                  {status.label}
                </button>
              ))}
            </div>
          </div>

          {/* 标签过滤器 */}
          <div>
            <div className="flex items-center justify-between mb-2">
              <h4 className="text-sm font-medium text-gray-700 flex items-center">
                <Tag className="w-4 h-4 mr-1" />
                标签
              </h4>
              <button
                onClick={() => setShowTagManager(true)}
                className="text-xs text-blue-500 hover:text-blue-600 flex items-center"
              >
                <Plus className="w-3 h-3 mr-0.5" />
                管理标签
              </button>
            </div>
            <div className="flex flex-wrap gap-2">
              {tags.length === 0 ? (
                <p className="text-sm text-gray-400">暂无标签</p>
              ) : (
                tags.map((tag) => (
                  <button
                    key={tag.id}
                    onClick={() => toggleTagFilter(tag.id)}
                    className={`
                      px-3 py-1.5 rounded-full text-sm transition-all
                      ${searchFilter.tags?.includes(tag.id)
                        ? 'ring-2 ring-offset-1'
                        : 'hover:opacity-80'
                      }
                    `}
                    style={{
                      backgroundColor: searchFilter.tags?.includes(tag.id) ? tag.color : tag.color + '20',
                      color: searchFilter.tags?.includes(tag.id) ? 'white' : tag.color,
                      '--tw-ring-color': tag.color,
                    } as React.CSSProperties}
                  >
                    <Hash className="w-3 h-3 inline mr-1" />
                    {tag.name}
                  </button>
                ))
              )}
            </div>
          </div>

          {/* 清除过滤器 */}
          {getActiveFilterCount() > 0 && (
            <button
              onClick={handleClearSearch}
              className="text-sm text-gray-500 hover:text-gray-700 underline"
            >
              清除所有过滤器
            </button>
          )}
        </div>
      )}

      {/* 标签管理器弹窗 */}
      {showTagManager && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <div className="bg-white rounded-2xl p-6 w-96 max-w-full">
            <div className="flex items-center justify-between mb-4">
              <h3 className="text-lg font-semibold text-gray-800">管理标签</h3>
              <button
                onClick={() => setShowTagManager(false)}
                className="text-gray-400 hover:text-gray-600"
              >
                <X className="w-5 h-5" />
              </button>
            </div>

            {/* 新建标签 */}
            <div className="mb-4">
              <label className="block text-sm font-medium text-gray-700 mb-2">
                新建标签
              </label>
              <div className="flex items-center space-x-2 mb-2">
                <input
                  type="text"
                  value={newTagName}
                  onChange={(e) => setNewTagName(e.target.value)}
                  placeholder="标签名称"
                  className="flex-1 px-3 py-2 border border-gray-200 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
                />
                <button
                  onClick={handleAddTag}
                  disabled={!newTagName.trim()}
                  className="px-4 py-2 bg-blue-500 text-white rounded-lg hover:bg-blue-600 disabled:opacity-50"
                >
                  添加
                </button>
              </div>
              <div className="flex flex-wrap gap-2">
                {presetColors.map((color) => (
                  <button
                    key={color}
                    onClick={() => setNewTagColor(color)}
                    className={`
                      w-8 h-8 rounded-full transition-all
                      ${newTagColor === color ? 'ring-2 ring-offset-2 ring-gray-400' : ''}
                    `}
                    style={{ backgroundColor: color }}
                  />
                ))}
              </div>
            </div>

            {/* 现有标签 */}
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-2">
                现有标签
              </label>
              <div className="space-y-2 max-h-48 overflow-y-auto">
                {tags.map((tag) => (
                  <div
                    key={tag.id}
                    className="flex items-center justify-between p-2 bg-gray-50 rounded-lg"
                  >
                    <div className="flex items-center">
                      <span
                        className="w-3 h-3 rounded-full mr-2"
                        style={{ backgroundColor: tag.color }}
                      />
                      <span className="text-sm">{tag.name}</span>
                      <span className="ml-2 text-xs text-gray-400">
                        ({tag.count || 0})
                      </span>
                    </div>
                    <button className="text-gray-400 hover:text-red-500">
                      <X className="w-4 h-4" />
                    </button>
                  </div>
                ))}
              </div>
            </div>
          </div>
        </div>
      )}

      {/* 活动过滤器标签 */}
      {getActiveFilterCount() > 0 && (
        <div className="flex flex-wrap gap-2 mb-4">
          {searchFilter.type && (
            <span className="inline-flex items-center px-3 py-1 bg-blue-100 text-blue-700 text-sm rounded-full">
              类型: {noteTypes.find((t) => t.value === searchFilter.type)?.label}
              <button
                onClick={() => setSearchFilter({ ...searchFilter, type: undefined })}
                className="ml-2 hover:text-blue-900"
              >
                <X className="w-3 h-3" />
              </button>
            </span>
          )}
          {searchFilter.status && (
            <span className="inline-flex items-center px-3 py-1 bg-green-100 text-green-700 text-sm rounded-full">
              状态: {noteStatuses.find((s) => s.value === searchFilter.status)?.label}
              <button
                onClick={() => setSearchFilter({ ...searchFilter, status: undefined })}
                className="ml-2 hover:text-green-900"
              >
                <X className="w-3 h-3" />
              </button>
            </span>
          )}
          {searchFilter.tags?.map((tagId) => {
            const tag = tags.find((t) => t.id === tagId);
            if (!tag) return null;
            return (
              <span
                key={tagId}
                className="inline-flex items-center px-3 py-1 text-sm rounded-full"
                style={{ backgroundColor: tag.color + '20', color: tag.color }}
              >
                <Hash className="w-3 h-3 mr-1" />
                {tag.name}
                <button
                  onClick={() => toggleTagFilter(tagId)}
                  className="ml-2 opacity-70 hover:opacity-100"
                >
                  <X className="w-3 h-3" />
                </button>
              </span>
            );
          })}
        </div>
      )}
    </div>
  );
};

export default NoteSearch;
