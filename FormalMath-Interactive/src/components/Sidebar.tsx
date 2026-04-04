import React, { useState } from 'react';
import { 
  ChevronRight, 
  ChevronDown, 
  Filter, 
  Layers, 
  Tag,
  Calendar,
  Users,
  Star,
  Clock,
  Bookmark
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { NodeType, NodeStatus } from '@types';

interface FilterSection {
  id: string;
  title: string;
  icon: React.ReactNode;
  options: { id: string; label: string; count?: number }[];
}

const filterSections: FilterSection[] = [
  {
    id: 'types',
    title: '节点类型',
    icon: <Layers className="w-4 h-4" />,
    options: [
      { id: 'concept', label: '概念', count: 1245 },
      { id: 'theorem', label: '定理', count: 892 },
      { id: 'proof', label: '证明', count: 567 },
      { id: 'example', label: '示例', count: 423 },
      { id: 'application', label: '应用', count: 234 },
      { id: 'mathematician', label: '数学家', count: 156 },
    ],
  },
  {
    id: 'status',
    title: '状态',
    icon: <Tag className="w-4 h-4" />,
    options: [
      { id: 'discovered', label: '已发现', count: 2890 },
      { id: 'verified', label: '已验证', count: 2341 },
      { id: 'contested', label: '有争议', count: 45 },
      { id: 'deprecated', label: '已废弃', count: 12 },
    ],
  },
  {
    id: 'domains',
    title: '领域',
    icon: <Bookmark className="w-4 h-4" />,
    options: [
      { id: 'algebra', label: '代数', count: 456 },
      { id: 'geometry', label: '几何', count: 389 },
      { id: 'analysis', label: '分析', count: 312 },
      { id: 'topology', label: '拓扑', count: 234 },
      { id: 'number-theory', label: '数论', count: 198 },
      { id: 'logic', label: '逻辑', count: 167 },
    ],
  },
  {
    id: 'time',
    title: '时间范围',
    icon: <Calendar className="w-4 h-4" />,
    options: [
      { id: 'ancient', label: '古代 (-500-500)', count: 234 },
      { id: 'medieval', label: '中世纪 (500-1500)', count: 123 },
      { id: 'renaissance', label: '文艺复兴 (1500-1700)', count: 345 },
      { id: 'modern', label: '近代 (1700-1900)', count: 890 },
      { id: 'contemporary', label: '现代 (1900-至今)', count: 1567 },
    ],
  },
];

interface SidebarProps {
  onFilterChange?: (filters: Record<string, string[]>) => void;
  className?: string;
}

export const Sidebar: React.FC<SidebarProps> = ({ onFilterChange, className }) => {
  const [expandedSections, setExpandedSections] = useState<string[]>(['types', 'status']);
  const [selectedFilters, setSelectedFilters] = useState<Record<string, string[]>>({});

  const toggleSection = (sectionId: string) => {
    setExpandedSections(prev =>
      prev.includes(sectionId)
        ? prev.filter(id => id !== sectionId)
        : [...prev, sectionId]
    );
  };

  const toggleFilter = (sectionId: string, optionId: string) => {
    setSelectedFilters(prev => {
      const current = prev[sectionId] || [];
      const updated = current.includes(optionId)
        ? current.filter(id => id !== optionId)
        : [...current, optionId];
      
      const newFilters = { ...prev, [sectionId]: updated };
      onFilterChange?.(newFilters);
      return newFilters;
    });
  };

  const clearAllFilters = () => {
    setSelectedFilters({});
    onFilterChange?.({});
  };

  const activeFilterCount = Object.values(selectedFilters).flat().length;

  return (
    <aside className={cn('w-64 bg-gray-50 border-r border-gray-200 flex flex-col h-full', className)}>
      {/* Header */}
      <div className="p-4 border-b border-gray-200">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-2 text-gray-700">
            <Filter className="w-4 h-4" />
            <span className="font-medium">过滤器</span>
          </div>
          {activeFilterCount > 0 && (
            <button
              onClick={clearAllFilters}
              className="text-xs text-blue-600 hover:text-blue-700"
            >
              清除全部 ({activeFilterCount})
            </button>
          )}
        </div>
      </div>

      {/* Quick Actions */}
      <div className="p-3 space-y-1 border-b border-gray-200">
        <button className="w-full flex items-center gap-2 px-3 py-2 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors">
          <Star className="w-4 h-4" />
          收藏夹
        </button>
        <button className="w-full flex items-center gap-2 px-3 py-2 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors">
          <Clock className="w-4 h-4" />
          最近查看
        </button>
        <button className="w-full flex items-center gap-2 px-3 py-2 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors">
          <Users className="w-4 h-4" />
          贡献者
        </button>
      </div>

      {/* Filter Sections */}
      <div className="flex-1 overflow-y-auto">
        {filterSections.map(section => {
          const isExpanded = expandedSections.includes(section.id);
          const selected = selectedFilters[section.id] || [];

          return (
            <div key={section.id} className="border-b border-gray-200 last:border-b-0">
              <button
                onClick={() => toggleSection(section.id)}
                className="w-full flex items-center justify-between px-4 py-3 text-sm font-medium text-gray-700 hover:bg-gray-100 transition-colors"
              >
                <div className="flex items-center gap-2">
                  {section.icon}
                  {section.title}
                  {selected.length > 0 && (
                    <span className="px-1.5 py-0.5 text-xs bg-blue-100 text-blue-700 rounded-full">
                      {selected.length}
                    </span>
                  )}
                </div>
                {isExpanded ? (
                  <ChevronDown className="w-4 h-4 text-gray-400" />
                ) : (
                  <ChevronRight className="w-4 h-4 text-gray-400" />
                )}
              </button>

              {isExpanded && (
                <div className="px-4 pb-3 space-y-1">
                  {section.options.map(option => {
                    const isSelected = selected.includes(option.id);
                    return (
                      <label
                        key={option.id}
                        className={cn(
                          'flex items-center justify-between px-2 py-1.5 rounded cursor-pointer text-sm transition-colors',
                          isSelected ? 'bg-blue-50 text-blue-700' : 'text-gray-600 hover:bg-gray-100'
                        )}
                      >
                        <div className="flex items-center gap-2">
                          <input
                            type="checkbox"
                            checked={isSelected}
                            onChange={() => toggleFilter(section.id, option.id)}
                            className="w-4 h-4 rounded border-gray-300 text-blue-600 focus:ring-blue-500"
                          />
                          <span>{option.label}</span>
                        </div>
                        {option.count && (
                          <span className="text-xs text-gray-400">{option.count}</span>
                        )}
                      </label>
                    );
                  })}
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* Footer */}
      <div className="p-4 border-t border-gray-200 text-xs text-gray-500">
        <p>共 3,518 个节点</p>
        <p>最后更新: 2024-01-15</p>
      </div>
    </aside>
  );
};

export default Sidebar;
