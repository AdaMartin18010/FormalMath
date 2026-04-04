// ==================== 笔记模板系统组件 ====================
import React, { useState, useCallback } from 'react';
import { useNoteStore } from '../../stores/noteStore';
import { createNoteFromTemplate, fetchTemplates } from '../../services/noteService';
import type { NoteTemplate, NoteType } from '../../types/notes';
import {
  Layout,
  BookOpen,
  Calculator,
  Lightbulb,
  FileText,
  Target,
  ChevronRight,
  X,
  Plus,
  Search,
  Star,
  Copy,
  Edit3,
  Check,
  MoreHorizontal,
  Grid,
  List,
} from 'lucide-react';

interface NoteTemplatesProps {
  onSelectTemplate?: (template: NoteTemplate) => void;
  onClose?: () => void;
  className?: string;
}

// 预设模板
export const defaultTemplates: NoteTemplate[] = [
  {
    id: 'blank',
    name: '空白笔记',
    description: '从零开始创建笔记',
    type: 'general',
    content: '',
    defaultTags: [],
    icon: 'file',
  },
  {
    id: 'concept',
    name: '数学概念',
    description: '记录数学概念和定义',
    type: 'concept',
    content: `# 概念名称

## 定义

在这里输入概念的精确定义...

## 数学表述

$$
\\text{数学公式}
$$

## 示例

### 例1

### 例2

## 相关概念

- 
- 

## 备注

`,
    defaultTags: ['概念', '定义'],
    icon: 'lightbulb',
  },
  {
    id: 'theorem',
    name: '定理证明',
    description: '记录定理及其证明',
    type: 'theorem',
    content: `# 定理名称

## 定理陈述

**定理**: 

$$
\\text{定理的数学表述}
$$

## 证明

**证明**: 

1. 首先...
2. 然后...
3. 因此...

$$
\\begin{aligned}
& \\text{步骤1} \\\\
& \\text{步骤2} \\\\
& \\therefore \\text{结论}
\\end{aligned}
$$

**证毕** □

## 应用

## 相关定理

- 
`,
    defaultTags: ['定理', '证明'],
    icon: 'book',
  },
  {
    id: 'example',
    name: '例题解析',
    description: '记录典型例题和解答',
    type: 'example',
    content: `# 题目

## 题目描述

## 已知条件

- 
- 

## 求解目标

## 解题思路

## 详细解答

### 步骤1: 

### 步骤2: 

### 步骤3: 

## 最终答案

$$
\\boxed{}
$$

## 方法总结

## 类似题目

`,
    defaultTags: ['例题', '解析'],
    icon: 'calculator',
  },
  {
    id: 'exercise',
    name: '练习题',
    description: '创建练习题和自测题',
    type: 'exercise',
    content: `# 练习题

## 题目

### 题目1

$$
\\text{题目内容}
$$

**选项**:
- A. 
- B. 
- C. 
- D. 

<details>
<summary>查看答案</summary>

**答案**: 

**解析**: 

</details>

### 题目2

---

## 自评

- [ ] 完全掌握
- [ ] 需要复习
- [ ] 不理解
`,
    defaultTags: ['练习', '自测'],
    icon: 'target',
  },
  {
    id: 'study-notes',
    name: '学习笔记',
    description: '课堂笔记和学习总结',
    type: 'general',
    content: `# 学习主题

## 学习目标

- 
- 

## 主要内容

### 要点1

### 要点2

### 要点3

## 关键公式

$$
\\text{公式1}
$$

$$
\\text{公式2}
$$

## 疑问与思考

1. 
2. 

## 总结

`,
    defaultTags: ['笔记', '学习'],
    icon: 'file',
  },
  {
    id: 'formula-sheet',
    name: '公式速查',
    description: '整理重要公式和定理',
    type: 'general',
    content: `# 公式速查表

## 代数

### 公式1
$$

$$

### 公式2
$$

$$

## 分析

### 极限
$$
\\lim_{x \\to a} f(x) = L
$$

### 导数
$$
f'(x) = \\lim_{h \\to 0} \\frac{f(x+h) - f(x)}{h}
$$

### 积分
$$
\\int_a^b f(x) \\, dx = F(b) - F(a)
$$

## 线性代数

### 矩阵
$$
\\det(A) = \\sum_{\\sigma \\in S_n} \\text{sgn}(\\sigma) \\prod_{i=1}^n a_{i,\\sigma(i)}
$$

## 概率统计

### 期望
$$
E[X] = \\sum_{i} x_i p_i
$$
`,
    defaultTags: ['公式', '速查'],
    icon: 'calculator',
  },
  {
    id: 'problem-solving',
    name: '解题思路',
    description: '记录解题方法和技巧',
    type: 'general',
    content: `# 解题方法: [方法名称]

## 适用场景

- 
- 

## 核心思想

## 解题步骤

1. 
2. 
3. 

## 典型案例

### 案例1

**问题**: 

**解法**: 

### 案例2

## 常见误区

1. 
2. 

## 技巧总结

`,
    defaultTags: ['方法', '技巧'],
    icon: 'lightbulb',
  },
];

// 模板图标组件
const TemplateIcon: React.FC<{ icon: string; className?: string }> = ({ icon, className = 'w-6 h-6' }) => {
  switch (icon) {
    case 'book':
      return <BookOpen className={className} />;
    case 'calculator':
      return <Calculator className={className} />;
    case 'lightbulb':
      return <Lightbulb className={className} />;
    case 'target':
      return <Target className={className} />;
    case 'file':
    default:
      return <FileText className={className} />;
  }
};

// 获取类型颜色
const getTypeColor = (type: NoteType): string => {
  switch (type) {
    case 'concept':
      return 'bg-blue-100 text-blue-700 border-blue-200';
    case 'theorem':
      return 'bg-purple-100 text-purple-700 border-purple-200';
    case 'proof':
      return 'bg-green-100 text-green-700 border-green-200';
    case 'example':
      return 'bg-yellow-100 text-yellow-700 border-yellow-200';
    case 'exercise':
      return 'bg-orange-100 text-orange-700 border-orange-200';
    default:
      return 'bg-gray-100 text-gray-700 border-gray-200';
  }
};

export const NoteTemplates: React.FC<NoteTemplatesProps> = ({
  onSelectTemplate,
  onClose,
  className = '',
}) => {
  const [templates, setTemplates] = useState<NoteTemplate[]>(defaultTemplates);
  const [viewMode, setViewMode] = useState<'grid' | 'list'>('grid');
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedType, setSelectedType] = useState<NoteType | 'all'>('all');
  const [isLoading, setIsLoading] = useState(false);
  const [favorites, setFavorites] = useState<string[]>([]);

  // 加载模板
  const loadTemplates = useCallback(async () => {
    setIsLoading(true);
    try {
      const response = await fetchTemplates();
      if (response.success && response.data && response.data.length > 0) {
        setTemplates([...defaultTemplates, ...response.data]);
      }
    } catch (error) {
      console.error('Failed to load templates:', error);
    } finally {
      setIsLoading(false);
    }
  }, []);

  // 从模板创建笔记
  const handleSelectTemplate = useCallback(async (template: NoteTemplate) => {
    if (template.id === 'blank') {
      onSelectTemplate?.(template);
      return;
    }

    try {
      const response = await createNoteFromTemplate(template.id);
      if (response.success && response.data) {
        onSelectTemplate?.(template);
      }
    } catch (error) {
      console.error('Failed to create note from template:', error);
      // 如果API失败，仍然使用本地模板
      onSelectTemplate?.(template);
    }
  }, [onSelectTemplate]);

  // 切换收藏
  const toggleFavorite = useCallback((templateId: string) => {
    setFavorites((prev) =>
      prev.includes(templateId)
        ? prev.filter((id) => id !== templateId)
        : [...prev, templateId]
    );
  }, []);

  // 过滤模板
  const filteredTemplates = templates.filter((template) => {
    const matchesSearch =
      template.name.toLowerCase().includes(searchQuery.toLowerCase()) ||
      template.description.toLowerCase().includes(searchQuery.toLowerCase());
    const matchesType = selectedType === 'all' || template.type === selectedType;
    return matchesSearch && matchesType;
  });

  // 排序：收藏优先
  const sortedTemplates = [...filteredTemplates].sort((a, b) => {
    const aFav = favorites.includes(a.id) ? 1 : 0;
    const bFav = favorites.includes(b.id) ? 1 : 0;
    return bFav - aFav;
  });

  return (
    <div className={`bg-white rounded-2xl shadow-xl ${className}`}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-6 py-4 border-b border-gray-200">
        <div>
          <h2 className="text-xl font-semibold text-gray-800">选择模板</h2>
          <p className="text-sm text-gray-500 mt-1">选择一个模板快速创建笔记</p>
        </div>
        <button
          onClick={onClose}
          className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
        >
          <X className="w-5 h-5" />
        </button>
      </div>

      {/* 搜索和过滤 */}
      <div className="px-6 py-4 border-b border-gray-200 space-y-4">
        {/* 搜索框 */}
        <div className="relative">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
          <input
            type="text"
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            placeholder="搜索模板..."
            className="
              w-full pl-10 pr-4 py-2.5
              border border-gray-200 rounded-xl
              focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-transparent
              transition-all
            "
          />
        </div>

        {/* 类型过滤 */}
        <div className="flex items-center justify-between">
          <div className="flex items-center space-x-2">
            {(['all', 'concept', 'theorem', 'example', 'exercise', 'general'] as const).map(
              (type) => (
                <button
                  key={type}
                  onClick={() => setSelectedType(type)}
                  className={`
                    px-3 py-1.5 rounded-lg text-sm transition-all
                    ${
                      selectedType === type
                        ? 'bg-blue-500 text-white'
                        : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
                    }
                  `}
                >
                  {type === 'all'
                    ? '全部'
                    : type === 'concept'
                    ? '概念'
                    : type === 'theorem'
                    ? '定理'
                    : type === 'example'
                    ? '例题'
                    : type === 'exercise'
                    ? '练习'
                    : '一般'}
                </button>
              )
            )}
          </div>

          {/* 视图切换 */}
          <div className="flex items-center bg-gray-100 rounded-lg p-1">
            <button
              onClick={() => setViewMode('grid')}
              className={`
                p-1.5 rounded transition-colors
                ${viewMode === 'grid' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-500'}
              `}
            >
              <Grid className="w-4 h-4" />
            </button>
            <button
              onClick={() => setViewMode('list')}
              className={`
                p-1.5 rounded transition-colors
                ${viewMode === 'list' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-500'}
              `}
            >
              <List className="w-4 h-4" />
            </button>
          </div>
        </div>
      </div>

      {/* 模板列表 */}
      <div className="p-6 max-h-[60vh] overflow-y-auto">
        {isLoading ? (
          <div className="flex items-center justify-center py-12">
            <div className="w-8 h-8 border-4 border-blue-200 border-t-blue-500 rounded-full animate-spin" />
          </div>
        ) : sortedTemplates.length === 0 ? (
          <div className="text-center py-12">
            <Layout className="w-12 h-12 text-gray-300 mx-auto mb-4" />
            <p className="text-gray-500">没有找到匹配的模板</p>
          </div>
        ) : viewMode === 'grid' ? (
          <div className="grid grid-cols-2 gap-4">
            {sortedTemplates.map((template) => (
              <div
                key={template.id}
                onClick={() => handleSelectTemplate(template)}
                className="
                  group relative p-4 rounded-xl border-2 border-transparent
                  bg-gray-50 hover:bg-white hover:border-blue-200 hover:shadow-lg
                  cursor-pointer transition-all
                "
              >
                {/* 收藏按钮 */}
                <button
                  onClick={(e) => {
                    e.stopPropagation();
                    toggleFavorite(template.id);
                  }}
                  className={`
                    absolute top-3 right-3 p-1 rounded-lg
                    transition-colors
                    ${
                      favorites.includes(template.id)
                        ? 'text-yellow-500 bg-yellow-50'
                        : 'text-gray-300 hover:text-yellow-500 hover:bg-yellow-50'
                    }
                  `}
                >
                  <Star
                    className={`w-4 h-4 ${favorites.includes(template.id) ? 'fill-current' : ''}`}
                  />
                </button>

                {/* 图标 */}
                <div
                  className={`
                    w-12 h-12 rounded-xl flex items-center justify-center mb-3
                    ${getTypeColor(template.type)}
                  `}
                >
                  <TemplateIcon icon={template.icon || 'file'} className="w-6 h-6" />
                </div>

                {/* 信息 */}
                <h3 className="font-semibold text-gray-800 mb-1">{template.name}</h3>
                <p className="text-sm text-gray-500 line-clamp-2">{template.description}</p>

                {/* 标签 */}
                {template.defaultTags.length > 0 && (
                  <div className="flex flex-wrap gap-1 mt-3">
                    {template.defaultTags.slice(0, 2).map((tag) => (
                      <span
                        key={tag}
                        className="px-2 py-0.5 bg-gray-200 text-gray-600 text-xs rounded-full"
                      >
                        {tag}
                      </span>
                    ))}
                    {template.defaultTags.length > 2 && (
                      <span className="px-2 py-0.5 bg-gray-200 text-gray-600 text-xs rounded-full">
                        +{template.defaultTags.length - 2}
                      </span>
                    )}
                  </div>
                )}

                {/* 悬停操作 */}
                <div className="absolute bottom-3 right-3 opacity-0 group-hover:opacity-100 transition-opacity">
                  <ChevronRight className="w-5 h-5 text-blue-500" />
                </div>
              </div>
            ))}
          </div>
        ) : (
          <div className="space-y-2">
            {sortedTemplates.map((template) => (
              <div
                key={template.id}
                onClick={() => handleSelectTemplate(template)}
                className="
                  group flex items-center p-3 rounded-xl
                  bg-gray-50 hover:bg-white hover:shadow-md
                  border border-transparent hover:border-gray-200
                  cursor-pointer transition-all
                "
              >
                {/* 图标 */}
                <div
                  className={`
                    w-10 h-10 rounded-lg flex items-center justify-center mr-4
                    ${getTypeColor(template.type)}
                  `}
                >
                  <TemplateIcon icon={template.icon || 'file'} className="w-5 h-5" />
                </div>

                {/* 信息 */}
                <div className="flex-1">
                  <div className="flex items-center">
                    <h3 className="font-medium text-gray-800">{template.name}</h3>
                    {favorites.includes(template.id) && (
                      <Star className="w-3 h-3 text-yellow-500 fill-current ml-2" />
                    )}
                  </div>
                  <p className="text-sm text-gray-500">{template.description}</p>
                </div>

                {/* 标签 */}
                {template.defaultTags.length > 0 && (
                  <div className="flex items-center space-x-1 mr-4">
                    {template.defaultTags.slice(0, 2).map((tag) => (
                      <span
                        key={tag}
                        className="px-2 py-0.5 bg-gray-200 text-gray-600 text-xs rounded-full"
                      >
                        {tag}
                      </span>
                    ))}
                  </div>
                )}

                {/* 操作 */}
                <ChevronRight className="w-5 h-5 text-gray-300 group-hover:text-blue-500 transition-colors" />
              </div>
            ))}
          </div>
        )}
      </div>

      {/* 底部 */}
      <div className="px-6 py-4 border-t border-gray-200 bg-gray-50 rounded-b-2xl">
        <div className="flex items-center justify-between">
          <p className="text-sm text-gray-500">
            共 {sortedTemplates.length} 个模板
          </p>
          <button
            onClick={() => handleSelectTemplate(defaultTemplates[0])}
            className="
              flex items-center px-4 py-2
              bg-blue-500 text-white rounded-lg
              hover:bg-blue-600 transition-colors
            "
          >
            <Plus className="w-4 h-4 mr-2" />
            创建空白笔记
          </button>
        </div>
      </div>
    </div>
  );
};

export default NoteTemplates;
