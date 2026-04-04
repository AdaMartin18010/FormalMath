# 智能笔记系统 (Smart Notes System)

## 概述

智能笔记系统是 FormalMath-Interactive 的核心功能模块，提供AI辅助的数学学习笔记管理功能。系统支持富文本编辑、LaTeX公式编辑、智能搜索、模板系统和AI助手等功能。

## 功能特性

### 1. 富文本编辑器 (NoteEditor)
- 支持 Markdown 语法
- 实时预览和分屏编辑
- 自动保存功能
- 键盘快捷键支持 (Ctrl+S 保存, Ctrl+B 粗体等)

```tsx
import { NoteEditor } from './components/Notes';

<NoteEditor noteId="note-id" className="h-full" />
```

### 2. LaTeX公式编辑 (LaTeXToolbar)
- 丰富的数学符号库
- 常用公式快捷插入
- 分类浏览（基础、运算符、微积分、希腊字母等）
- 行内公式 `$...$` 和块级公式 `$$...$$` 支持

```tsx
import { LaTeXToolbar } from './components/Notes';

<LaTeXToolbar 
  onInsert={(latex) => console.log(latex)} 
/>
```

### 3. 笔记模板系统 (NoteTemplates)
- 7种预设模板：
  - 空白笔记
  - 数学概念
  - 定理证明
  - 例题解析
  - 练习题
  - 学习笔记
  - 公式速查
  - 解题思路
- 支持自定义模板
- 模板收藏功能

```tsx
import { NoteTemplates, defaultTemplates } from './components/Notes';

<NoteTemplates
  onSelectTemplate={(template) => handleSelect(template)}
  onClose={() => setShowTemplates(false)}
/>
```

### 4. 笔记搜索功能 (NoteSearch)
- 全文搜索支持
- 高级筛选（类型、标签、状态、日期）
- 模糊匹配和高亮显示
- 标签管理

```tsx
import { NoteSearch } from './components/Notes';

<NoteSearch 
  onSearch={(results) => console.log(results)} 
/>
```

### 5. AI笔记助手 (NoteAIAssistant)
- 智能总结：自动生成笔记摘要
- 深度解释：解释选中的内容
- 内容扩展：丰富和扩展笔记
- 知识关联：关联相关概念
- 智能标签：自动推荐标签
- 全面分析：分析笔记难度和关键概念

```tsx
import { NoteAIAssistant } from './components/Notes';

<NoteAIAssistant note={currentNote} />
```

### 6. 笔记管理界面 (NotesPage)
- 三栏布局：侧边栏、笔记列表、编辑器
- 多种视图模式：列表、网格、分屏
- 文件夹和标签管理
- 收藏和置顶功能

```tsx
import { NotesPage } from './components/Notes';

<NotesPage />
```

## 状态管理

使用 Zustand 进行状态管理：

```tsx
import { useNoteStore } from './stores/noteStore';

const { 
  notes, 
  editor, 
  addNote, 
  updateNote,
  selectNote 
} = useNoteStore();
```

### 主要状态
- `notes`: 笔记列表
- `folders`: 文件夹列表
- `tags`: 标签列表
- `editor`: 编辑器状态（当前笔记、保存状态、视图模式等）
- `searchFilter`: 搜索过滤条件
- `statistics`: 统计信息

## 服务API

```tsx
import {
  fetchNotes,
  createNote,
  updateNote,
  searchNotes,
  aiAssistant,
  generateNoteSummary,
} from './services/noteService';
```

### 主要API
- `fetchNotes()`: 获取笔记列表
- `createNote(data)`: 创建新笔记
- `updateNote(id, updates)`: 更新笔记
- `searchNotes(query, filters)`: 搜索笔记
- `aiAssistant(request)`: AI助手请求
- `generateNoteSummary(noteId)`: 生成笔记摘要

## 类型定义

```tsx
import type { 
  Note, 
  NoteType, 
  NoteStatus, 
  NoteTag,
  NoteFolder,
  NoteTemplate,
  NoteAIRequest,
  NoteAIResponse,
} from './types/notes';
```

## 使用示例

### 基础使用
```tsx
import { BasicExample } from './components/Notes/examples';

function App() {
  return <BasicExample />;
}
```

### 仅编辑器
```tsx
import { EditorOnlyExample } from './components/Notes/examples';

function App() {
  return <EditorOnlyExample />;
}
```

### LaTeX公式编辑
```tsx
import { LaTeXExample } from './components/Notes/examples';

function App() {
  return <LaTeXExample />;
}
```

### AI助手
```tsx
import { AIAssistantExample } from './components/Notes/examples';

function App() {
  return <AIAssistantExample />;
}
```

### 完整功能
```tsx
import { FullFeatureExample } from './components/Notes/examples';

function App() {
  return <FullFeatureExample />;
}
```

## 文件结构

```
src/
├── components/
│   └── Notes/
│       ├── NoteEditor.tsx         # 笔记编辑器
│       ├── NoteList.tsx           # 笔记列表
│       ├── NoteSearch.tsx         # 笔记搜索
│       ├── NoteTemplates.tsx      # 笔记模板
│       ├── LaTeXToolbar.tsx       # LaTeX工具栏
│       ├── NoteAIAssistant.tsx    # AI笔记助手
│       ├── NotesPage.tsx          # 笔记主页面
│       ├── NoteShare.tsx          # 笔记分享
│       ├── NoteConceptGraph.tsx   # 概念图谱
│       ├── index.ts               # 组件导出
│       └── examples/
│           ├── BasicExample.tsx   # 基础示例
│           └── index.ts           # 示例导出
├── stores/
│   └── noteStore.ts               # 笔记状态管理
├── services/
│   └── noteService.ts             # 笔记服务API
└── types/
    └── notes.ts                   # 笔记类型定义
```

## 技术栈

- **React 18** - UI框架
- **TypeScript** - 类型系统
- **Zustand** - 状态管理
- **Tailwind CSS** - 样式系统
- **React Markdown** - Markdown渲染
- **KaTeX** - LaTeX公式渲染
- **Lucide React** - 图标库
- **Axios** - HTTP客户端

## 键盘快捷键

| 快捷键 | 功能 |
|--------|------|
| Ctrl+S | 保存笔记 |
| Ctrl+B | 粗体 |
| Ctrl+I | 斜体 |
| Enter | 发送AI消息 |
| Shift+Enter | AI消息换行 |

## 贡献指南

1. Fork 项目
2. 创建功能分支 (`git checkout -b feature/AmazingFeature`)
3. 提交更改 (`git commit -m 'Add some AmazingFeature'`)
4. 推送到分支 (`git push origin feature/AmazingFeature`)
5. 创建 Pull Request

## 许可证

MIT License
