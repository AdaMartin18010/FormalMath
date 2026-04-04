# 智能笔记系统 (Intelligent Note System)

## 概述

智能笔记系统是 FormalMath-Interactive 的一个核心功能模块，提供 AI 辅助的数学学习笔记管理功能。支持 Markdown 编辑、LaTeX 数学公式、AI 智能助手、笔记模板、知识图谱关联等功能。

## 功能特性

### 1. 笔记编辑器 (NoteEditor)
- **Markdown 支持**: 完整的 Markdown 语法支持
- **LaTeX 公式**: 行内公式 `$...$` 和块级公式 `$$...$$`
- **LaTeX 工具栏**: 可视化公式编辑器，包含常用数学符号和公式
- **实时预览**: 编辑/预览/分屏三种模式
- **自动保存**: 3秒自动保存，防止内容丢失
- **键盘快捷键**: Ctrl+S 保存, Ctrl+B 粗体, Ctrl+I 斜体
- **代码高亮**: 支持多种编程语言的语法高亮

### 2. AI 笔记助手 (NoteAIAssistant)
- **智能总结**: 自动生成笔记要点总结
- **深度解释**: 对选中内容进行详细解释
- **内容扩展**: 基于现有内容提供扩展建议
- **知识关联**: 推荐相关的数学概念
- **智能标签**: 自动推荐标签
- **全面分析**: 分析笔记难度、阅读时间等
- **对话式交互**: 支持与 AI 助手进行对话

### 3. 笔记模板系统 (NoteTemplates)
内置多种数学学习模板：
- **空白笔记**: 自由创作
- **数学概念**: 概念定义模板
- **定理证明**: 定理陈述与证明结构
- **例题解析**: 题目与解答模板
- **练习题**: 自测题目模板
- **学习笔记**: 课堂笔记模板
- **公式速查**: 公式整理模板
- **解题思路**: 方法总结模板

### 4. 笔记搜索 (NoteSearch)
- **全文搜索**: 支持模糊搜索和高亮显示
- **高级过滤**: 按类型、状态、标签、日期筛选
- **标签管理**: 创建、编辑、删除标签
- **排序功能**: 多种排序方式（更新时间、创建时间、标题等）

### 5. 笔记分享 (NoteShare)
- **链接分享**: 生成分享链接
- **权限控制**: 公开/密码保护/限时访问
- **协作编辑**: 允许他人协作编辑
- **评论功能**: 允许评论和讨论
- **分享统计**: 查看次数统计
- **多种格式**: 支持二维码、邮件、导出分享

### 6. 知识图谱关联 (NoteConceptGraph)
- **概念关联**: 将笔记与知识图谱中的概念关联
- **关系类型**: 定义、解释、应用、引用、扩展
- **AI 推荐**: 智能推荐相关概念
- **相关笔记**: 查找相关笔记

### 7. 笔记管理 (NoteList)
- **文件夹管理**: 支持多级文件夹结构
- **置顶/收藏**: 重要笔记管理
- **批量操作**: 批量删除、移动、标签
- **笔记列表**: 网格/列表视图

### 8. 自定义 Hooks (useNotes)
- `useNotesList`: 笔记列表管理
- `useNoteCRUD`: 笔记增删改查
- `useNoteSearch`: 搜索功能
- `useNoteTemplates`: 模板管理
- `useNoteAI`: AI 助手功能
- `useNoteShare`: 分享功能
- `useNoteImportExport`: 导入导出
- `useNoteAutoSave`: 自动保存

## 技术栈

- **前端框架**: React 18 + TypeScript
- **状态管理**: Zustand (持久化存储)
- **样式**: Tailwind CSS
- **Markdown 渲染**: react-markdown + remark-math + rehype-katex
- **数学公式**: KaTeX
- **代码高亮**: react-syntax-highlighter
- **图标**: Lucide React
- **后端 API**: Express.js + MongoDB (已有)

## 文件结构

```
src/components/Notes/
├── NoteEditor.tsx        # 笔记编辑器主组件
├── NoteAIAssistant.tsx   # AI 助手组件
├── NoteTemplates.tsx     # 笔记模板系统
├── NoteSearch.tsx        # 笔记搜索组件
├── NoteShare.tsx         # 笔记分享组件
├── NoteList.tsx          # 笔记列表组件
├── NoteConceptGraph.tsx  # 知识图谱关联
├── NotesPage.tsx         # 笔记系统主页面
├── LaTeXToolbar.tsx      # LaTeX 公式工具栏
├── index.ts              # 组件导出
└── README.md             # 本文档

src/hooks/
├── useNotes.ts           # 笔记系统综合 Hook
└── index.ts              # Hook 导出

src/services/
├── noteService.ts        # 笔记 API 服务
└── index.ts              # 服务导出

src/stores/
└── noteStore.ts          # 笔记状态管理

src/types/
└── notes.ts              # TypeScript 类型定义

server/routes/
└── notes.js              # 后端 API 路由

server/models/
└── note.js               # 数据模型
```

## 使用方法

### 基础使用

```tsx
import { NotesPage } from './components/Notes';

function App() {
  return <NotesPage />;
}
```

### 独立使用组件

```tsx
import { 
  NoteEditor, 
  NoteAIAssistant, 
  NoteTemplates,
  LaTeXToolbar 
} from './components/Notes';

// 使用编辑器
<NoteEditor noteId="note-id" />

// 使用 AI 助手
<NoteAIAssistant note={currentNote} />

// 使用模板选择器
<NoteTemplates 
  onSelectTemplate={(template) => {
    // 处理模板选择
  }}
/>

// 使用 LaTeX 工具栏
<LaTeXToolbar 
  onInsert={(latex) => {
    // 插入 LaTeX 公式
  }}
/>
```

### 使用 Hooks

```tsx
import { 
  useNotes, 
  useNoteCRUD, 
  useNoteSearch,
  useNoteAI 
} from './hooks';

// 综合使用
const notes = useNotes();

// 独立使用
const { createNewNote, updateExistingNote } = useNoteCRUD();
const { search } = useNoteSearch();
const { summarize, analyze } = useNoteAI();
```

## API 接口

后端 API 已完整实现，包括：

- **笔记 CRUD**: GET/POST/PATCH/DELETE /api/notes
- **版本历史**: /api/notes/:id/versions
- **搜索**: /api/notes/search
- **标签管理**: /api/notes/tags
- **文件夹管理**: /api/notes/folders
- **AI 助手**: /api/notes/:id/analyze, /api/notes/ai/assist
- **分享**: /api/notes/:id/share
- **知识图谱**: /api/notes/:id/concepts
- **统计**: /api/notes/statistics

详见 `server/routes/notes.js`

## 类型定义

主要类型定义在 `src/types/notes.ts`：

```typescript
interface Note {
  id: string;
  title: string;
  content: string;
  type: 'concept' | 'theorem' | 'proof' | 'example' | 'exercise' | 'general';
  status: 'draft' | 'published' | 'archived' | 'shared';
  tags: NoteTag[];
  author: { id: string; name: string; avatar?: string };
  createdAt: string;
  updatedAt: string;
  aiAnalysis?: NoteAIAnalysis;
  shareSettings?: NoteShareSettings;
  // ... 更多字段
}
```

## 未来扩展

- [ ] 支持手写公式识别
- [ ] 语音输入笔记
- [ ] 协作实时编辑
- [ ] AI 自动批改练习题
- [ ] 学习路径推荐
- [ ] 笔记导入导出更多格式 (PDF, Word)

## 贡献指南

1. 确保代码符合 TypeScript 类型规范
2. 添加必要的注释和文档
3. 遵循现有的代码风格
4. 测试所有新功能
