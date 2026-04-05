---
title: AI智能助手集成文档
msc_primary: 00A99
processed_at: '2026-04-05'
---
# AI智能助手集成文档

本文档介绍如何在FormalMath-Interactive项目中使用AI智能助手组件。

## 目录

- [概述](#概述)
- [功能特性](#功能特性)
- [安装依赖](#安装依赖)
- [基本使用](#基本使用)
- [组件API](#组件api)
- [上下文感知](#上下文感知)
- [服务层配置](#服务层配置)
- [Hook使用](#hook使用)
- [自定义渲染](#自定义渲染)

## 概述

AI智能助手是一个集成了大语言模型的聊天组件，专为数学学习场景设计。它支持：

- 自然语言对话
- LaTeX数学公式渲染
- Lean4代码高亮
- 流式响应
- 对话历史管理
- 上下文感知

## 功能特性

### 1. 聊天界面

- 浮动窗口或侧边栏模式
- 可最小化和关闭
- 历史会话管理
- 快捷提问选项

### 2. 消息渲染

- Markdown格式支持
- 数学公式（KaTeX）
- 代码块高亮（支持Lean4）
- 逐步推导展示
- 相关概念推荐

### 3. 输入功能

- 多行文本输入
- LaTeX预览
- Enter发送 / Shift+Enter换行
- 输入状态指示

### 4. AI功能

- 流式响应（SSE）
- 对话历史管理
- 错误处理和重试
- 上下文感知

## 安装依赖

```bash
npm install react-markdown remark-math rehype-katex katex react-syntax-highlighter
npm install -D @types/react-syntax-highlighter
```

## 基本使用

### 1. 全局集成（App.tsx）

```tsx
import { ChatInterface } from '@components/AIAssistant';

function App() {
  return (
    <div className="app">
      {/* 页面内容 */}
      <ChatInterface position="floating" />
    </div>
  );
}
```

### 2. 页面级集成

```tsx
import { ChatInterface } from '@components/AIAssistant';
import type { PageContext } from '@types/aiAssistant';

function KnowledgeGraphPage() {
  const context: PageContext = {
    pageType: 'knowledge-graph',
    currentConcept: '群论',
    selectedNode: {
      id: 'group-theory',
      label: '群论',
      type: 'concept',
    },
  };

  return (
    <div>
      {/* 页面内容 */}
      <ChatInterface 
        position="right" 
        context={context}
        onMessageSend={(msg) => console.log('发送:', msg)}
      />
    </div>
  );
}
```

### 3. 使用Hook

```tsx
import { useAIAssistant } from '@hooks/useAIAssistant';

function MyComponent() {
  const {
    sessions,
    currentSession,
    isLoading,
    isStreaming,
    error,
    sendMessage,
    createSession,
    selectSession,
    deleteSession,
    quickQuestions,
  } = useAIAssistant({
    context: {
      pageType: 'knowledge-graph',
      currentConcept: '拓扑学',
    },
    enableStreaming: true,
  });

  const handleSend = async (message: string) => {
    await sendMessage(message);
  };

  return (
    <div>
      {/* 自定义UI */}
    </div>
  );
}
```

## 组件API

### ChatInterface Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| `initialOpen` | `boolean` | `false` | 初始是否打开 |
| `position` | `'right' \| 'left' \| 'floating'` | `'right'` | 位置 |
| `context` | `PageContext` | - | 页面上下文 |
| `onClose` | `() => void` | - | 关闭回调 |
| `onMessageSend` | `(message: string) => void` | - | 消息发送回调 |

### PageContext

```typescript
interface PageContext {
  pageType: 'knowledge-graph' | 'reasoning-tree' | 'mind-map' | 
            'comparison' | 'decision-tree' | 'evolution' | 'general';
  currentConcept?: string;           // 当前概念
  selectedFormulas?: string[];       // 选中的公式
  selectedNode?: {                   // 选中的节点
    id: string;
    label: string;
    type: string;
    description?: string;
  };
  learningPath?: string[];           // 学习路径
}
```

## 上下文感知

AI助手可以根据当前页面内容提供上下文感知的回答。

### 示例：知识图谱页面

```tsx
const context: PageContext = {
  pageType: 'knowledge-graph',
  currentConcept: '伽罗瓦理论',
  selectedNode: {
    id: 'galois-theory',
    label: '伽罗瓦理论',
    type: 'theorem',
    description: '连接域论和群论的重要理论',
  },
};

<ChatInterface context={context} />
```

当用户询问"请解释这个概念"时，AI会自动知道用户想了解的是"伽罗瓦理论"。

## 服务层配置

### 环境变量

```bash
# .env
VITE_AI_API_BASE_URL=/api/ai
VITE_AI_MODEL=gpt-4
```

### 自定义配置

```typescript
import { AIService } from '@services/aiService';

const aiService = new AIService({
  baseURL: '/api/ai',
  model: 'gpt-4',
  temperature: 0.7,
  maxTokens: 4096,
  enableStreaming: true,
  timeout: 60000,
  retryCount: 3,
});
```

## Hook使用

### useAIAssistant

```typescript
const {
  // 状态
  sessions,           // 所有会话
  currentSession,     // 当前会话
  isLoading,          // 是否加载中
  isStreaming,        // 是否流式输出
  error,              // 错误信息

  // 方法
  sendMessage,        // 发送消息
  createSession,      // 创建会话
  selectSession,      // 选择会话
  deleteSession,      // 删除会话
  clearAllSessions,   // 清除所有会话
  stopGeneration,     // 停止生成
  askAboutSelection,  // 询问选中内容
  sendQuickQuestion,  // 发送快捷问题

  // 数据
  quickQuestions,     // 快捷问题列表
} = useAIAssistant(options);
```

### 选中内容提问

```tsx
const { askAboutSelection } = useAIAssistant();

// 解释选中内容
await askAboutSelection('E = mc^2', 'explain');

// 证明选中公式
await askAboutSelection('费马大定理', 'prove');

// 应用示例
await askAboutSelection('欧拉公式', 'apply');

// 相关概念
await askAboutSelection('黎曼猜想', 'relate');
```

## 自定义渲染

### 自定义Markdown渲染

```tsx
import { MarkdownRenderer } from '@components/AIAssistant';

function MyComponent() {
  return (
    <MarkdownRenderer
      content="## 标题\n\n公式: $E = mc^2$"
      enableMath={true}
      enableCodeHighlight={true}
    />
  );
}
```

### 自定义消息列表

```tsx
import { MessageList } from '@components/AIAssistant';

function MyComponent() {
  const messages = [
    {
      id: '1',
      role: 'user',
      content: '什么是群论？',
      timestamp: new Date(),
    },
    {
      id: '2',
      role: 'assistant',
      content: '群论是研究代数结构"群"的数学分支...',
      timestamp: new Date(),
    },
  ];

  return (
    <MessageList
      messages={messages}
      isStreaming={false}
      onRegenerate={(id) => console.log('重新生成:', id)}
      onFeedback={(id, type) => console.log('反馈:', id, type)}
    />
  );
}
```

## 后端API规范

AI助手期望后端API遵循以下规范：

### POST /api/ai/chat

请求体：
```json
{
  "message": "用户消息",
  "sessionId": "会话ID",
  "context": { /* 页面上下文 */ },
  "history": [ /* 历史消息 */ ],
  "model": "gpt-4",
  "temperature": 0.7,
  "maxTokens": 4096
}
```

响应：
```json
{
  "message": "AI回复",
  "messageId": "消息ID",
  "metadata": {
    "relatedConcepts": ["相关概念1", "相关概念2"],
    "suggestedQuestions": ["建议问题1", "建议问题2"],
    "derivationSteps": [
      {
        "stepNumber": 1,
        "statement": "步骤描述",
        "justification": "依据",
        "latex": "$x = 1$"
      }
    ]
  }
}
```

### POST /api/ai/chat/stream

SSE流式响应：
```
data: {"content": "部分", "messageId": "msg-1"}

data: {"content": "回复", "messageId": "msg-1"}

data: [DONE]
```

## 示例场景

### 1. 公式解释

用户在知识图谱页面选中公式 `$\int_{-\infty}^{\infty} e^{-x^2} dx = \sqrt{\pi}$`，点击"解释"，AI助手会解释这个高斯积分的含义和推导过程。

### 2. 证明引导

用户在推理树页面查看定理，可以询问"请帮我理解这个证明的关键步骤"，AI助手会逐步解释证明过程。

### 3. 学习路径推荐

用户询问"我想学习代数拓扑，应该按什么顺序学习相关概念？"，AI助手会根据知识图谱推荐学习路径。

## 最佳实践

1. **上下文管理**: 在页面切换时更新context，让AI了解当前页面内容
2. **错误处理**: 使用try-catch包装sendMessage调用
3. **性能优化**: 使用useCallback缓存回调函数
4. **状态持久化**: 会话自动保存到localStorage，页面刷新后保留
5. **流式响应**: 启用流式响应提升用户体验

## 故障排除

### 公式不渲染

检查是否正确引入了KaTeX CSS：
```tsx
import 'katex/dist/katex.min.css';
```

### 代码不高亮

确保安装了react-syntax-highlighter：
```bash
npm install react-syntax-highlighter
```

### 流式响应不工作

检查后端是否正确实现了SSE接口，响应头应包含：
```
Content-Type: text/event-stream
```
