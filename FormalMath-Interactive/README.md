# FormalMath Interactive

FormalMath 交互式可视化界面框架 - 基于 React + D3.js + Mermaid.js 构建的数学知识可视化平台。

## 🚀 技术栈

- **React 18** - 现代 React 框架
- **TypeScript** - 类型安全的开发体验
- **D3.js v7** - 强大的数据可视化库
- **Mermaid.js** - 图表渲染引擎
- **React Router** - 客户端路由
- **Axios** - HTTP 客户端
- **Tailwind CSS** - 实用优先的 CSS 框架
- **Vite** - 快速的构建工具

## 📁 项目结构

```
FormalMath-Interactive/
├── public/                  # 静态资源
│   ├── index.html
│   └── assets/
├── src/
│   ├── components/          # 可复用组件
│   │   ├── Header.tsx
│   │   ├── Sidebar.tsx
│   │   ├── Footer.tsx
│   │   └── Loading.tsx
│   ├── pages/               # 页面组件
│   │   ├── Home.tsx
│   │   ├── KnowledgeGraph/
│   │   ├── ReasoningTree/
│   │   ├── MindMap/
│   │   ├── Comparison/
│   │   ├── DecisionTree/
│   │   └── Evolution/
│   ├── visualizations/      # 可视化组件
│   │   ├── D3Graph.tsx
│   │   ├── MermaidChart.tsx
│   │   ├── InteractiveTree.tsx
│   │   └── MatrixTable.tsx
│   ├── hooks/               # 自定义 Hooks
│   │   ├── useGraph.ts
│   │   ├── useMermaid.ts
│   │   ├── useD3.ts
│   │   └── useLocalStorage.ts
│   ├── utils/               # 工具函数
│   │   ├── helpers.ts
│   │   └── classNames.ts
│   ├── types/               # TypeScript 类型
│   │   └── index.ts
│   ├── api/                 # API 接口
│   │   ├── client.ts
│   │   └── graph.ts
│   ├── App.tsx
│   ├── main.tsx
│   └── index.css
├── package.json
├── tsconfig.json
├── vite.config.ts
├── tailwind.config.js
└── postcss.config.js
```

## 🛠️ 安装与运行

### 环境要求

- Node.js 18+
- npm 9+ 或 yarn 1.22+

### 安装依赖

```bash
cd FormalMath-Interactive
npm install
```

### 开发模式

```bash
npm run dev
```

应用将在 http://localhost:3000 启动

### 生产构建

```bash
npm run build
```

构建输出将位于 `dist/` 目录

### 预览生产构建

```bash
npm run preview
```

## 🎯 核心功能

### 1. 知识图谱 (Knowledge Graph)

使用 D3.js 力导向图展示数学概念之间的关联关系。

- 节点类型：概念、定理、证明、示例、应用、数学家
- 边类型：依赖、证明、使用、扩展、矛盾、影响
- 交互功能：拖拽、缩放、选择、过滤

### 2. 推理树 (Reasoning Tree)

可视化数学证明的逻辑推理结构。

- 支持层级展开/折叠
- 显示推理前提和结论
- 置信度指示

### 3. 思维导图 (Mind Map)

使用 Mermaid.js 展示数学知识的层级结构。

- 支持多种布局方式
- 可导出为 SVG
- 大纲视图切换

### 4. 对比分析 (Comparison)

并排比较不同的数学理论和方法。

- 表格视图
- 矩阵视图
- 自定义评估权重

### 5. 决策树 (Decision Tree)

基于条件判断的问题求解向导。

- 交互式问答流程
- 流程图展示
- 可重置和回退

### 6. 演化历史 (Evolution)

追溯数学理论的发展历程。

- 时间线视图
- 甘特图展示
- 网络演化动画

## 📝 开发指南

### 添加新页面

1. 在 `src/pages/` 下创建新目录和组件
2. 在 `src/App.tsx` 中添加路由
3. 在 `src/components/Header.tsx` 中添加导航链接

### 添加新的可视化组件

1. 在 `src/visualizations/` 下创建组件
2. 导出组件类型定义
3. 在页面中引入使用

### API 接口

API 客户端配置在 `src/api/client.ts`，图数据接口在 `src/api/graph.ts`。

```typescript
import { fetchKnowledgeGraph } from '@api/graph';

const { data, error } = await fetchKnowledgeGraph();
```

## 🔧 配置

### 环境变量

复制 `.env.example` 为 `.env` 并修改：

```
VITE_API_BASE_URL=http://localhost:8080/api
VITE_ENABLE_ANALYTICS=false
```

### Tailwind 配置

在 `tailwind.config.js` 中自定义主题：

```javascript
theme: {
  extend: {
    colors: {
      primary: {
        500: '#3b82f6',
      },
    },
  },
}
```

## 📄 许可证

MIT License

## 🤝 贡献

欢迎提交 Issue 和 Pull Request！
