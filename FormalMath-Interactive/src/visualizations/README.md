---
title: FormalMath 可视化组件库 v2.0
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 可视化组件库 v2.0

FormalMath Interactive 高级可视化组件库，基于 React + TypeScript + D3.js 构建。

## 组件清单

### 基础组件

| 组件 | 文件 | 说明 |
|------|------|------|
| D3Graph | `D3Graph.tsx` | 力导向知识图谱 |
| Graph3D | `Graph3D.tsx` | 3D 知识图谱 |
| InteractiveTree | `InteractiveTree.tsx` | 交互式树形图 |
| MatrixTable | `MatrixTable.tsx` | 矩阵对比表 |
| MermaidChart | `MermaidChart.tsx` | Mermaid 图表 |

### 高级组件 v2.0

| 组件 | 文件 | 说明 |
|------|------|------|
| **ConceptTimeline** | `ConceptTimeline.tsx` | 概念演化时间线 |
| **GraphComparison** | `GraphComparison.tsx` | 知识图谱对比视图 |
| **PathAnimation** | `PathAnimation.tsx` | 学习路径动画 |
| **ProofTreeViz** | `ProofTreeViz.tsx` | 定理证明树可视化 |
| **AssociationHeatmap** | `AssociationHeatmap.tsx` | 概念关联强度热力图 |

## 快速开始

```tsx
import { ConceptTimeline, GraphComparison, PathAnimation } from '@visualizations';

function MyComponent() {
  return (
    <>
      <ConceptTimeline events={events} stages={stages} />
      <GraphComparison graphA={graphA} graphB={graphB} />
      <PathAnimation nodes={nodes} connections={connections} />
    </>
  );
}
```

## 文件结构

```
visualizations/
├── index.ts              # 统一导出
├── types.ts              # 类型定义
├── README.md             # 本文档
│
├── D3Graph.tsx           # 基础力导向图
├── Graph3D.tsx           # 3D图谱
├── InteractiveTree.tsx   # 交互式树
├── MatrixTable.tsx       # 矩阵表
├── MermaidChart.tsx      # Mermaid图表
│
├── ConceptTimeline.tsx   # 概念演化时间线 ⭐NEW
├── GraphComparison.tsx   # 图谱对比 ⭐NEW
├── PathAnimation.tsx     # 路径动画 ⭐NEW
├── ProofTreeViz.tsx      # 证明树 ⭐NEW
└── AssociationHeatmap.tsx # 关联热力图 ⭐NEW
```

## 特性

- 🎨 **丰富的可视化类型**: 时间线、对比、动画、树形、热力图
- ⚡ **高性能渲染**: 基于 D3.js 优化
- 🎯 **TypeScript 支持**: 完整的类型定义
- 📱 **响应式设计**: 适配各种屏幕尺寸
- 🎬 **动画效果**: 流畅的过渡和交互动画
- 🔧 **高度可定制**: 丰富的配置选项

## 文档

详细使用文档请参阅: `docs/Visualization-v2-Guide.md`

## 更新日志

### v2.0.0 (2026-04-04)

- ✨ 新增 5 个高级可视化组件
- 📚 添加完整类型定义
- 📝 编写详细使用文档
- 🎨 创建示例展示页面
