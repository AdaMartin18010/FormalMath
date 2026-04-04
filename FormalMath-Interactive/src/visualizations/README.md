# FormalMath Interactive - 知识图谱可视化组件

## 组件清单

### 1. D3Graph - 力导向图组件
力导向图可视化组件，支持交互式探索知识图谱。

**功能特性：**
- 力导向布局算法
- 节点拖拽交互
- 点击展开详情
- 悬停显示信息Tooltip
- 缩放与平移
- 搜索高亮匹配节点
- 多种节点类型颜色区分

**使用示例：**
```tsx
import { D3Graph } from './visualizations';

const nodes = [
  { id: '1', label: '微积分', type: 'concept', size: 30 },
  { id: '2', label: '导数', type: 'theorem', size: 25 },
  { id: '3', label: '牛顿', type: 'person', size: 20 }
];

const links = [
  { source: '1', target: '2', type: 'relates' },
  { source: '3', target: '1', type: 'proves' }
];

<D3Graph
  nodes={nodes}
  links={links}
  width={800}
  height={600}
  onNodeClick={(node) => console.log('Clicked:', node)}
  onNodeHover={(node) => console.log('Hover:', node)}
  enableZoom={true}
  enableDrag={true}
  searchQuery="导数"
/>
```

---

### 2. InteractiveTree - 交互式树组件
可折叠的树形结构可视化组件，适合展示层次化知识。

**功能特性：**
- 可折叠/展开节点
- 平滑过渡动画
- 路径高亮
- 节点详情弹窗
- 垂直/水平布局
- 层级展开控制

**使用示例：**
```tsx
import { InteractiveTree } from './visualizations';

const treeData = {
  id: 'root',
  label: '数学',
  children: [
    {
      id: 'calculus',
      label: '微积分',
      description: '研究变化的数学分支',
      children: [
        { id: 'derivative', label: '导数' },
        { id: 'integral', label: '积分' }
      ]
    },
    {
      id: 'algebra',
      label: '代数',
      children: [
        { id: 'linear', label: '线性代数' },
        { id: 'abstract', label: '抽象代数' }
      ]
    }
  ]
};

<InteractiveTree
  data={treeData}
  orientation="horizontal"
  collapsible={true}
  onNodeClick={(node) => console.log('Clicked:', node)}
  onNodeToggle={(node, expanded) => console.log('Toggled:', node, expanded)}
  highlightPath={['root', 'calculus']}
/>
```

---

### 3. MatrixTable - 矩阵对比组件
热力图矩阵可视化组件，适合对比分析数据。

**功能特性：**
- 热力图显示（sequential/diverging/categorical）
- 单元格详情Tooltip
- 行列排序
- 筛选功能
- 统计信息显示
- 自定义颜色映射

**使用示例：**
```tsx
import { MatrixTable } from './visualizations';

const headers = ['定理A', '定理B', '定理C', '定理D'];
const rowHeaders = ['概念X', '概念Y', '概念Z'];

const data = [
  [{ value: 0.8 }, { value: 0.3 }, { value: 0.9 }, { value: 0.1 }],
  [{ value: 0.4 }, { value: 0.7 }, { value: 0.2 }, { value: 0.6 }],
  [{ value: 0.9 }, { value: 0.5 }, { value: 0.3 }, { value: 0.8 }]
];

const colorScale = {
  type: 'sequential' as const,
  domain: [0, 1],
  range: ['#e3f2fd', '#1565c0']
};

<MatrixTable
  headers={headers}
  rowHeaders={rowHeaders}
  data={data}
  colorScale={colorScale}
  sortable={true}
  filterable={true}
  onCellClick={(cell, row, col) => console.log('Cell:', cell, row, col)}
  showValues={true}
/>
```

---

### 4. MermaidChart - Mermaid图表组件
支持渲染Mermaid语法的图表组件。

**功能特性：**
- 渲染多种Mermaid图表类型（flowchart、sequence、gantt等）
- 节点点击事件
- 图表缩放和平移
- SVG/PNG导出
- 多种主题支持

**使用示例：**
```tsx
import { MermaidChart } from './visualizations';

const chartCode = `
flowchart TD
    A[开始] --> B{判断}
    B -->|条件1| C[处理1]
    B -->|条件2| D[处理2]
    C --> E[结束]
    D --> E
`;

<MermaidChart
  chart={chartCode}
  interactive={true}
  theme="default"
  onNodeClick={(nodeId, data) => console.log('Node:', nodeId, data)}
  enableZoom={true}
  width={800}
  height={600}
/>
```

---

## 类型定义

所有组件的类型定义位于 `types.ts`：

```typescript
import type {
  // D3Graph
  GraphNode, GraphLink, D3GraphProps,
  
  // InteractiveTree  
  TreeNode, InteractiveTreeProps,
  
  // MatrixTable
  MatrixCell, ColorScale, MatrixTableProps,
  
  // MermaidChart
  MermaidChartProps,
  
  // 通用
  Point, Bounds, TooltipState, VisualizationTheme
} from './visualizations/types';
```

---

## 样式文件

每个组件都有对应的CSS样式文件：
- `D3Graph.css` - 力导向图样式
- `InteractiveTree.css` - 树形组件样式
- `MatrixTable.css` - 矩阵表格样式
- `MermaidChart.css` - Mermaid图表样式

支持暗色模式（通过 `prefers-color-scheme: dark` 媒体查询）

---

## 安装依赖

```bash
npm install d3 mermaid
# 或
yarn add d3 mermaid
```

TypeScript类型支持：
```bash
npm install -D @types/d3
```

---

## 完整示例

```tsx
import React, { useState } from 'react';
import { D3Graph, InteractiveTree, MatrixTable, MermaidChart } from './visualizations';

const KnowledgeGraphDemo: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'graph' | 'tree' | 'matrix' | 'mermaid'>('graph');

  return (
    <div className="knowledge-graph-demo">
      <div className="tabs">
        <button onClick={() => setActiveTab('graph')}>力导向图</button>
        <button onClick={() => setActiveTab('tree')}>树形图</button>
        <button onClick={() => setActiveTab('matrix')}>矩阵表</button>
        <button onClick={() => setActiveTab('mermaid')}>Mermaid</button>
      </div>

      <div className="visualization-container">
        {activeTab === 'graph' && <D3Graph {...graphData} />}
        {activeTab === 'tree' && <InteractiveTree {...treeData} />}
        {activeTab === 'matrix' && <MatrixTable {...matrixData} />}
        {activeTab === 'mermaid' && <MermaidChart {...mermaidData} />}
      </div>
    </div>
  );
};

export default KnowledgeGraphDemo;
```

---

## 开发团队

FormalMath Interactive Team
