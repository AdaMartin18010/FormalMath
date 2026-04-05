---
title: FormalMath 可视化组件库 v2.0 使用指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 可视化组件库 v2.0 使用指南

## 概述

FormalMath Interactive 可视化组件库 v2.0 提供了5个高级可视化组件，用于构建丰富的数学知识图谱可视化界面。

## 组件列表

### 1. ConceptTimeline - 概念演化时间线

展示数学概念随时间的演化历程和发展阶段。

#### 使用示例

```tsx
import { ConceptTimeline } from '@visualizations';
import type { TimelineEvent, ConceptStage } from '@visualizations';

const events: TimelineEvent[] = [
  {
    id: '1',
    date: new Date(300, 0, 1),
    year: 300,
    title: '欧几里得几何基础',
    description: '《几何原本》奠定了公理化几何的基础',
    type: 'publication',
    mathematician: '欧几里得',
    conceptId: 'euclidean-geometry',
    impact: 10,
  },
  // ...
];

const stages: ConceptStage[] = [
  {
    id: 's1',
    conceptId: 'euclidean-geometry',
    name: '古典时期',
    startDate: new Date(-300, 0, 1),
    endDate: new Date(1600, 0, 1),
    description: '几何学的奠基期',
    maturity: 'mature',
    keyContributors: ['欧几里得', '阿基米德'],
  },
  // ...
];

<ConceptTimeline
  events={events}
  stages={stages}
  width={1000}
  height={500}
  autoPlay={false}
  onEventClick={(event) => console.log('Event clicked:', event)}
  onStageClick={(stage) => console.log('Stage clicked:', stage)}
/>
```

#### Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| events | TimelineEvent[] | 必填 | 时间线事件数据 |
| stages | ConceptStage[] | [] | 概念发展阶段数据 |
| width | number | 1000 | 组件宽度 |
| height | number | 600 | 组件高度 |
| autoPlay | boolean | false | 是否自动播放 |
| onEventClick | (event) => void | - | 事件点击回调 |
| onStageClick | (stage) => void | - | 阶段点击回调 |
| highlightedConcepts | string[] | [] | 高亮显示的概念ID |

---

### 2. GraphComparison - 知识图谱对比视图

并排对比两个知识图谱的差异和相似性。

#### 使用示例

```tsx
import { GraphComparison } from '@visualizations';
import type { GraphNode, GraphLink, ComparisonMode } from '@visualizations';

const graphA = {
  nodes: [{ id: '1', label: '群论', type: 'concept' }, ...],
  edges: [{ source: '1', target: '2', type: 'relates' }, ...],
};

const graphB = {
  nodes: [{ id: '1', label: '群论', type: 'concept' }, ...],
  edges: [{ source: '1', target: '2', type: 'relates' }, ...],
};

<GraphComparison
  graphA={graphA}
  graphB={graphB}
  titleA="版本A"
  titleB="版本B"
  width={1200}
  height={600}
  mode="side-by-side"
  onNodeClick={(match) => console.log('Match:', match)}
/>
```

#### Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| graphA | { nodes, edges } | 必填 | 第一个图谱数据 |
| graphB | { nodes, edges } | 必填 | 第二个图谱数据 |
| titleA | string | '图谱 A' | 第一个图谱标题 |
| titleB | string | '图谱 B' | 第二个图谱标题 |
| mode | ComparisonMode | 'side-by-side' | 对比模式 |
| onNodeClick | (match) => void | - | 节点点击回调 |
| showStats | boolean | true | 显示统计信息 |
| showLegend | boolean | true | 显示图例 |

#### 对比模式

- `side-by-side`: 并排视图
- `overlay`: 叠加视图
- `diff`: 差异视图
- `merge`: 合并视图

---

### 3. PathAnimation - 学习路径动画

动态展示学习路径的探索和推荐过程。

#### 使用示例

```tsx
import { PathAnimation } from '@visualizations';
import type { PathNode, PathConnection } from '@visualizations';

const nodes: PathNode[] = [
  {
    id: '1',
    conceptId: 'c1',
    label: '集合论',
    x: 100,
    y: 300,
    status: 'completed',
    mastery: 100,
    difficulty: 3,
    estimatedTime: 60,
    prerequisites: [],
    isMilestone: true,
  },
  // ...
];

const connections: PathConnection[] = [
  { from: '1', to: '2', type: 'required' },
  // ...
];

<PathAnimation
  nodes={nodes}
  connections={connections}
  width={900}
  height={500}
  showParticles={true}
  autoPlay={false}
  onNodeClick={(node) => console.log('Node:', node)}
/>
```

#### Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| nodes | PathNode[] | 必填 | 路径节点数据 |
| connections | PathConnection[] | 必填 | 路径连接数据 |
| width | number | 900 | 组件宽度 |
| height | number | 600 | 组件高度 |
| autoPlay | boolean | false | 自动播放动画 |
| playbackSpeed | number | 1 | 播放速度 |
| showParticles | boolean | true | 显示粒子效果 |
| showHeatmap | boolean | false | 显示热力图背景 |
| onNodeClick | (node) => void | - | 节点点击回调 |
| onAnimationComplete | () => void | - | 动画完成回调 |

#### 节点状态

- `locked`: 未解锁
- `available`: 可学习
- `in_progress`: 学习中
- `completed`: 已完成
- `recommended`: 推荐学习

---

### 4. ProofTreeViz - 定理证明树可视化

交互式展示定理证明的结构和推理过程。

#### 使用示例

```tsx
import { ProofTreeViz } from '@visualizations';
import type { ProofNode } from '@visualizations';

const root: ProofNode = {
  id: 'root',
  label: '费马大定理',
  type: 'theorem',
  status: 'proven',
  statement: '当 n > 2 时，方程 a^n + b^n = c^n 没有正整数解',
  depth: 0,
  children: [
    {
      id: 'p1',
      label: '椭圆曲线',
      type: 'lemma',
      status: 'proven',
      statement: '特定的椭圆曲线与模形式相关联',
      depth: 1,
      children: [...],
    },
  ],
};

<ProofTreeViz
  root={root}
  width={1000}
  height={700}
  orientation="vertical"
  showStepByStep={false}
  interactive={true}
  onNodeClick={(node) => console.log('Node:', node)}
  onNodeExpand={(node, expanded) => console.log('Expanded:', expanded)}
/>
```

#### Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| root | ProofNode | 必填 | 证明树根节点 |
| width | number | 1000 | 组件宽度 |
| height | number | 700 | 组件高度 |
| orientation | 'vertical' \| 'horizontal' | 'vertical' | 布局方向 |
| showStepByStep | boolean | false | 逐步播放模式 |
| interactive | boolean | true | 启用交互 |
| onNodeClick | (node) => void | - | 节点点击回调 |
| onNodeExpand | (node, expanded) => void | - | 展开/折叠回调 |

#### 节点类型

- `theorem`: 定理
- `lemma`: 引理
- `axiom`: 公理
- `assumption`: 假设
- `conclusion`: 结论
- `contradiction`: 矛盾

#### 证明状态

- `proven`: 已证明
- `unproven`: 未证明
- `pending`: 进行中
- `invalid`: 无效
- `axiomatic`: 公理

---

### 5. AssociationHeatmap - 概念关联强度热力图

可视化展示概念之间的关联强度和模式。

#### 使用示例

```tsx
import { AssociationHeatmap } from '@visualizations';
import type { AssociationData } from '@visualizations';

const data: AssociationData = {
  concepts: ['群', '环', '域', '向量空间', '模', '代数'],
  matrix: [
    [1, 0.8, 0.6, 0.7, 0.5, 0.4],
    [0.8, 1, 0.9, 0.6, 0.7, 0.5],
    // ...
  ],
};

<AssociationHeatmap
  data={data}
  width={800}
  height={600}
  mode="matrix"
  enableClustering={true}
  threshold={0.3}
  onCellClick={(a, b, strength) => console.log(a, b, strength)}
/>
```

#### Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| data | AssociationData | 必填 | 关联数据 |
| width | number | 800 | 组件宽度 |
| height | number | 700 | 组件高度 |
| mode | HeatmapMode | 'matrix' | 显示模式 |
| threshold | number | 0.3 | 关联强度阈值 |
| enableClustering | boolean | true | 启用聚类分析 |
| showColorScale | boolean | true | 显示颜色比例尺 |
| onCellClick | (a, b, strength) => void | - | 单元格点击回调 |
| onModeChange | (mode) => void | - | 模式切换回调 |

#### 显示模式

- `matrix`: 矩阵热力图
- `clustered`: 聚类视图
- `network`: 网络图视图
- `circular`: 圆形弦图视图

---

## 快速开始

### 安装依赖

确保项目已安装以下依赖：

```bash
npm install d3 framer-motion lucide-react
```

### 导入组件

```tsx
// 导入所有组件
import { 
  ConceptTimeline, 
  GraphComparison, 
  PathAnimation, 
  ProofTreeViz, 
  AssociationHeatmap 
} from '@visualizations';

// 导入类型
import type { 
  TimelineEvent, 
  ConceptStage,
  PathNode,
  ProofNode,
  AssociationData 
} from '@visualizations';
```

### 基础用法

```tsx
function App() {
  return (
    <div className="p-8">
      <h1>知识图谱可视化</h1>
      
      <ConceptTimeline 
        events={events} 
        width={1000} 
        height={500} 
      />
      
      <GraphComparison 
        graphA={graphA} 
        graphB={graphB} 
      />
      
      <PathAnimation 
        nodes={nodes} 
        connections={connections} 
      />
      
      <ProofTreeViz 
        root={proofRoot} 
      />
      
      <AssociationHeatmap 
        data={associationData} 
      />
    </div>
  );
}
```

---

## 最佳实践

### 1. 数据处理

- 确保数据格式符合类型定义
- 对于大型数据集，考虑使用虚拟滚动或分页
- 预处理数据以提高渲染性能

### 2. 性能优化

- 使用 `React.memo` 包裹组件避免不必要的重渲染
- 对于动态更新的数据，使用 `useMemo` 缓存计算结果
- 限制同时显示的节点数量

### 3. 响应式设计

```tsx
const ResponsiveVisualization = () => {
  const containerRef = useRef<HTMLDivElement>(null);
  const [dimensions, setDimensions] = useState({ width: 800, height: 600 });

  useEffect(() => {
    const updateDimensions = () => {
      if (containerRef.current) {
        setDimensions({
          width: containerRef.current.clientWidth,
          height: containerRef.current.clientHeight,
        });
      }
    };

    window.addEventListener('resize', updateDimensions);
    updateDimensions();

    return () => window.removeEventListener('resize', updateDimensions);
  }, []);

  return (
    <div ref={containerRef} className="w-full h-[600px]">
      <ConceptTimeline
        events={events}
        width={dimensions.width}
        height={dimensions.height}
      />
    </div>
  );
};
```

### 4. 自定义样式

所有组件都支持 `className` 属性，可以使用 Tailwind CSS 进行样式定制：

```tsx
<ConceptTimeline
  events={events}
  className="rounded-xl shadow-lg border border-gray-200"
/>
```

---

## 示例页面

项目包含一个完整的示例页面，展示了所有组件的用法：

```bash
# 启动开发服务器
npm run dev

# 访问示例页面
open http://localhost:5173/visualization-gallery
```

---

## API 参考

详见源码中的类型定义文件：`src/visualizations/types.ts`

---

## 更新日志

### v2.0.0 (2026-04-04)

- 新增 ConceptTimeline 组件
- 新增 GraphComparison 组件
- 新增 PathAnimation 组件
- 新增 ProofTreeViz 组件
- 新增 AssociationHeatmap 组件
- 统一类型定义和导出
- 添加完整的文档和示例
