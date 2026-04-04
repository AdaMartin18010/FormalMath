# EnhancedD3Graph - 增强版知识图谱可视化组件

高性能、可交互的知识图谱可视化组件，支持 5000+ 节点流畅渲染。

## 特性

### 核心功能

- ✨ **虚拟化渲染** - 支持 5000+ 节点，只渲染可见区域
- 🎮 **力导向参数调节** - 实时调整物理模拟参数
- 🎯 **层级聚类** - 按类型自动聚类显示
- 🔍 **筛选搜索** - 多维度节点筛选和关键词搜索
- 🎨 **现代UI设计** - 毛玻璃效果、动画过渡、深色/浅色主题
- 📊 **FPS监控** - 实时性能监控和自适应质量降级

### 性能优化

- RAF 节流渲染
- 内存优化
- 批量节点更新
- 自适应质量降级
- 节点重要性排序

## 安装

```bash
npm install d3 lucide-react
```

## 基础使用

```tsx
import { EnhancedD3Graph } from './visualizations';

function App() {
  const data = {
    nodes: [
      { id: '1', label: '群论', type: 'concept', status: 'verified' },
      { id: '2', label: '拉格朗日定理', type: 'theorem', status: 'verified' },
    ],
    edges: [
      { id: 'e1', source: '1', target: '2', type: 'proves' },
    ],
  };

  return (
    <EnhancedD3Graph
      data={data}
      width={800}
      height={600}
    />
  );
}
```

## Props 接口

```typescript
interface EnhancedD3GraphProps {
  data: GraphData;                    // 图数据
  width?: number;                     // 宽度 (默认 800)
  height?: number;                    // 高度 (默认 600)
  config?: Partial<ViewConfig>;       // 视图配置
  className?: string;                 // 自定义类名
  theme?: 'light' | 'dark';           // 主题
  onNodeClick?: (node: GraphNode) => void;      // 节点点击回调
  onEdgeClick?: (edge: GraphEdge) => void;      // 边点击回调
  onNodeHover?: (node: GraphNode | null) => void; // 节点悬停回调
  selectedNodes?: string[];           // 选中节点ID列表
  highlightPath?: string[];           // 高亮路径节点ID
  enableVirtualization?: boolean;     // 启用虚拟化 (默认 true)
  maxVisibleNodes?: number;           // 最大可见节点数 (默认 1000)
}
```

## 高级功能

### 1. 力导向参数调节

点击工具栏的「设置」按钮，可以实时调整：

- **连接距离** - 节点间理想距离 (50-300px)
- **斥力强度** - 节点间排斥力 (-1000 ~ -50)
- **碰撞半径** - 节点碰撞检测半径 (10-100px)
- **中心引力** - 向中心的牵引力 (0-0.2)
- **衰减系数** - 模拟收敛速度 (0.001-0.1)

### 2. 筛选和搜索

点击工具栏的「筛选」按钮：

```typescript
// 搜索节点
const filterState = {
  searchQuery: '群论',              // 关键词搜索
  selectedTypes: new Set(['concept', 'theorem']), // 类型筛选
  minImportance: 0.5,               // 重要性阈值
  showIsolated: false,              // 显示孤立节点
};
```

### 3. 层级聚类

组件会自动按节点类型聚类，显示聚类边界和标签。

### 4. 节点选中和高亮

```tsx
const [selectedNodes, setSelectedNodes] = useState<string[]>([]);

<EnhancedD3Graph
  data={data}
  selectedNodes={selectedNodes}
  onNodeClick={(node) => {
    setSelectedNodes(prev => 
      prev.includes(node.id) 
        ? prev.filter(id => id !== node.id)
        : [...prev, node.id]
    );
  }}
  highlightPath={['node-1', 'node-2', 'node-3']} // 高亮路径
/>
```

## 性能优化建议

### 大数据集 (>1000 节点)

```tsx
<EnhancedD3Graph
  data={largeData}
  enableVirtualization={true}     // 启用虚拟化
  maxVisibleNodes={800}           // 限制可见节点数
/>
```

### 节点重要性

为节点设置 importance 属性，高重要性节点会优先显示：

```typescript
const nodes = [
  { 
    id: '1', 
    label: '重要概念', 
    type: 'concept',
    importance: 0.9  // 0-1 重要性分数
  },
];
```

## 主题系统

支持浅色、深色两种主题：

```tsx
<EnhancedD3Graph
  data={data}
  theme="dark"  // 或 "light"
/>
```

## 工具栏功能

- 🔍 放大/缩小
- 🎯 重置视图
- 👁️ 聚焦选中节点
- 🔍 打开筛选面板
- ⚙️ 打开力导向设置
- 💾 导出 SVG
- ⛶ 全屏显示

## 性能测试

使用性能测试工具：

```tsx
import { runBenchmark, generateTestData } from './utils/performanceBenchmark';

const data = generateTestData(1000, 1.5); // 1000节点，1.5倍边数

const report = await runBenchmark(
  { nodeCounts: [100, 500, 1000], edgeRatio: 1.5 },
  async (data) => {
    // 渲染逻辑
    return { destroy: () => {} };
  }
);
```

## 浏览器兼容性

- Chrome 90+
- Firefox 88+
- Safari 14+
- Edge 90+

## 依赖

- d3 ^7.8.0
- react ^18.0.0
- lucide-react ^0.294.0

## 许可证

MIT License
