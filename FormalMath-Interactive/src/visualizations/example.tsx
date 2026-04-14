// @ts-nocheck
/**
 * FormalMath Interactive - 可视化组件使用示例
 * Knowledge Graph Visualization Examples
 */

import React, { useState } from 'react';
import { D3Graph, InteractiveTree, MatrixTable, MermaidChart } from './index';
import type { GraphNode, GraphLink, TreeNode, MatrixCell, ColorScale } from './types';

// ============================================
// 示例数据
// ============================================

// D3Graph 示例数据
const graphNodes: GraphNode[] = [
  { id: '1', label: '微积分', type: 'concept', size: 35, data: { description: '研究变化的数学分支' } },
  { id: '2', label: '导数', type: 'theorem', size: 28, data: { year: 1666 } },
  { id: '3', label: '积分', type: 'theorem', size: 28, data: { year: 1675 } },
  { id: '4', label: '牛顿', type: 'person', size: 25, data: { period: '1643-1727' } },
  { id: '5', label: '莱布尼茨', type: 'person', size: 25, data: { period: '1646-1716' } },
  { id: '6', label: '极限', type: 'concept', size: 30, data: { foundation: true } },
  { id: '7', label: '连续性', type: 'concept', size: 25 },
  { id: '8', label: '微分方程', type: 'application', size: 26 },
];

const graphLinks: GraphLink[] = [
  { source: '1', target: '2', type: 'relates', strength: 1 },
  { source: '1', target: '3', type: 'relates', strength: 1 },
  { source: '4', target: '2', type: 'proves', strength: 0.8 },
  { source: '5', target: '3', type: 'proves', strength: 0.8 },
  { source: '6', target: '1', type: 'depends', strength: 1 },
  { source: '6', target: '7', type: 'relates', strength: 0.6 },
  { source: '2', target: '8', type: 'applies', strength: 0.7 },
  { source: '3', target: '8', type: 'applies', strength: 0.7 },
  { source: '4', target: '5', type: 'references', strength: 0.4 },
];

// InteractiveTree 示例数据
const treeData: TreeNode = {
  id: 'math',
  label: '数学',
  description: '研究数量、结构、变化等概念的学科',
  expanded: true,
  color: '#4A90D9',
  children: [
    {
      id: 'analysis',
      label: '分析学',
      description: '以极限为基础研究函数、连续性等',
      children: [
        {
          id: 'calculus',
          label: '微积分',
          children: [
            { id: 'derivative', label: '微分学' },
            { id: 'integral', label: '积分学' },
            { id: 'ode', label: '常微分方程' }
          ]
        },
        {
          id: 'real-analysis',
          label: '实分析',
          children: [
            { id: 'measure', label: '测度论' },
            { id: 'lebesgue', label: '勒贝格积分' }
          ]
        }
      ]
    },
    {
      id: 'algebra',
      label: '代数学',
      description: '研究运算结构和代数系统',
      children: [
        {
          id: 'linear-algebra',
          label: '线性代数',
          children: [
            { id: 'vector', label: '向量空间' },
            { id: 'matrix', label: '矩阵论' },
            { id: 'eigen', label: '特征值理论' }
          ]
        },
        {
          id: 'abstract-algebra',
          label: '抽象代数',
          children: [
            { id: 'group', label: '群论' },
            { id: 'ring', label: '环论' },
            { id: 'field', label: '域论' }
          ]
        }
      ]
    },
    {
      id: 'geometry',
      label: '几何学',
      children: [
        { id: 'euclidean', label: '欧几里得几何' },
        { id: 'non-euclidean', label: '非欧几何' },
        { id: 'topology', label: '拓扑学' }
      ]
    }
  ]
};

// MatrixTable 示例数据
const matrixHeaders = ['概念理解', '计算能力', '证明技巧', '应用能力', '创新思维'];
const matrixRowHeaders = ['学生A', '学生B', '学生C', '学生D', '学生E', '学生F'];

const matrixData: MatrixCell[][] = [
  [{ value: 0.85 }, { value: 0.72 }, { value: 0.68 }, { value: 0.90 }, { value: 0.55 }],
  [{ value: 0.92 }, { value: 0.88 }, { value: 0.75 }, { value: 0.65 }, { value: 0.70 }],
  [{ value: 0.60 }, { value: 0.95 }, { value: 0.80 }, { value: 0.78 }, { value: 0.45 }],
  [{ value: 0.78 }, { value: 0.65 }, { value: 0.92 }, { value: 0.60 }, { value: 0.82 }],
  [{ value: 0.88 }, { value: 0.70 }, { value: 0.55 }, { value: 0.85 }, { value: 0.90 }],
  [{ value: 0.45 }, { value: 0.58 }, { value: 0.62 }, { value: 0.70 }, { value: 0.65 }],
].map(row => row.map(cell => ({
  ...cell,
  tooltip: `得分: ${(cell.value as number * 100).toFixed(0)}%`
})));

const matrixColorScale: ColorScale = {
  type: 'sequential',
  domain: [0, 1],
  range: ['#ffebee', '#ffcdd2', '#ef9a9a', '#e57373', '#ef5350', '#f44336', '#e53935', '#d32f2f', '#c62828', '#b71c1c']
};

// MermaidChart 示例数据
const mermaidFlowchart = `
flowchart TD
    A[数学基础] --> B[代数学]
    A --> C[几何学]
    A --> D[分析学]
    
    B --> B1[线性代数]
    B --> B2[抽象代数]
    
    C --> C1[欧氏几何]
    C --> C2[非欧几何]
    
    D --> D1[微积分]
    D --> D2[实分析]
    D --> D3[复分析]
    
    B1 --> E[应用数学]
    C2 --> E
    D1 --> E
    
    style A fill:#4A90D9,stroke:#333,stroke-width:2px,color:#fff
    style E fill:#27AE60,stroke:#333,stroke-width:2px,color:#fff
`;

const mermaidSequence = `
sequenceDiagram
    participant Student as 学生
    participant System as 学习系统
    participant Tutor as AI导师
    participant Knowledge as 知识图谱
    
    Student->>System: 提交问题
    System->>Knowledge: 查询相关概念
    Knowledge-->>System: 返回概念关联
    System->>Tutor: 请求解释
    Tutor->>Tutor: 生成个性化解答
    Tutor-->>System: 返回解答
    System-->>Student: 显示学习路径
`;

// ============================================
// 示例组件
// ============================================

const VisualizationExamples: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'graph' | 'tree' | 'matrix' | 'mermaid'>('graph');
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [searchQuery, setSearchQuery] = useState('');

  return (
    <div style={{ padding: '20px', maxWidth: '1200px', margin: '0 auto' }}>
      <h1 style={{ marginBottom: '8px' }}>FormalMath 知识图谱可视化组件</h1>
      <p style={{ color: '#666', marginBottom: '24px' }}>
        四个核心可视化组件，用于展示和分析数学知识图谱
      </p>

      {/* Tab 导航 */}
      <div style={{ 
        display: 'flex', 
        gap: '8px', 
        marginBottom: '20px',
        borderBottom: '2px solid #e9ecef',
        paddingBottom: '12px'
      }}>
        {[
          { key: 'graph', label: '力导向图', icon: '🕸️' },
          { key: 'tree', label: '交互式树', icon: '🌳' },
          { key: 'matrix', label: '矩阵热力图', icon: '🔥' },
          { key: 'mermaid', label: 'Mermaid图表', icon: '📊' },
        ].map(tab => (
          <button
            key={tab.key}
            onClick={() => setActiveTab(tab.key as typeof activeTab)}
            style={{
              padding: '10px 20px',
              border: 'none',
              borderRadius: '8px',
              background: activeTab === tab.key ? '#4A90D9' : '#f8f9fa',
              color: activeTab === tab.key ? '#fff' : '#495057',
              cursor: 'pointer',
              fontSize: '14px',
              fontWeight: 600,
              transition: 'all 0.2s',
              display: 'flex',
              alignItems: 'center',
              gap: '6px'
            }}
          >
            <span>{tab.icon}</span>
            {tab.label}
          </button>
        ))}
      </div>

      {/* 控制栏 */}
      {activeTab === 'graph' && (
        <div style={{ marginBottom: '16px' }}>
          <input
            type="text"
            placeholder="搜索节点..."
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            style={{
              padding: '8px 12px',
              border: '1px solid #dee2e6',
              borderRadius: '6px',
              width: '250px',
              fontSize: '14px'
            }}
          />
          {selectedNode && (
            <span style={{ marginLeft: '12px', color: '#4A90D9' }}>
              已选中: {selectedNode}
            </span>
          )}
        </div>
      )}

      {/* 可视化区域 */}
      <div style={{ 
        border: '1px solid #e9ecef', 
        borderRadius: '12px', 
        overflow: 'hidden',
        background: '#fff'
      }}>
        {activeTab === 'graph' && (
          <D3Graph
            nodes={graphNodes}
            links={graphLinks}
            width={1160}
            height={600}
            onNodeClick={(node) => setSelectedNode(node.label)}
            onNodeHover={(node) => console.log('Hover:', node?.label)}
            searchQuery={searchQuery}
            highlightNode={selectedNode || null}
          />
        )}

        {activeTab === 'tree' && (
          <InteractiveTree
            data={treeData}
            width={1160}
            height={600}
            orientation="horizontal"
            collapsible={true}
            onNodeClick={(node) => console.log('Tree node:', node.label)}
            highlightPath={['math', 'analysis', 'calculus']}
          />
        )}

        {activeTab === 'matrix' && (
          <MatrixTable
            headers={matrixHeaders}
            rowHeaders={matrixRowHeaders}
            data={matrixData}
            colorScale={matrixColorScale}
            sortable={true}
            filterable={true}
            onCellClick={(cell, row, col) => console.log('Cell:', cell, row, col)}
            showValues={true}
          />
        )}

        {activeTab === 'mermaid' && (
          <div style={{ padding: '20px' }}>
            <h3 style={{ marginBottom: '16px' }}>流程图示例</h3>
            <MermaidChart
              chart={mermaidFlowchart}
              interactive={true}
              width={1120}
              height={400}
              onNodeClick={(id, data) => console.log('Mermaid node:', id, data)}
            />
            
            <h3 style={{ marginTop: '24px', marginBottom: '16px' }}>时序图示例</h3>
            <MermaidChart
              chart={mermaidSequence}
              interactive={true}
              width={1120}
              height={350}
            />
          </div>
        )}
      </div>

      {/* 说明文档 */}
      <div style={{ 
        marginTop: '24px', 
        padding: '20px', 
        background: '#f8f9fa', 
        borderRadius: '8px',
        fontSize: '14px',
        lineHeight: '1.6'
      }}>
        <h3 style={{ marginBottom: '12px' }}>组件功能说明</h3>
        
        {activeTab === 'graph' && (
          <ul style={{ paddingLeft: '20px', color: '#495057' }}>
            <li><strong>拖拽节点：</strong>可以手动调整节点位置</li>
            <li><strong>滚轮缩放：</strong>使用鼠标滚轮放大/缩小视图</li>
            <li><strong>点击节点：</strong>选中节点并在控制台输出信息</li>
            <li><strong>搜索高亮：</strong>输入关键词高亮匹配节点</li>
            <li><strong>悬停提示：</strong>鼠标悬停显示节点详情</li>
          </ul>
        )}

        {activeTab === 'tree' && (
          <ul style={{ paddingLeft: '20px', color: '#495057' }}>
            <li><strong>折叠/展开：</strong>点击节点旁的 +/- 按钮</li>
            <li><strong>工具栏：</strong>使用顶部工具栏展开/折叠全部</li>
            <li><strong>路径高亮：</strong>数学 → 分析学 → 微积分路径已高亮</li>
            <li><strong>悬停提示：</strong>显示节点描述信息</li>
          </ul>
        )}

        {activeTab === 'matrix' && (
          <ul style={{ paddingLeft: '20px', color: '#495057' }}>
            <li><strong>热力图：</strong>颜色深浅表示数值大小</li>
            <li><strong>排序：</strong>点击列标题进行升序/降序排序</li>
            <li><strong>筛选：</strong>在筛选行输入关键词过滤</li>
            <li><strong>统计信息：</strong>顶部显示最小值、最大值、平均值</li>
          </ul>
        )}

        {activeTab === 'mermaid' && (
          <ul style={{ paddingLeft: '20px', color: '#495057' }}>
            <li><strong>多种图表：</strong>支持流程图、时序图、甘特图等</li>
            <li><strong>节点交互：</strong>点击节点触发事件</li>
            <li><strong>导出功能：</strong>支持导出 SVG 和 PNG 格式</li>
            <li><strong>缩放平移：</strong>滚轮缩放，拖拽平移</li>
          </ul>
        )}
      </div>
    </div>
  );
};

export default VisualizationExamples;
