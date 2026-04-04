/**
 * FormalMath 可视化组件库展示页面
 * 展示所有高级可视化组件的用法和效果
 */

import React, { useState, useCallback } from 'react';
import { 
  ConceptTimeline, GraphComparison, PathAnimation, 
  ProofTreeViz, AssociationHeatmap 
} from '@visualizations';
import type { 
  TimelineEvent, ConceptStage, GraphNode, GraphLink,
  PathNode, PathConnection, ProofNode, AssociationData 
} from '@visualizations';
import { 
  LayoutDashboard, GitBranch, Route, GitCompare, 
  Flame, Calendar, ChevronRight 
} from 'lucide-react';

// 示例数据生成器
const generateTimelineData = (): { events: TimelineEvent[]; stages: ConceptStage[] } => {
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
    {
      id: '2',
      date: new Date(1637, 0, 1),
      year: 1637,
      title: '解析几何的诞生',
      description: '引入坐标系，将几何与代数统一',
      type: 'discovery',
      mathematician: '笛卡尔',
      conceptId: 'analytic-geometry',
      impact: 9,
    },
    {
      id: '3',
      date: new Date(1854, 0, 1),
      year: 1854,
      title: '黎曼几何',
      description: '非欧几何的重要分支，为相对论奠定基础',
      type: 'extension',
      mathematician: '黎曼',
      conceptId: 'riemannian-geometry',
      impact: 10,
    },
    {
      id: '4',
      date: new Date(1915, 0, 1),
      year: 1915,
      title: '广义相对论',
      description: '黎曼几何在物理学中的革命性应用',
      type: 'application',
      mathematician: '爱因斯坦',
      conceptId: 'general-relativity',
      impact: 10,
    },
    {
      id: '5',
      date: new Date(1950, 0, 1),
      year: 1950,
      title: '微分几何的现代化',
      description: '纤维丛理论的发展',
      type: 'extension',
      mathematician: '陈省身',
      conceptId: 'differential-geometry',
      impact: 8,
    },
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
    {
      id: 's2',
      conceptId: 'analytic-geometry',
      name: '解析时期',
      startDate: new Date(1600, 0, 1),
      endDate: new Date(1850, 0, 1),
      description: '代数方法的引入',
      maturity: 'refined',
      keyContributors: ['笛卡尔', '费马'],
    },
    {
      id: 's3',
      conceptId: 'modern-geometry',
      name: '现代时期',
      startDate: new Date(1850, 0, 1),
      description: '抽象化和公理化',
      maturity: 'developing',
      keyContributors: ['黎曼', '陈省身'],
    },
  ];

  return { events, stages };
};

const generateGraphData = (): { nodes: GraphNode[]; edges: GraphLink[] } => {
  const nodes: GraphNode[] = [
    { id: '1', label: '群论', type: 'concept' },
    { id: '2', label: '环论', type: 'concept' },
    { id: '3', label: '域论', type: 'concept' },
    { id: '4', label: '线性代数', type: 'concept' },
    { id: '5', label: '伽罗瓦理论', type: 'theorem' },
    { id: '6', label: '多项式', type: 'concept' },
  ];

  const edges: GraphLink[] = [
    { source: '1', target: '2', type: 'relates' },
    { source: '2', target: '3', type: 'relates' },
    { source: '4', target: '1', type: 'relates' },
    { source: '3', target: '5', type: 'proves' },
    { source: '6', target: '3', type: 'relates' },
  ];

  return { nodes, edges };
};

const generatePathData = (): { nodes: PathNode[]; connections: PathConnection[] } => {
  const nodes: PathNode[] = [
    { id: '1', conceptId: 'c1', label: '集合论', x: 100, y: 300, status: 'completed', mastery: 100, difficulty: 3, estimatedTime: 60, prerequisites: [], isMilestone: true },
    { id: '2', conceptId: 'c2', label: '逻辑', x: 250, y: 300, status: 'completed', mastery: 100, difficulty: 4, estimatedTime: 90, prerequisites: ['1'] },
    { id: '3', conceptId: 'c3', label: '数论', x: 400, y: 200, status: 'in_progress', mastery: 60, difficulty: 6, estimatedTime: 120, prerequisites: ['2'] },
    { id: '4', conceptId: 'c4', label: '代数', x: 400, y: 400, status: 'available', mastery: 0, difficulty: 7, estimatedTime: 150, prerequisites: ['2'] },
    { id: '5', conceptId: 'c5', label: '分析', x: 550, y: 300, status: 'locked', mastery: 0, difficulty: 8, estimatedTime: 180, prerequisites: ['3', '4'], isMilestone: true },
    { id: '6', conceptId: 'c6', label: '拓扑', x: 700, y: 300, status: 'locked', mastery: 0, difficulty: 9, estimatedTime: 200, prerequisites: ['5'], isShortcut: true },
  ];

  const connections: PathConnection[] = [
    { from: '1', to: '2', type: 'required' },
    { from: '2', to: '3', type: 'required' },
    { from: '2', to: '4', type: 'recommended' },
    { from: '3', to: '5', type: 'required' },
    { from: '4', to: '5', type: 'required' },
    { from: '5', to: '6', type: 'shortcut' },
  ];

  return { nodes, connections };
};

const generateProofTreeData = (): ProofNode => {
  return {
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
        children: [
          {
            id: 'p1-1',
            label: '谷山-志村猜想',
            type: 'axiom',
            status: 'axiomatic',
            statement: '每条椭圆曲线都是模的',
            depth: 2,
          },
        ],
      },
      {
        id: 'p2',
        label: '伽罗瓦表示',
        type: 'lemma',
        status: 'proven',
        statement: '伽罗瓦群的表示理论',
        depth: 1,
      },
      {
        id: 'p3',
        label: '岩泽理论',
        type: 'lemma',
        status: 'proven',
        statement: 'p进L函数的理论',
        depth: 1,
      },
    ],
  };
};

const generateAssociationData = (): AssociationData => {
  const concepts = ['群', '环', '域', '向量空间', '模', '代数', '拓扑', '流形', '范畴', '函子'];
  
  // 生成对称关联矩阵
  const matrix: number[][] = concepts.map((_, i) => 
    concepts.map((_, j) => {
      if (i === j) return 1;
      // 模拟一些关联模式
      const baseStrength = Math.random() * 0.5;
      const proximityBonus = Math.abs(i - j) < 3 ? 0.3 : 0;
      return Math.min(1, baseStrength + proximityBonus);
    })
  );

  // 对称化
  for (let i = 0; i < concepts.length; i++) {
    for (let j = i + 1; j < concepts.length; j++) {
      matrix[j][i] = matrix[i][j];
    }
  }

  return { concepts, matrix };
};

// 组件卡片
const ComponentCard: React.FC<{
  title: string;
  description: string;
  icon: React.ReactNode;
  children: React.ReactNode;
}> = ({ title, description, icon, children }) => (
  <div className="bg-white rounded-xl shadow-sm border border-gray-200 overflow-hidden">
    <div className="px-6 py-4 border-b border-gray-100 bg-gradient-to-r from-gray-50 to-white">
      <div className="flex items-center gap-3">
        <div className="p-2 bg-blue-100 rounded-lg">
          {icon}
        </div>
        <div>
          <h3 className="font-semibold text-gray-800">{title}</h3>
          <p className="text-sm text-gray-500">{description}</p>
        </div>
      </div>
    </div>
    <div className="p-4">
      {children}
    </div>
  </div>
);

// 主页面
const VisualizationGallery: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'all' | 'timeline' | 'comparison' | 'path' | 'proof' | 'heatmap'>('all');
  
  const timelineData = React.useMemo(generateTimelineData, []);
  const graphAData = React.useMemo(generateGraphData, []);
  const graphBData = React.useMemo(() => {
    const data = generateGraphData();
    // 修改部分节点模拟差异
    data.nodes[2].label = '体论';
    data.nodes.push({ id: '7', label: '模论', type: 'concept' });
    return data;
  }, []);
  const pathData = React.useMemo(generatePathData, []);
  const proofTreeData = React.useMemo(generateProofTreeData, []);
  const associationData = React.useMemo(generateAssociationData, []);

  const tabs = [
    { id: 'all', label: '全部', icon: LayoutDashboard },
    { id: 'timeline', label: '时间线', icon: Calendar },
    { id: 'comparison', label: '对比', icon: GitCompare },
    { id: 'path', label: '路径', icon: Route },
    { id: 'proof', label: '证明树', icon: GitBranch },
    { id: 'heatmap', label: '热力图', icon: Flame },
  ];

  return (
    <div className="min-h-screen bg-gray-50">
      {/* 头部 */}
      <div className="bg-white border-b border-gray-200">
        <div className="max-w-7xl mx-auto px-6 py-8">
          <h1 className="text-3xl font-bold text-gray-900">知识图谱可视化 2.0</h1>
          <p className="mt-2 text-gray-600">FormalMath Interactive 高级可视化组件库</p>
          
          {/* 标签导航 */}
          <div className="mt-6 flex flex-wrap gap-2">
            {tabs.map((tab) => (
              <button
                key={tab.id}
                onClick={() => setActiveTab(tab.id as any)}
                className={`flex items-center gap-2 px-4 py-2 rounded-lg text-sm font-medium transition-colors ${
                  activeTab === tab.id
                    ? 'bg-blue-500 text-white'
                    : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
                }`}
              >
                <tab.icon className="w-4 h-4" />
                {tab.label}
              </button>
            ))}
          </div>
        </div>
      </div>

      {/* 内容区域 */}
      <div className="max-w-7xl mx-auto px-6 py-8">
        <div className="space-y-8">
          {/* 概念演化时间线 */}
          {(activeTab === 'all' || activeTab === 'timeline') && (
            <ComponentCard
              title="ConceptTimeline - 概念演化时间线"
              description="展示数学概念随时间的演化历程和发展阶段"
              icon={<Calendar className="w-5 h-5 text-blue-600" />}
            >
              <ConceptTimeline
                events={timelineData.events}
                stages={timelineData.stages}
                width={1000}
                height={500}
                onEventClick={(event) => console.log('Event clicked:', event)}
              />
            </ComponentCard>
          )}

          {/* 知识图谱对比 */}
          {(activeTab === 'all' || activeTab === 'comparison') && (
            <ComponentCard
              title="GraphComparison - 知识图谱对比视图"
              description="并排对比两个知识图谱的差异和相似性"
              icon={<GitCompare className="w-5 h-5 text-blue-600" />}
            >
              <GraphComparison
                graphA={graphAData}
                graphB={graphBData}
                titleA="代数基础"
                titleB="代数进阶"
                width={1000}
                height={500}
                mode="side-by-side"
                onNodeClick={(match) => console.log('Match clicked:', match)}
              />
            </ComponentCard>
          )}

          {/* 学习路径动画 */}
          {(activeTab === 'all' || activeTab === 'path') && (
            <ComponentCard
              title="PathAnimation - 学习路径动画"
              description="动态展示学习路径的探索和推荐过程"
              icon={<Route className="w-5 h-5 text-blue-600" />}
            >
              <PathAnimation
                nodes={pathData.nodes}
                connections={pathData.connections}
                width={900}
                height={500}
                showParticles={true}
                onNodeClick={(node) => console.log('Node clicked:', node)}
              />
            </ComponentCard>
          )}

          {/* 定理证明树 */}
          {(activeTab === 'all' || activeTab === 'proof') && (
            <ComponentCard
              title="ProofTreeViz - 定理证明树可视化"
              description="交互式展示定理证明的结构和推理过程"
              icon={<GitBranch className="w-5 h-5 text-blue-600" />}
            >
              <ProofTreeViz
                root={proofTreeData}
                width={1000}
                height={600}
                orientation="vertical"
                showStepByStep={false}
                onNodeClick={(node) => console.log('Proof node clicked:', node)}
              />
            </ComponentCard>
          )}

          {/* 概念关联热力图 */}
          {(activeTab === 'all' || activeTab === 'heatmap') && (
            <ComponentCard
              title="AssociationHeatmap - 概念关联强度热力图"
              description="可视化展示概念之间的关联强度和模式"
              icon={<Flame className="w-5 h-5 text-blue-600" />}
            >
              <AssociationHeatmap
                data={associationData}
                width={800}
                height={600}
                mode="matrix"
                enableClustering={true}
                threshold={0.3}
                onCellClick={(a, b, strength) => console.log('Cell clicked:', a, b, strength)}
              />
            </ComponentCard>
          )}
        </div>

        {/* 特性说明 */}
        <div className="mt-12 grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
          <div className="bg-white rounded-lg p-6 border border-gray-200">
            <div className="w-10 h-10 bg-blue-100 rounded-lg flex items-center justify-center mb-4">
              <LayoutDashboard className="w-5 h-5 text-blue-600" />
            </div>
            <h3 className="font-semibold text-gray-800 mb-2">5个高级组件</h3>
            <p className="text-sm text-gray-600">
              提供概念时间线、图谱对比、路径动画、证明树和关联热力图等高级可视化能力
            </p>
          </div>
          
          <div className="bg-white rounded-lg p-6 border border-gray-200">
            <div className="w-10 h-10 bg-green-100 rounded-lg flex items-center justify-center mb-4">
              <GitBranch className="w-5 h-5 text-green-600" />
            </div>
            <h3 className="font-semibold text-gray-800 mb-2">D3.js驱动</h3>
            <p className="text-sm text-gray-600">
              基于D3.js构建，支持力导向图、树形布局、网络图等多种可视化形式
            </p>
          </div>
          
          <div className="bg-white rounded-lg p-6 border border-gray-200">
            <div className="w-10 h-10 bg-purple-100 rounded-lg flex items-center justify-center mb-4">
              <ChevronRight className="w-5 h-5 text-purple-600" />
            </div>
            <h3 className="font-semibold text-gray-800 mb-2">交互丰富</h3>
            <p className="text-sm text-gray-600">
              支持缩放、拖拽、点击、悬停提示、动画播放等丰富的交互功能
            </p>
          </div>
        </div>
      </div>
    </div>
  );
};

export default VisualizationGallery;
