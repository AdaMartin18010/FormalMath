/**
 * 知识网络分析组件
 * 可视化展示知识图谱结构和掌握情况
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import * as d3 from 'd3';
import type { KnowledgeNetworkData, KnowledgeNode, KnowledgeEdge, KnowledgeCommunity, BridgeConcept } from '@types/analytics';

interface KnowledgeNetworkProps {
  data: KnowledgeNetworkData;
  onNodeClick?: (node: KnowledgeNode) => void;
  className?: string;
}

/**
 * 知识网络分析组件
 */
export const KnowledgeNetwork: React.FC<KnowledgeNetworkProps> = ({
  data,
  onNodeClick,
  className = '',
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const [selectedCommunity, setSelectedCommunity] = useState<string | 'all'>('all');
  const [showOnlyKnown, setShowOnlyKnown] = useState(false);
  const [hoveredNode, setHoveredNode] = useState<KnowledgeNode | null>(null);
  const [viewMode, setViewMode] = useState<'network' | 'communities' | 'bridges'>('network');

  // D3 渲染
  useEffect(() => {
    if (!svgRef.current || data.nodes.length === 0) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const width = svgRef.current.clientWidth;
    const height = 500;

    svg.attr('height', height);

    // 过滤节点
    let filteredNodes = data.nodes;
    if (selectedCommunity !== 'all') {
      const community = data.communities.find((c) => c.id === selectedCommunity);
      if (community) {
        filteredNodes = data.nodes.filter((n) => community.conceptIds.includes(n.conceptId));
      }
    }
    if (showOnlyKnown) {
      filteredNodes = filteredNodes.filter((n) => n.masteryLevel > 0);
    }

    const nodeIds = new Set(filteredNodes.map((n) => n.id));
    const filteredEdges = data.edges.filter((e) => nodeIds.has(e.source) && nodeIds.has(e.target));

    // 创建力导向模拟
    const simulation = d3
      .forceSimulation(filteredNodes as any)
      .force(
        'link',
        d3.forceLink(filteredEdges).id((d: any) => d.id).distance(80)
      )
      .force('charge', d3.forceManyBody().strength(-200))
      .force('center', d3.forceCenter(width / 2, height / 2))
      .force('collision', d3.forceCollide().radius(30));

    // 容器组
    const g = svg.append('g');

    // 缩放行为
    const zoom = d3
      .zoom()
      .scaleExtent([0.1, 4])
      .on('zoom', (event) => {
        g.attr('transform', event.transform);
      });

    svg.call(zoom as any);

    // 绘制连线
    const links = g
      .append('g')
      .attr('class', 'links')
      .selectAll('line')
      .data(filteredEdges)
      .enter()
      .append('line')
      .attr('stroke', (d) => (d.userKnown ? '#22c55e' : '#9ca3af'))
      .attr('stroke-width', (d) => Math.sqrt(d.strength * 3))
      .attr('stroke-opacity', 0.6)
      .attr('stroke-dasharray', (d) => (d.type === 'prerequisite' ? '0' : '5,5'));

    // 绘制节点
    const nodes = g
      .append('g')
      .attr('class', 'nodes')
      .selectAll('g')
      .data(filteredNodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .style('cursor', 'pointer')
      .call(
        d3
          .drag()
          .on('start', (event, d: any) => {
            if (!event.active) simulation.alphaTarget(0.3).restart();
            d.fx = d.x;
            d.fy = d.y;
          })
          .on('drag', (event, d: any) => {
            d.fx = event.x;
            d.fy = event.y;
          })
          .on('end', (event, d: any) => {
            if (!event.active) simulation.alphaTarget(0);
            d.fx = null;
            d.fy = null;
          }) as any
      );

    // 节点圆形
    nodes
      .append('circle')
      .attr('r', (d) => d.size)
      .attr('fill', (d) => d.color)
      .attr('stroke', '#fff')
      .attr('stroke-width', 2)
      .attr('opacity', (d) => (d.masteryLevel > 0 ? 1 : 0.5));

    // 掌握度指示环
    nodes
      .append('circle')
      .attr('r', (d) => d.size + 3)
      .attr('fill', 'none')
      .attr('stroke', (d) => {
        if (d.masteryLevel >= 80) return '#22c55e';
        if (d.masteryLevel >= 50) return '#eab308';
        if (d.masteryLevel > 0) return '#f97316';
        return '#9ca3af';
      })
      .attr('stroke-width', 2)
      .attr('opacity', 0.8);

    // 节点标签
    nodes
      .append('text')
      .text((d) => d.label)
      .attr('x', 0)
      .attr('y', (d) => d.size + 15)
      .attr('text-anchor', 'middle')
      .style('font-size', '11px')
      .style('font-weight', '500')
      .style('fill', '#374151')
      .style('pointer-events', 'none');

    // 交互事件
    nodes
      .on('click', (_, d) => onNodeClick?.(d))
      .on('mouseenter', (_, d) => setHoveredNode(d))
      .on('mouseleave', () => setHoveredNode(null));

    // 更新位置
    simulation.on('tick', () => {
      links
        .attr('x1', (d: any) => d.source.x)
        .attr('y1', (d: any) => d.source.y)
        .attr('x2', (d: any) => d.target.x)
        .attr('y2', (d: any) => d.target.y);

      nodes.attr('transform', (d: any) => `translate(${d.x},${d.y})`);
    });

    return () => {
      simulation.stop();
    };
  }, [data, selectedCommunity, showOnlyKnown, onNodeClick]);

  return (
    <div className={`bg-white dark:bg-slate-800 rounded-xl shadow-lg ${className}`}>
      {/* 头部 */}
      <div className="p-4 border-b border-gray-200 dark:border-slate-700">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <div>
            <h3 className="text-lg font-semibold text-gray-800 dark:text-gray-200">知识网络分析</h3>
            <p className="text-sm text-gray-500 dark:text-gray-400 mt-1">
              {data.networkStats.totalNodes} 个概念, {data.networkStats.totalEdges} 个连接
            </p>
          </div>

          {/* 视图切换 */}
          <div className="flex bg-gray-100 dark:bg-slate-700 rounded-lg p-1">
            {[
              { key: 'network', label: '网络图' },
              { key: 'communities', label: '知识社群' },
              { key: 'bridges', label: '关键概念' },
            ].map((view) => (
              <button
                key={view.key}
                onClick={() => setViewMode(view.key as typeof viewMode)}
                className={`px-3 py-1.5 text-sm rounded-md transition-colors ${
                  viewMode === view.key
                    ? 'bg-white dark:bg-slate-600 text-blue-600 dark:text-blue-400 shadow-sm'
                    : 'text-gray-600 dark:text-gray-400 hover:text-gray-900 dark:hover:text-gray-200'
                }`}
              >
                {view.label}
              </button>
            ))}
          </div>
        </div>

        {/* 筛选器 */}
        {viewMode === 'network' && (
          <div className="flex flex-wrap gap-3 mt-3">
            <select
              value={selectedCommunity}
              onChange={(e) => setSelectedCommunity(e.target.value)}
              className="px-3 py-1.5 text-sm border border-gray-300 dark:border-slate-600 rounded-lg 
                       bg-white dark:bg-slate-700 text-gray-700 dark:text-gray-300
                       focus:outline-none focus:ring-2 focus:ring-blue-500"
            >
              <option value="all">全部分类</option>
              {data.communities.map((c) => (
                <option key={c.id} value={c.id}>
                  {c.name} ({c.conceptIds.length})
                </option>
              ))}
            </select>

            <label className="flex items-center gap-2 text-sm text-gray-700 dark:text-gray-300 cursor-pointer">
              <input
                type="checkbox"
                checked={showOnlyKnown}
                onChange={(e) => setShowOnlyKnown(e.target.checked)}
                className="rounded border-gray-300 text-blue-600 focus:ring-blue-500"
              />
              仅显示已学概念
            </label>
          </div>
        )}
      </div>

      {/* 内容区域 */}
      <div className="p-4">
        {viewMode === 'network' && (
          <>
            <div className="relative border border-gray-200 dark:border-slate-700 rounded-lg overflow-hidden">
              <svg ref={svgRef} className="w-full" />
            </div>

            {/* 图例 */}
            <div className="flex flex-wrap gap-4 mt-3 text-xs text-gray-500 dark:text-gray-400">
              <span className="flex items-center gap-1">
                <span className="w-3 h-3 rounded-full border-2 border-green-500" /> 已掌握
              </span>
              <span className="flex items-center gap-1">
                <span className="w-3 h-3 rounded-full border-2 border-yellow-500" /> 学习中
              </span>
              <span className="flex items-center gap-1">
                <span className="w-3 h-3 rounded-full border-2 border-orange-500" /> 初学
              </span>
              <span className="flex items-center gap-1">
                <span className="w-3 h-3 rounded-full border-2 border-gray-400" /> 未开始
              </span>
              <span className="flex items-center gap-1">
                <span className="w-6 h-0.5 bg-green-500" /> 已连接
              </span>
              <span className="flex items-center gap-1">
                <span className="w-6 h-0.5 bg-gray-400" /> 未连接
              </span>
            </div>

            {/* 悬停信息 */}
            {hoveredNode && (
              <div className="mt-3 bg-gray-50 dark:bg-slate-700 rounded-lg p-3">
                <div className="flex items-center justify-between">
                  <h4 className="font-medium text-gray-800 dark:text-gray-200">{hoveredNode.label}</h4>
                  <span
                    className={`text-xs px-2 py-0.5 rounded-full ${
                      hoveredNode.masteryLevel >= 80
                        ? 'bg-green-100 text-green-600 dark:bg-green-900/30 dark:text-green-400'
                        : hoveredNode.masteryLevel >= 50
                        ? 'bg-yellow-100 text-yellow-600 dark:bg-yellow-900/30 dark:text-yellow-400'
                        : hoveredNode.masteryLevel > 0
                        ? 'bg-orange-100 text-orange-600 dark:bg-orange-900/30 dark:text-orange-400'
                        : 'bg-gray-100 text-gray-600 dark:bg-slate-600 dark:text-gray-400'
                    }`}
                  >
                    {hoveredNode.masteryLevel >= 80 ? '已掌握' : hoveredNode.masteryLevel >= 50 ? '熟练' : hoveredNode.masteryLevel > 0 ? '初学' : '未开始'}
                  </span>
                </div>
                <div className="text-sm text-gray-600 dark:text-gray-400 mt-1">
                  分类: {hoveredNode.category} | 连接数: {hoveredNode.connections} | 重要度: {hoveredNode.importance.toFixed(2)}
                </div>
              </div>
            )}
          </>
        )}

        {viewMode === 'communities' && <CommunitiesView communities={data.communities} />}
        {viewMode === 'bridges' && <BridgesView bridges={data.bridges} />}
      </div>

      {/* 网络统计 */}
      <div className="px-4 pb-4">
        <div className="grid grid-cols-2 md:grid-cols-4 gap-3">
          <StatBox label="网络密度" value={`${(data.networkStats.density * 100).toFixed(1)}%`} />
          <StatBox label="平均连接数" value={data.networkStats.averageDegree.toFixed(1)} />
          <StatBox label="聚类系数" value={`${(data.networkStats.clusteringCoefficient * 100).toFixed(1)}%`} />
          <StatBox label="知识覆盖率" value={`${(data.networkStats.knowledgeCoverage * 100).toFixed(1)}%`} />
        </div>
      </div>
    </div>
  );
};

// 统计框
const StatBox: React.FC<{ label: string; value: string }> = ({ label, value }) => (
  <div className="bg-gray-50 dark:bg-slate-700 rounded-lg p-3 text-center">
    <div className="text-lg font-bold text-gray-800 dark:text-gray-200">{value}</div>
    <div className="text-xs text-gray-500 dark:text-gray-400">{label}</div>
  </div>
);

// 知识社群视图
const CommunitiesView: React.FC<{ communities: KnowledgeCommunity[] }> = ({ communities }) => {
  return (
    <div className="space-y-3">
      {communities.map((community) => (
        <div key={community.id} className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
          <div className="flex items-center justify-between">
            <div className="flex items-center gap-3">
              <div
                className="w-4 h-4 rounded"
                style={{ backgroundColor: community.color }}
              />
              <h4 className="font-medium text-gray-800 dark:text-gray-200">{community.name}</h4>
            </div>
            <span className="text-sm text-gray-500 dark:text-gray-400">
              {community.conceptIds.length} 个概念
            </span>
          </div>
          
          <div className="mt-3">
            <div className="flex justify-between text-sm text-gray-600 dark:text-gray-400 mb-1">
              <span>平均掌握度</span>
              <span className="font-medium">{community.avgMastery}%</span>
            </div>
            <div className="w-full bg-gray-200 dark:bg-slate-600 rounded-full h-2">
              <div
                className="bg-blue-500 h-2 rounded-full transition-all"
                style={{ width: `${community.avgMastery}%` }}
              />
            </div>
          </div>

          <div className="mt-2 text-xs text-gray-500 dark:text-gray-400">
            内聚度: {(community.cohesion * 100).toFixed(1)}%
          </div>
        </div>
      ))}
    </div>
  );
};

// 关键概念视图
const BridgesView: React.FC<{ bridges: BridgeConcept[] }> = ({ bridges }) => {
  const getImportanceColor = (importance: BridgeConcept['importance']) => {
    const colors: Record<string, string> = {
      critical: 'bg-red-100 text-red-700 dark:bg-red-900/30 dark:text-red-400',
      important: 'bg-orange-100 text-orange-700 dark:bg-orange-900/30 dark:text-orange-400',
      minor: 'bg-blue-100 text-blue-700 dark:bg-blue-900/30 dark:text-blue-400',
    };
    return colors[importance] || colors.minor;
  };

  const getImportanceLabel = (importance: BridgeConcept['importance']) => {
    const labels: Record<string, string> = {
      critical: '关键',
      important: '重要',
      minor: '次要',
    };
    return labels[importance] || importance;
  };

  return (
    <div className="space-y-3">
      <p className="text-sm text-gray-600 dark:text-gray-400 mb-3">
        这些概念连接不同的知识领域，掌握它们有助于构建完整的知识体系。
      </p>
      
      {bridges.map((bridge) => (
        <div key={bridge.conceptId} className="bg-gray-50 dark:bg-slate-700 rounded-lg p-4">
          <div className="flex items-start justify-between">
            <div>
              <div className="flex items-center gap-2">
                <h4 className="font-medium text-gray-800 dark:text-gray-200">{bridge.conceptName}</h4>
                <span className={`text-xs px-2 py-0.5 rounded ${getImportanceColor(bridge.importance)}`}>
                  {getImportanceLabel(bridge.importance)}
                </span>
              </div>
              <div className="text-sm text-gray-600 dark:text-gray-400 mt-1">
                连接 {bridge.connectsCommunities.length} 个知识领域
              </div>
            </div>
            <div className="text-right">
              <div className="text-sm font-medium text-gray-800 dark:text-gray-200">
                {(bridge.betweenness * 100).toFixed(1)}
              </div>
              <div className="text-xs text-gray-500 dark:text-gray-400">桥接度</div>
            </div>
          </div>
          
          <div className="flex flex-wrap gap-1 mt-2">
            {bridge.connectsCommunities.map((community, idx) => (
              <span
                key={idx}
                className="text-xs px-2 py-0.5 bg-gray-200 dark:bg-slate-600 text-gray-700 dark:text-gray-300 rounded"
              >
                {community}
              </span>
            ))}
          </div>
        </div>
      ))}
    </div>
  );
};

export default KnowledgeNetwork;
