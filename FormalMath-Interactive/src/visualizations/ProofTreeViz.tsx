/**
 * FormalMath 定理证明树可视化组件
 * 交互式展示定理证明的结构和推理过程
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import * as d3 from 'd3';
import { 
  GitBranch, Check, X, AlertCircle, ChevronRight, 
  ChevronDown, BookOpen, Search, Filter, Download,
  Maximize2, Minimize2, RotateCcw, Zap
} from 'lucide-react';
import { cn } from '@utils/classNames';

// 证明节点类型
export type ProofNodeType = 'theorem' | 'lemma' | 'axiom' | 'assumption' | 'conclusion' | 'contradiction';

// 证明状态
export type ProofStatus = 'proven' | 'unproven' | 'pending' | 'invalid' | 'axiomatic';

// 证明节点
export interface ProofNode {
  id: string;
  label: string;
  type: ProofNodeType;
  status: ProofStatus;
  statement: string;
  proof?: string;
  children?: ProofNode[];
  parentId?: string;
  depth: number;
  confidence?: number; // 0-1
  usedAxioms?: string[];
  usedLemmas?: string[];
  isExpanded?: boolean;
  metadata?: {
    author?: string;
    date?: string;
    complexity?: number;
  };
}

// 证明步骤
export interface ProofStep {
  id: string;
  stepNumber: number;
  description: string;
  justification: string;
  dependsOn?: string[];
  produces?: string;
}

// 组件Props
export interface ProofTreeVizProps {
  root: ProofNode;
  width?: number;
  height?: number;
  className?: string;
  orientation?: 'vertical' | 'horizontal';
  onNodeClick?: (node: ProofNode) => void;
  onNodeExpand?: (node: ProofNode, expanded: boolean) => void;
  showStepByStep?: boolean;
  interactive?: boolean;
}

// 节点类型配置
const NODE_TYPE_CONFIG: Record<ProofNodeType, { 
  icon: string; 
  color: string; 
  bgColor: string;
  borderColor: string;
  shape: 'circle' | 'rect' | 'diamond';
}> = {
  theorem: { 
    icon: '📐', 
    color: '#3b82f6', 
    bgColor: '#eff6ff',
    borderColor: '#60a5fa',
    shape: 'rect' 
  },
  lemma: { 
    icon: '📎', 
    color: '#8b5cf6', 
    bgColor: '#f5f3ff',
    borderColor: '#a78bfa',
    shape: 'rect' 
  },
  axiom: { 
    icon: '📋', 
    color: '#10b981', 
    bgColor: '#ecfdf5',
    borderColor: '#34d399',
    shape: 'rect' 
  },
  assumption: { 
    icon: '❓', 
    color: '#f59e0b', 
    bgColor: '#fffbeb',
    borderColor: '#fbbf24',
    shape: 'diamond' 
  },
  conclusion: { 
    icon: '✓', 
    color: '#10b981', 
    bgColor: '#d1fae5',
    borderColor: '#10b981',
    shape: 'circle' 
  },
  contradiction: { 
    icon: '✗', 
    color: '#ef4444', 
    bgColor: '#fef2f2',
    borderColor: '#f87171',
    shape: 'diamond' 
  },
};

// 状态配置
const STATUS_CONFIG: Record<ProofStatus, { 
  icon: React.ReactNode; 
  color: string;
  label: string;
}> = {
  proven: { 
    icon: <Check className="w-4 h-4" />, 
    color: '#10b981',
    label: '已证明'
  },
  unproven: { 
    icon: <AlertCircle className="w-4 h-4" />, 
    color: '#f59e0b',
    label: '未证明'
  },
  pending: { 
    icon: <Zap className="w-4 h-4" />, 
    color: '#8b5cf6',
    label: '进行中'
  },
  invalid: { 
    icon: <X className="w-4 h-4" />, 
    color: '#ef4444',
    label: '无效'
  },
  axiomatic: { 
    icon: <BookOpen className="w-4 h-4" />, 
    color: '#6b7280',
    label: '公理'
  },
};

export const ProofTreeViz: React.FC<ProofTreeVizProps> = ({
  root,
  width = 1000,
  height = 700,
  className,
  orientation = 'vertical',
  onNodeClick,
  onNodeExpand,
  showStepByStep = false,
  interactive = true,
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const [expandedNodes, setExpandedNodes] = useState<Set<string>>(new Set([root.id]));
  const [selectedNode, setSelectedNode] = useState<ProofNode | null>(null);
  const [hoveredNode, setHoveredNode] = useState<string | null>(null);
  const [currentStep, setCurrentStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [searchQuery, setSearchQuery] = useState('');
  const [filterType, setFilterType] = useState<ProofNodeType | 'all'>('all');
  const [zoomLevel, setZoomLevel] = useState(1);

  // 将树转换为D3层次结构
  const hierarchyData = React.useMemo(() => {
    const convertNode = (node: ProofNode): any => ({
      ...node,
      children: node.children
        ?.filter(child => expandedNodes.has(node.id))
        .map(convertNode) || [],
    });
    return d3.hierarchy(convertNode(root));
  }, [root, expandedNodes]);

  // 绘制证明树
  const drawTree = useCallback(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const margin = { top: 40, right: 40, bottom: 40, left: 40 };
    const innerWidth = width - margin.left - margin.right;
    const innerHeight = height - margin.top - margin.bottom;

    const g = svg.append('g')
      .attr('transform', `translate(${margin.left},${margin.top}) scale(${zoomLevel})`);

    // 创建树布局
    const treeLayout = d3.tree<ProofNode>()
      .size(orientation === 'vertical' 
        ? [innerWidth, innerHeight] 
        : [innerHeight, innerWidth]
      );

    const treeData = treeLayout(hierarchyData);

    // 绘制连接线
    const links = g.selectAll('.link')
      .data(treeData.links())
      .enter()
      .append('g')
      .attr('class', 'link');

    links.append('path')
      .attr('fill', 'none')
      .attr('stroke', d => {
        const targetStatus = (d.target.data as ProofNode).status;
        return STATUS_CONFIG[targetStatus].color;
      })
      .attr('stroke-width', 2)
      .attr('stroke-opacity', 0.6)
      .attr('d', orientation === 'vertical' 
        ? d3.linkVertical<any, any>()
          .x(d => d.x)
          .y(d => d.y)
        : d3.linkHorizontal<any, any>()
          .x(d => d.y)
          .y(d => d.x)
      );

    // 绘制节点
    const nodes = g.selectAll('.node')
      .data(treeData.descendants())
      .enter()
      .append('g')
      .attr('class', 'node')
      .attr('transform', d => orientation === 'vertical'
        ? `translate(${d.x},${d.y})`
        : `translate(${d.y},${d.x})`
      )
      .style('cursor', interactive ? 'pointer' : 'default')
      .on('click', (event, d) => {
        event.stopPropagation();
        handleNodeClick(d.data as ProofNode);
      })
      .on('mouseover', (event, d) => setHoveredNode(d.data.id))
      .on('mouseout', () => setHoveredNode(null));

    // 节点背景
    nodes.each(function(d) {
      const node = d3.select(this);
      const data = d.data as ProofNode;
      const config = NODE_TYPE_CONFIG[data.type];
      const isHighlighted = searchQuery && 
        (data.label.toLowerCase().includes(searchQuery.toLowerCase()) ||
         data.statement.toLowerCase().includes(searchQuery.toLowerCase()));
      const isFiltered = filterType !== 'all' && data.type !== filterType;

      // 根据形状绘制
      if (config.shape === 'circle') {
        node.append('circle')
          .attr('r', 25)
          .attr('fill', isHighlighted ? '#fef3c7' : config.bgColor)
          .attr('stroke', isHighlighted ? '#f59e0b' : config.borderColor)
          .attr('stroke-width', isHighlighted ? 3 : 2)
          .attr('opacity', isFiltered ? 0.3 : 1);
      } else if (config.shape === 'diamond') {
        node.append('polygon')
          .attr('points', '0,-25 25,0 0,25 -25,0')
          .attr('fill', isHighlighted ? '#fef3c7' : config.bgColor)
          .attr('stroke', isHighlighted ? '#f59e0b' : config.borderColor)
          .attr('stroke-width', isHighlighted ? 3 : 2)
          .attr('opacity', isFiltered ? 0.3 : 1);
      } else {
        node.append('rect')
          .attr('x', -40)
          .attr('y', -20)
          .attr('width', 80)
          .attr('height', 40)
          .attr('rx', 8)
          .attr('fill', isHighlighted ? '#fef3c7' : config.bgColor)
          .attr('stroke', isHighlighted ? '#f59e0b' : config.borderColor)
          .attr('stroke-width', isHighlighted ? 3 : 2)
          .attr('opacity', isFiltered ? 0.3 : 1);
      }
    });

    // 状态指示器
    nodes.append('circle')
      .attr('cx', 15)
      .attr('cy', -15)
      .attr('r', 6)
      .attr('fill', d => STATUS_CONFIG[(d.data as ProofNode).status].color);

    // 节点图标
    nodes.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', 5)
      .attr('class', 'text-lg')
      .text(d => NODE_TYPE_CONFIG[(d.data as ProofNode).type].icon);

    // 节点标签
    nodes.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', 45)
      .attr('class', 'text-xs font-medium')
      .attr('fill', '#374151')
      .text(d => {
        const label = (d.data as ProofNode).label;
        return label.length > 12 ? label.substring(0, 12) + '...' : label;
      });

    // 展开/折叠指示器
    nodes.filter(d => (d.data as ProofNode).children && (d.data as ProofNode).children!.length > 0)
      .append('circle')
      .attr('cx', 0)
      .attr('cy', 30)
      .attr('r', 8)
      .attr('fill', '#fff')
      .attr('stroke', '#9ca3af')
      .attr('stroke-width', 1);

    nodes.filter(d => (d.data as ProofNode).children && (d.data as ProofNode).children!.length > 0)
      .append('text')
      .attr('x', 0)
      .attr('y', 34)
      .attr('text-anchor', 'middle')
      .attr('class', 'text-xs')
      .attr('fill', '#6b7280')
      .text(d => expandedNodes.has((d.data as ProofNode).id) ? '−' : '+');

    // 置信度指示
    nodes.filter(d => (d.data as ProofNode).confidence !== undefined)
      .append('path')
      .attr('d', d => {
        const confidence = (d.data as ProofNode).confidence || 0;
        const radius = 28;
        const angle = confidence * Math.PI * 2;
        const x = radius * Math.sin(angle);
        const y = -radius * Math.cos(angle);
        return `M 0,-${radius} A ${radius},${radius} 0 ${confidence > 0.5 ? 1 : 0},1 ${x},${y}`;
      })
      .attr('fill', 'none')
      .attr('stroke', d => {
        const confidence = (d.data as ProofNode).confidence || 0;
        return confidence > 0.8 ? '#10b981' : confidence > 0.5 ? '#f59e0b' : '#ef4444';
      })
      .attr('stroke-width', 3)
      .attr('stroke-linecap', 'round');

    // 添加缩放行为
    const zoom = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.3, 3])
      .on('zoom', (event) => {
        g.attr('transform', `translate(${margin.left + event.transform.x},${margin.top + event.transform.y}) scale(${event.transform.k})`);
        setZoomLevel(event.transform.k);
      });

    svg.call(zoom as any);

  }, [hierarchyData, width, height, orientation, interactive, searchQuery, filterType, expandedNodes, zoomLevel]);

  // 重绘树
  useEffect(() => {
    drawTree();
  }, [drawTree]);

  // 节点点击处理
  const handleNodeClick = (node: ProofNode) => {
    setSelectedNode(node);
    onNodeClick?.(node);

    if (node.children && node.children.length > 0) {
      const newExpanded = new Set(expandedNodes);
      if (newExpanded.has(node.id)) {
        newExpanded.delete(node.id);
      } else {
        newExpanded.add(node.id);
      }
      setExpandedNodes(newExpanded);
      onNodeExpand?.(node, newExpanded.has(node.id));
    }
  };

  // 逐步播放
  useEffect(() => {
    if (!isPlaying || !showStepByStep) return;

    const totalSteps = hierarchyData.descendants().length;
    const interval = setInterval(() => {
      setCurrentStep(prev => {
        if (prev >= totalSteps - 1) {
          setIsPlaying(false);
          return prev;
        }
        return prev + 1;
      });
    }, 1500);

    return () => clearInterval(interval);
  }, [isPlaying, showStepByStep, hierarchyData]);

  // 展开全部
  const expandAll = () => {
    const allIds = new Set<string>();
    const collectIds = (node: ProofNode) => {
      allIds.add(node.id);
      node.children?.forEach(collectIds);
    };
    collectIds(root);
    setExpandedNodes(allIds);
  };

  // 折叠全部
  const collapseAll = () => {
    setExpandedNodes(new Set([root.id]));
  };

  // 导出SVG
  const exportSVG = () => {
    if (!svgRef.current) return;
    const svgData = new XMLSerializer().serializeToString(svgRef.current);
    const blob = new Blob([svgData], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `proof-tree-${Date.now()}.svg`;
    link.click();
  };

  // 收集所有步骤
  const allSteps = React.useMemo(() => {
    const steps: ProofNode[] = [];
    const traverse = (node: ProofNode) => {
      steps.push(node);
      node.children?.forEach(traverse);
    };
    traverse(root);
    return steps;
  }, [root]);

  return (
    <div ref={containerRef} className={cn('bg-white rounded-lg border border-gray-200', className)}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center gap-3">
          <div className="p-2 bg-blue-100 rounded-lg">
            <GitBranch className="w-5 h-5 text-blue-600" />
          </div>
          <div>
            <h3 className="font-semibold text-gray-800">定理证明树</h3>
            <p className="text-sm text-gray-500">{root.label}</p>
          </div>
        </div>

        {/* 搜索和过滤 */}
        <div className="flex items-center gap-2">
          <div className="relative">
            <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
            <input
              type="text"
              placeholder="搜索节点..."
              value={searchQuery}
              onChange={(e) => setSearchQuery(e.target.value)}
              className="pl-9 pr-4 py-1.5 text-sm border border-gray-200 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500 w-48"
            />
          </div>
          <select
            value={filterType}
            onChange={(e) => setFilterType(e.target.value as ProofNodeType | 'all')}
            className="px-3 py-1.5 text-sm border border-gray-200 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
          >
            <option value="all">所有类型</option>
            <option value="theorem">定理</option>
            <option value="lemma">引理</option>
            <option value="axiom">公理</option>
            <option value="assumption">假设</option>
            <option value="conclusion">结论</option>
          </select>
        </div>

        {/* 控制按钮 */}
        <div className="flex items-center gap-1">
          <button
            onClick={expandAll}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="展开全部"
          >
            <Maximize2 className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={collapseAll}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="折叠全部"
          >
            <Minimize2 className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={() => setOrientation(o => o === 'vertical' ? 'horizontal' : 'vertical')}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="切换方向"
          >
            <RotateCcw className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={exportSVG}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="导出SVG"
          >
            <Download className="w-4 h-4 text-gray-600" />
          </button>
        </div>
      </div>

      {/* 逐步播放控制 */}
      {showStepByStep && (
        <div className="px-4 py-2 bg-gray-50 border-b border-gray-200 flex items-center gap-4">
          <button
            onClick={() => setIsPlaying(!isPlaying)}
            className="flex items-center gap-2 px-3 py-1.5 bg-blue-500 hover:bg-blue-600 text-white rounded-lg transition-colors"
          >
            {isPlaying ? '暂停' : '播放'}
          </button>
          <div className="flex-1 h-2 bg-gray-200 rounded-full overflow-hidden">
            <div 
              className="h-full bg-blue-500 transition-all duration-300"
              style={{ width: `${(currentStep / allSteps.length) * 100}%` }}
            />
          </div>
          <span className="text-sm text-gray-600">
            {currentStep + 1} / {allSteps.length}
          </span>
        </div>
      )}

      {/* 主可视化区域 */}
      <div className="relative">
        <svg
          ref={svgRef}
          width={width}
          height={height}
          className="w-full"
        />

        {/* 悬浮提示 */}
        {hoveredNode && (
          <div className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 max-w-sm z-10">
            {(() => {
              const findNode = (node: ProofNode, id: string): ProofNode | null => {
                if (node.id === id) return node;
                for (const child of node.children || []) {
                  const found = findNode(child, id);
                  if (found) return found;
                }
                return null;
              };
              const node = findNode(root, hoveredNode);
              if (!node) return null;
              
              return (
                <>
                  <div className="flex items-center gap-2 mb-2">
                    <span className="text-lg">{NODE_TYPE_CONFIG[node.type].icon}</span>
                    <span 
                      className="text-xs font-medium px-2 py-0.5 rounded-full"
                      style={{ 
                        backgroundColor: NODE_TYPE_CONFIG[node.type].bgColor,
                        color: NODE_TYPE_CONFIG[node.type].color 
                      }}
                    >
                      {node.type}
                    </span>
                    <span 
                      className="text-xs flex items-center gap-1"
                      style={{ color: STATUS_CONFIG[node.status].color }}
                    >
                      {STATUS_CONFIG[node.status].icon}
                      {STATUS_CONFIG[node.status].label}
                    </span>
                  </div>
                  <h4 className="font-semibold text-gray-800">{node.label}</h4>
                  <p className="text-sm text-gray-600 mt-1 line-clamp-2">{node.statement}</p>
                  {node.confidence !== undefined && (
                    <div className="mt-2 flex items-center gap-2">
                      <span className="text-xs text-gray-500">置信度:</span>
                      <div className="flex-1 h-1.5 bg-gray-200 rounded-full overflow-hidden">
                        <div 
                          className="h-full rounded-full"
                          style={{ 
                            width: `${node.confidence * 100}%`,
                            backgroundColor: node.confidence > 0.8 ? '#10b981' : 
                                            node.confidence > 0.5 ? '#f59e0b' : '#ef4444'
                          }}
                        />
                      </div>
                      <span className="text-xs text-gray-600">{Math.round(node.confidence * 100)}%</span>
                    </div>
                  )}
                </>
              );
            })()}
          </div>
        )}

        {/* 选中节点详情面板 */}
        {selectedNode && (
          <div className="absolute top-4 right-4 bg-white rounded-lg shadow-lg border border-gray-200 p-5 w-80 z-10 max-h-[80%] overflow-y-auto">
            <div className="flex justify-between items-start mb-4">
              <div className="flex items-center gap-2">
                <span className="text-2xl">{NODE_TYPE_CONFIG[selectedNode.type].icon}</span>
                <div>
                  <h4 className="font-semibold text-gray-800">{selectedNode.label}</h4>
                  <span className="text-xs text-gray-500">{selectedNode.type}</span>
                </div>
              </div>
              <button
                onClick={() => setSelectedNode(null)}
                className="text-gray-400 hover:text-gray-600"
              >
                ×
              </button>
            </div>

            <div className="space-y-4">
              <div>
                <h5 className="text-sm font-medium text-gray-700 mb-1">陈述</h5>
                <p className="text-sm text-gray-600 bg-gray-50 p-3 rounded-lg">
                  {selectedNode.statement}
                </p>
              </div>

              {selectedNode.proof && (
                <div>
                  <h5 className="text-sm font-medium text-gray-700 mb-1">证明</h5>
                  <p className="text-sm text-gray-600 bg-gray-50 p-3 rounded-lg font-mono">
                    {selectedNode.proof}
                  </p>
                </div>
              )}

              <div className="grid grid-cols-2 gap-3">
                <div className="bg-gray-50 p-3 rounded-lg">
                  <span className="text-xs text-gray-500">状态</span>
                  <div 
                    className="flex items-center gap-1 mt-1"
                    style={{ color: STATUS_CONFIG[selectedNode.status].color }}
                  >
                    {STATUS_CONFIG[selectedNode.status].icon}
                    <span className="text-sm font-medium">
                      {STATUS_CONFIG[selectedNode.status].label}
                    </span>
                  </div>
                </div>
                {selectedNode.confidence !== undefined && (
                  <div className="bg-gray-50 p-3 rounded-lg">
                    <span className="text-xs text-gray-500">置信度</span>
                    <p className="text-sm font-medium text-gray-800 mt-1">
                      {Math.round(selectedNode.confidence * 100)}%
                    </p>
                  </div>
                )}
              </div>

              {selectedNode.usedAxioms && selectedNode.usedAxioms.length > 0 && (
                <div>
                  <h5 className="text-sm font-medium text-gray-700 mb-2">使用的公理</h5>
                  <div className="flex flex-wrap gap-1">
                    {selectedNode.usedAxioms.map((axiom, idx) => (
                      <span key={idx} className="text-xs px-2 py-1 bg-green-100 text-green-700 rounded">
                        {axiom}
                      </span>
                    ))}
                  </div>
                </div>
              )}

              {selectedNode.usedLemmas && selectedNode.usedLemmas.length > 0 && (
                <div>
                  <h5 className="text-sm font-medium text-gray-700 mb-2">使用的引理</h5>
                  <div className="flex flex-wrap gap-1">
                    {selectedNode.usedLemmas.map((lemma, idx) => (
                      <span key={idx} className="text-xs px-2 py-1 bg-purple-100 text-purple-700 rounded">
                        {lemma}
                      </span>
                    ))}
                  </div>
                </div>
              )}
            </div>
          </div>
        )}
      </div>

      {/* 图例 */}
      <div className="px-4 py-3 border-t border-gray-200 flex flex-wrap items-center gap-6">
        <span className="text-sm font-medium text-gray-700">节点类型:</span>
        {Object.entries(NODE_TYPE_CONFIG).map(([type, config]) => (
          <div key={type} className="flex items-center gap-1.5">
            <span className="text-sm">{config.icon}</span>
            <span className="text-xs text-gray-600 capitalize">{type}</span>
          </div>
        ))}
        <div className="ml-auto flex items-center gap-4">
          <span className="text-sm font-medium text-gray-700">状态:</span>
          {Object.entries(STATUS_CONFIG).map(([status, config]) => (
            <div key={status} className="flex items-center gap-1" style={{ color: config.color }}>
              {config.icon}
              <span className="text-xs">{config.label}</span>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default ProofTreeViz;
