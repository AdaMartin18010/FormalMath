/**
 * FormalMath 个性化知识图谱可视化组件
 * 显示用户掌握度、薄弱点、推荐概念
 */

import React, { useEffect, useRef, useState, useCallback } from 'react';
import { personalizedGraphService } from '../../integrations/personalizedGraph';
import type {
  PersonalizedGraphData,
  PersonalizedNode,
  GraphEdge,
  MasteryLevel,
} from '../../types/learning';

interface PersonalizedGraphProps {
  userId: string;
  conceptGraph: import('../../integrations/personalizedGraph').ConceptGraph;
  width?: number;
  height?: number;
  onNodeClick?: (node: PersonalizedNode) => void;
  onNodeHover?: (node: PersonalizedNode | null) => void;
  className?: string;
}

interface TooltipState {
  visible: boolean;
  x: number;
  y: number;
  node: PersonalizedNode | null;
}

/**
 * 个性化知识图谱组件
 */
export const PersonalizedGraph: React.FC<PersonalizedGraphProps> = ({
  userId,
  conceptGraph,
  width = 1000,
  height = 600,
  onNodeClick,
  onNodeHover,
  className = '',
}) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const [graphData, setGraphData] = useState<PersonalizedGraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<Error | null>(null);
  const [tooltip, setTooltip] = useState<TooltipState>({
    visible: false,
    x: 0,
    y: 0,
    node: null,
  });
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [legendVisible, setLegendVisible] = useState(true);

  // 加载图谱数据
  useEffect(() => {
    setLoading(true);
    personalizedGraphService.getPersonalizedGraph(userId, conceptGraph)
      .then(data => {
        setGraphData(data);
        setLoading(false);
      })
      .catch(err => {
        setError(err instanceof Error ? err : new Error('Failed to load graph'));
        setLoading(false);
      });
  }, [userId, conceptGraph]);

  // 绘制图谱
  const drawGraph = useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas || !graphData) return;

    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    // 清空画布
    ctx.clearRect(0, 0, width, height);

    // 绘制边
    graphData.edges.forEach(edge => {
      const sourceNode = graphData.nodes.find(n => n.id === edge.source);
      const targetNode = graphData.nodes.find(n => n.id === edge.target);
      
      if (sourceNode && targetNode) {
        drawEdge(ctx, sourceNode, targetNode, edge.type);
      }
    });

    // 绘制节点
    graphData.nodes.forEach(node => {
      drawNode(ctx, node, selectedNode === node.id);
    });
  }, [graphData, width, height, selectedNode]);

  // 绘制节点
  const drawNode = (
    ctx: CanvasRenderingContext2D,
    node: PersonalizedNode,
    isSelected: boolean
  ) => {
    const { x, y, size, color, opacity } = node;

    // 节点光晕（薄弱点或当前焦点）
    if (node.isWeakPoint || node.isCurrentFocus) {
      ctx.beginPath();
      ctx.arc(x, y, size + 10, 0, Math.PI * 2);
      ctx.fillStyle = node.isCurrentFocus 
        ? 'rgba(139, 92, 246, 0.3)' // 紫色光晕
        : 'rgba(220, 38, 38, 0.3)'; // 红色光晕
      ctx.fill();
    }

    // 推荐标记
    if (node.isRecommended) {
      ctx.beginPath();
      ctx.arc(x, y, size + 5, 0, Math.PI * 2);
      ctx.strokeStyle = '#06b6d4';
      ctx.lineWidth = 3;
      ctx.stroke();
    }

    // 节点主体
    ctx.beginPath();
    ctx.arc(x, y, size, 0, Math.PI * 2);
    ctx.fillStyle = color;
    ctx.globalAlpha = opacity;
    ctx.fill();
    ctx.globalAlpha = 1;

    // 选中状态
    if (isSelected) {
      ctx.beginPath();
      ctx.arc(x, y, size + 3, 0, Math.PI * 2);
      ctx.strokeStyle = '#ffffff';
      ctx.lineWidth = 3;
      ctx.stroke();
    }

    // 节点标签
    ctx.fillStyle = '#1f2937';
    ctx.font = '12px sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(node.label, x, y + size + 15);

    // 掌握度指示器
    const masteryLabel = getMasteryLabel(node.mastery);
    ctx.fillStyle = getMasteryColor(node.mastery);
    ctx.font = '10px sans-serif';
    ctx.fillText(masteryLabel, x, y);
  };

  // 绘制边
  const drawEdge = (
    ctx: CanvasRenderingContext2D,
    source: PersonalizedNode,
    target: PersonalizedNode,
    type: GraphEdge['type']
  ) => {
    ctx.beginPath();
    ctx.moveTo(source.x, source.y);
    ctx.lineTo(target.x, target.y);

    // 根据边类型设置样式
    switch (type) {
      case 'prerequisite':
        ctx.strokeStyle = '#9ca3af';
        ctx.lineWidth = 2;
        break;
      case 'related':
        ctx.strokeStyle = '#d1d5db';
        ctx.lineWidth = 1;
        ctx.setLineDash([5, 5]);
        break;
      case 'extension':
        ctx.strokeStyle = '#93c5fd';
        ctx.lineWidth = 1;
        break;
    }

    ctx.stroke();
    ctx.setLineDash([]);

    // 绘制箭头（仅先决条件）
    if (type === 'prerequisite') {
      drawArrow(ctx, source.x, source.y, target.x, target.y);
    }
  };

  // 绘制箭头
  const drawArrow = (
    ctx: CanvasRenderingContext2D,
    fromX: number,
    fromY: number,
    toX: number,
    toY: number
  ) => {
    const angle = Math.atan2(toY - fromY, toX - fromX);
    const arrowLength = 10;
    const arrowAngle = Math.PI / 6;

    // 计算箭头起点（在目标节点边缘）
    const targetNode = graphData?.nodes.find(n => n.x === toX && n.y === toY);
    const offset = targetNode ? targetNode.size + 5 : 20;
    const startX = toX - offset * Math.cos(angle);
    const startY = toY - offset * Math.sin(angle);

    ctx.beginPath();
    ctx.moveTo(startX, startY);
    ctx.lineTo(
      startX - arrowLength * Math.cos(angle - arrowAngle),
      startY - arrowLength * Math.sin(angle - arrowAngle)
    );
    ctx.moveTo(startX, startY);
    ctx.lineTo(
      startX - arrowLength * Math.cos(angle + arrowAngle),
      startY - arrowLength * Math.sin(angle + arrowAngle)
    );
    ctx.strokeStyle = '#9ca3af';
    ctx.lineWidth = 2;
    ctx.stroke();
  };

  // 处理鼠标事件
  const handleMouseMove = (e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas || !graphData) return;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // 查找悬停的节点
    const hoveredNode = graphData.nodes.find(node => {
      const dx = x - node.x;
      const dy = y - node.y;
      return Math.sqrt(dx * dx + dy * dy) <= node.size;
    });

    if (hoveredNode) {
      setTooltip({
        visible: true,
        x: e.clientX + 10,
        y: e.clientY - 10,
        node: hoveredNode,
      });
      onNodeHover?.(hoveredNode);
    } else {
      setTooltip(prev => ({ ...prev, visible: false }));
      onNodeHover?.(null);
    }
  };

  const handleClick = (e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas || !graphData) return;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    const clickedNode = graphData.nodes.find(node => {
      const dx = x - node.x;
      const dy = y - node.y;
      return Math.sqrt(dx * dx + dy * dy) <= node.size;
    });

    if (clickedNode) {
      setSelectedNode(clickedNode.id);
      onNodeClick?.(clickedNode);
    } else {
      setSelectedNode(null);
    }
  };

  const handleMouseLeave = () => {
    setTooltip(prev => ({ ...prev, visible: false }));
    onNodeHover?.(null);
  };

  // 重绘图谱
  useEffect(() => {
    drawGraph();
  }, [drawGraph]);

  if (loading) {
    return (
      <div className="flex items-center justify-center" style={{ width, height }}>
        <div className="text-gray-500">加载知识图谱...</div>
      </div>
    );
  }

  if (error) {
    return (
      <div className="flex items-center justify-center" style={{ width, height }}>
        <div className="text-red-500">加载失败: {error.message}</div>
      </div>
    );
  }

  return (
    <div className={`relative ${className}`}>
      {/* 统计信息 */}
      {graphData?.userProgress && (
        <div className="absolute top-4 left-4 bg-white/90 backdrop-blur rounded-lg shadow p-4 z-10">
          <h3 className="font-semibold text-gray-800 mb-2">学习进度</h3>
          <div className="space-y-1 text-sm">
            <div className="flex justify-between gap-4">
              <span className="text-gray-600">总概念:</span>
              <span className="font-medium">{graphData.userProgress.totalConcepts}</span>
            </div>
            <div className="flex justify-between gap-4">
              <span className="text-gray-600">已掌握:</span>
              <span className="font-medium text-green-600">
                {graphData.userProgress.masteredConcepts}
              </span>
            </div>
            <div className="flex justify-between gap-4">
              <span className="text-gray-600">薄弱点:</span>
              <span className="font-medium text-red-600">
                {graphData.userProgress.weakPointsCount}
              </span>
            </div>
            <div className="flex justify-between gap-4">
              <span className="text-gray-600">完成度:</span>
              <span className="font-medium">{graphData.userProgress.overallCompletion}%</span>
            </div>
          </div>
        </div>
      )}

      {/* 图例 */}
      {legendVisible && (
        <div className="absolute bottom-4 right-4 bg-white/90 backdrop-blur rounded-lg shadow p-4 z-10">
          <div className="flex items-center justify-between mb-2">
            <h4 className="font-medium text-gray-800">图例</h4>
            <button
              onClick={() => setLegendVisible(false)}
              className="text-gray-400 hover:text-gray-600"
            >
              ×
            </button>
          </div>
          <div className="space-y-2 text-sm">
            <LegendItem color={personalizedGraphService.MASTERY_COLORS[4]} label="精通 (L4)" />
            <LegendItem color={personalizedGraphService.MASTERY_COLORS[3]} label="熟练 (L3)" />
            <LegendItem color={personalizedGraphService.MASTERY_COLORS[2]} label="理解 (L2)" />
            <LegendItem color={personalizedGraphService.MASTERY_COLORS[1]} label="初学 (L1)" />
            <LegendItem color={personalizedGraphService.MASTERY_COLORS[0]} label="未掌握 (L0)" />
            <div className="border-t pt-2 mt-2">
              <LegendItem color="#dc2626" label="薄弱点" />
              <LegendItem color="#8b5cf6" label="当前焦点" />
              <LegendItem color="#06b6d4" label="推荐学习" />
            </div>
          </div>
        </div>
      )}

      {/* 画布 */}
      <canvas
        ref={canvasRef}
        width={width}
        height={height}
        onMouseMove={handleMouseMove}
        onClick={handleClick}
        onMouseLeave={handleMouseLeave}
        className="cursor-pointer"
        style={{ background: 'linear-gradient(135deg, #f8fafc 0%, #e2e8f0 100%)' }}
      />

      {/* Tooltip */}
      {tooltip.visible && tooltip.node && (
        <div
          className="fixed z-50 bg-white rounded-lg shadow-lg p-3 pointer-events-none"
          style={{ left: tooltip.x, top: tooltip.y }}
        >
          <div className="font-semibold text-gray-800">{tooltip.node.label}</div>
          <div className="text-sm text-gray-600 mt-1">
            掌握度: {getMasteryLabel(tooltip.node.mastery)}
          </div>
          {tooltip.node.isWeakPoint && (
            <div className="text-sm text-red-500 mt-1">⚠️ 薄弱点</div>
          )}
          {tooltip.node.isRecommended && (
            <div className="text-sm text-cyan-600 mt-1">⭐ 推荐学习</div>
          )}
          {tooltip.node.isCurrentFocus && (
            <div className="text-sm text-purple-600 mt-1">📍 当前学习</div>
          )}
        </div>
      )}
    </div>
  );
};

// 图例项组件
const LegendItem: React.FC<{ color: string; label: string }> = ({ color, label }) => (
  <div className="flex items-center gap-2">
    <div
      className="w-3 h-3 rounded-full"
      style={{ backgroundColor: color }}
    />
    <span className="text-gray-600">{label}</span>
  </div>
);

// 获取掌握度标签
const getMasteryLabel = (level: MasteryLevel): string => {
  const labels: Record<MasteryLevel, string> = {
    0: 'L0',
    1: 'L1',
    2: 'L2',
    3: 'L3',
    4: 'L4',
  };
  return labels[level];
};

// 获取掌握度颜色
const getMasteryColor = (level: MasteryLevel): string => {
  return personalizedGraphService.MASTERY_COLORS[level];
};

export default PersonalizedGraph;
