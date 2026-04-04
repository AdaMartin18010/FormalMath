/**
 * FormalMath 学习路径可视化组件
 * 显示推荐学习路径和时间预估
 */

import React, { useEffect, useState, useCallback } from 'react';
import { learningPathService } from '../../integrations/learningPath';
import type { VisualPath, VisualPathNode, PathConnection } from '../../types/learning';
import type { PathTimeEstimate, PathComparison } from '../../integrations/learningPath';

interface LearningPathViewProps {
  userId: string;
  width?: number;
  height?: number;
  showTimeEstimate?: boolean;
  showComparison?: boolean;
  onNodeClick?: (node: VisualPathNode) => void;
  className?: string;
}

interface NodePosition {
  x: number;
  y: number;
}

/**
 * 学习路径可视化组件
 */
export const LearningPathView: React.FC<LearningPathViewProps> = ({
  userId,
  width = 900,
  height = 500,
  showTimeEstimate = true,
  showComparison = false,
  onNodeClick,
  className = '',
}) => {
  const [path, setPath] = useState<VisualPath | null>(null);
  const [timeEstimate, setTimeEstimate] = useState<PathTimeEstimate | null>(null);
  const [comparison, setComparison] = useState<PathComparison | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<Error | null>(null);
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [viewMode, setViewMode] = useState<'path' | 'comparison'>('path');

  // 加载路径数据
  useEffect(() => {
    setLoading(true);
    
    const loadData = async () => {
      try {
        const [pathData, timeData] = await Promise.all([
          learningPathService.getVisualLearningPath(userId),
          showTimeEstimate ? learningPathService.getPathTimeEstimate(userId) : null,
          showComparison ? learningPathService.getPathComparison(userId) : null,
        ]);
        
        setPath(pathData);
        setTimeEstimate(timeData);
        if (showComparison) {
          const compData = await learningPathService.getPathComparison(userId);
          setComparison(compData);
        }
      } catch (err) {
        setError(err instanceof Error ? err : new Error('Failed to load path'));
      } finally {
        setLoading(false);
      }
    };
    
    loadData();
  }, [userId, showTimeEstimate, showComparison]);

  // 获取节点状态样式
  const getNodeStatusStyle = (node: VisualPathNode) => {
    const baseClasses = 'absolute w-12 h-12 rounded-full flex items-center justify-center text-sm font-medium transition-all cursor-pointer hover:scale-110';
    
    switch (node.status) {
      case 'completed':
        return `${baseClasses} bg-green-500 text-white shadow-lg`;
      case 'in_progress':
        return `${baseClasses} bg-purple-500 text-white shadow-lg ring-4 ring-purple-200 animate-pulse`;
      case 'available':
        return `${baseClasses} bg-blue-500 text-white shadow`;
      case 'locked':
        return `${baseClasses} bg-gray-300 text-gray-500 cursor-not-allowed`;
      case 'skipped':
        return `${baseClasses} bg-gray-400 text-white opacity-50`;
      default:
        return baseClasses;
    }
  };

  // 获取连接线样式
  const getConnectionStyle = (type: PathConnection['type']) => {
    switch (type) {
      case 'main':
        return 'stroke-blue-400 stroke-2';
      case 'alternative':
        return 'stroke-gray-300 stroke-1 stroke-dasharray-4';
      case 'shortcut':
        return 'stroke-green-400 stroke-1';
      default:
        return 'stroke-gray-300';
    }
  };

  // 处理节点点击
  const handleNodeClick = (node: VisualPathNode) => {
    setSelectedNode(node.id);
    onNodeClick?.(node);
  };

  // 格式化时间
  const formatTime = (minutes: number): string => {
    if (minutes < 60) return `${minutes}分钟`;
    const hours = Math.floor(minutes / 60);
    const mins = minutes % 60;
    return mins > 0 ? `${hours}小时${mins}分钟` : `${hours}小时`;
  };

  // 渲染路径视图
  const renderPathView = () => {
    if (!path) return null;

    return (
      <div className="relative" style={{ width, height }}>
        {/* 进度信息 */}
        <div className="absolute top-4 left-4 bg-white rounded-lg shadow p-4 z-10">
          <h3 className="font-semibold text-gray-800 mb-2">学习进度</h3>
          <div className="space-y-2">
            <div className="flex items-center gap-4">
              <div className="text-2xl font-bold text-blue-600">
                {path.progress.completed}
                <span className="text-gray-400 text-lg">/{path.progress.total}</span>
              </div>
              <div className="text-sm text-gray-600">
                已完成
              </div>
            </div>
            <div className="w-48 h-2 bg-gray-200 rounded-full overflow-hidden">
              <div
                className="h-full bg-blue-500 transition-all"
                style={{
                  width: `${(path.progress.completed / path.progress.total) * 100}%`,
                }}
              />
            </div>
          </div>
          {timeEstimate && (
            <div className="mt-4 pt-4 border-t text-sm">
              <div className="flex justify-between text-gray-600">
                <span>预计剩余时间:</span>
                <span className="font-medium">{formatTime(timeEstimate.totalMinutes)}</span>
              </div>
              <div className="flex justify-between text-gray-600 mt-1">
                <span>预计完成日期:</span>
                <span className="font-medium">
                  {new Date(timeEstimate.estimatedCompletionDate).toLocaleDateString('zh-CN')}
                </span>
              </div>
            </div>
          )}
        </div>

        {/* 图例 */}
        <div className="absolute top-4 right-4 bg-white rounded-lg shadow p-4 z-10">
          <h4 className="font-medium text-gray-800 mb-2">节点状态</h4>
          <div className="space-y-2 text-sm">
            <LegendItem color="bg-green-500" label="已完成" />
            <LegendItem color="bg-purple-500" label="学习中" ring />
            <LegendItem color="bg-blue-500" label="可开始" />
            <LegendItem color="bg-gray-300" label="未解锁" />
          </div>
        </div>

        {/* 路径图 */}
        <svg width={width} height={height} className="absolute inset-0">
          {/* 连接线 */}
          {path.connections.map((conn, idx) => {
            const fromNode = path.nodes.find(n => n.id === conn.from);
            const toNode = path.nodes.find(n => n.id === conn.to);
            if (!fromNode || !toNode) return null;

            return (
              <line
                key={idx}
                x1={fromNode.position.x + 24}
                y1={fromNode.position.y + 24}
                x2={toNode.position.x + 24}
                y2={toNode.position.y + 24}
                className={getConnectionStyle(conn.type)}
                markerEnd="url(#arrowhead)"
              />
            );
          })}

          {/* 箭头标记 */}
          <defs>
            <marker
              id="arrowhead"
              markerWidth="10"
              markerHeight="7"
              refX="28"
              refY="3.5"
              orient="auto"
            >
              <polygon points="0 0, 10 3.5, 0 7" fill="#9ca3af" />
            </marker>
          </defs>
        </svg>

        {/* 节点 */}
        {path.nodes.map((node, idx) => (
          <div
            key={node.id}
            className={getNodeStatusStyle(node)}
            style={{
              left: node.position.x,
              top: node.position.y,
            }}
            onClick={() => handleNodeClick(node)}
          >
            {node.status === 'completed' ? '✓' : idx + 1}
          </div>
        ))}

        {/* 节点标签 */}
        {path.nodes.map((node, idx) => (
          <div
            key={`label-${node.id}`}
            className="absolute text-xs text-gray-600 text-center"
            style={{
              left: node.position.x,
              top: node.position.y + 50,
              width: 48,
            }}
          >
            <div className="font-medium truncate">{node.conceptId}</div>
            <div className="text-gray-400">{node.estimatedTime}分钟</div>
            {node.isMilestone && (
              <div className="text-amber-500">🏆</div>
            )}
          </div>
        ))}

        {/* 选中节点详情 */}
        {selectedNode && (
          <NodeDetailPanel
            node={path.nodes.find(n => n.id === selectedNode)!}
            onClose={() => setSelectedNode(null)}
          />
        )}
      </div>
    );
  };

  // 渲染对比视图
  const renderComparisonView = () => {
    if (!comparison) return null;

    return (
      <div className="p-6" style={{ width, height }}>
        <h3 className="text-xl font-bold text-gray-800 mb-6">路径优化对比</h3>
        
        <div className="grid grid-cols-2 gap-6">
          {/* 当前路径 */}
          <div className="bg-gray-50 rounded-lg p-4">
            <h4 className="font-semibold text-gray-700 mb-4">当前路径</h4>
            <div className="space-y-3">
              <ComparisonItem label="总节点数" value={comparison.currentPath.totalNodes} />
              <ComparisonItem label="已完成" value={comparison.currentPath.completedNodes} />
              <ComparisonItem label="剩余节点" value={comparison.currentPath.remainingNodes} />
              <ComparisonItem 
                label="预计时间" 
                value={formatTime(comparison.currentPath.estimatedTime)} 
              />
            </div>
          </div>

          {/* 优化路径 */}
          <div className="bg-green-50 rounded-lg p-4">
            <h4 className="font-semibold text-green-700 mb-4">优化路径</h4>
            <div className="space-y-3">
              <ComparisonItem label="总节点数" value={comparison.optimizedPath.totalNodes} />
              <ComparisonItem 
                label="预计时间" 
                value={formatTime(comparison.optimizedPath.estimatedTime)} 
              />
              <ComparisonItem 
                label="整体难度" 
                value={`${comparison.optimizedPath.difficulty}/10`} 
              />
              <div className="text-green-600 font-medium">
                可节省 {formatTime(comparison.potentialSavings)}
              </div>
            </div>
          </div>
        </div>

        {/* 建议 */}
        <div className="mt-6 bg-blue-50 rounded-lg p-4">
          <h4 className="font-semibold text-blue-700 mb-2">优化建议</h4>
          <ul className="list-disc list-inside space-y-1 text-blue-600">
            {comparison.recommendations.map((rec, idx) => (
              <li key={idx}>{rec}</li>
            ))}
          </ul>
        </div>
      </div>
    );
  };

  if (loading) {
    return (
      <div className="flex items-center justify-center" style={{ width, height }}>
        <div className="text-gray-500">加载学习路径...</div>
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
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 视图切换 */}
      {showComparison && (
        <div className="flex border-b">
          <button
            className={`px-6 py-3 font-medium transition-colors ${
              viewMode === 'path'
                ? 'text-blue-600 border-b-2 border-blue-600'
                : 'text-gray-600 hover:text-gray-800'
            }`}
            onClick={() => setViewMode('path')}
          >
            学习路径
          </button>
          <button
            className={`px-6 py-3 font-medium transition-colors ${
              viewMode === 'comparison'
                ? 'text-blue-600 border-b-2 border-blue-600'
                : 'text-gray-600 hover:text-gray-800'
            }`}
            onClick={() => setViewMode('comparison')}
          >
            路径对比
          </button>
        </div>
      )}

      {/* 内容 */}
      {viewMode === 'path' ? renderPathView() : renderComparisonView()}
    </div>
  );
};

// 图例项组件
const LegendItem: React.FC<{ color: string; label: string; ring?: boolean }> = ({
  color,
  label,
  ring,
}) => (
  <div className="flex items-center gap-2">
    <div className={`w-4 h-4 rounded-full ${color} ${ring ? 'ring-2 ring-purple-200' : ''}`} />
    <span className="text-gray-600">{label}</span>
  </div>
);

// 对比项组件
const ComparisonItem: React.FC<{ label: string; value: string | number }> = ({
  label,
  value,
}) => (
  <div className="flex justify-between">
    <span className="text-gray-600">{label}</span>
    <span className="font-medium">{value}</span>
  </div>
);

// 节点详情面板
const NodeDetailPanel: React.FC<{ node: VisualPathNode; onClose: () => void }> = ({
  node,
  onClose,
}) => (
  <div className="absolute bottom-4 left-4 right-4 bg-white rounded-lg shadow-lg p-4 z-20">
    <div className="flex justify-between items-start mb-2">
      <h4 className="font-semibold text-gray-800">{node.conceptId}</h4>
      <button onClick={onClose} className="text-gray-400 hover:text-gray-600">×</button>
    </div>
    <div className="grid grid-cols-3 gap-4 text-sm">
      <div>
        <span className="text-gray-500">状态:</span>
        <span className="ml-2 font-medium">
          {node.status === 'completed' && '已完成'}
          {node.status === 'in_progress' && '学习中'}
          {node.status === 'available' && '可开始'}
          {node.status === 'locked' && '未解锁'}
          {node.status === 'skipped' && '已跳过'}
        </span>
      </div>
      <div>
        <span className="text-gray-500">预计时间:</span>
        <span className="ml-2 font-medium">{node.estimatedTime}分钟</span>
      </div>
      <div>
        <span className="text-gray-500">里程碑:</span>
        <span className="ml-2">{node.isMilestone ? '🏆 是' : '否'}</span>
      </div>
    </div>
  </div>
);

export default LearningPathView;
