import React, { useState, useCallback } from 'react';
import { 
  ChevronRight, 
  ChevronDown, 
  Plus, 
  Minus, 
  RotateCcw,
  Search,
  Maximize2,
  Minimize2
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface TreeNode {
  id: string;
  label: string;
  type?: 'root' | 'branch' | 'leaf';
  description?: string;
  children?: TreeNode[];
  expanded?: boolean;
  data?: Record<string, unknown>;
}

interface InteractiveTreeProps {
  data: TreeNode;
  className?: string;
  onNodeClick?: (node: TreeNode) => void;
  onNodeToggle?: (node: TreeNode, expanded: boolean) => void;
  renderNode?: (node: TreeNode, isExpanded: boolean) => React.ReactNode;
  searchable?: boolean;
  zoomable?: boolean;
}

export const InteractiveTree: React.FC<InteractiveTreeProps> = ({
  data,
  className,
  onNodeClick,
  onNodeToggle,
  renderNode,
  searchable = true,
  zoomable = true,
}) => {
  const [expandedNodes, setExpandedNodes] = useState<Set<string>>(new Set([data.id]));
  const [zoom, setZoom] = useState(1);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedNode, setSelectedNode] = useState<string | null>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);

  const toggleNode = useCallback((node: TreeNode) => {
    setExpandedNodes(prev => {
      const next = new Set(prev);
      if (next.has(node.id)) {
        next.delete(node.id);
        onNodeToggle?.(node, false);
      } else {
        next.add(node.id);
        onNodeToggle?.(node, true);
      }
      return next;
    });
  }, [onNodeToggle]);

  const expandAll = useCallback(() => {
    const collectIds = (node: TreeNode): string[] => {
      const ids = [node.id];
      node.children?.forEach(child => {
        ids.push(...collectIds(child));
      });
      return ids;
    };
    setExpandedNodes(new Set(collectIds(data)));
  }, [data]);

  const collapseAll = useCallback(() => {
    setExpandedNodes(new Set([data.id]));
  }, [data]);

  const handleNodeClick = useCallback((node: TreeNode) => {
    setSelectedNode(node.id);
    onNodeClick?.(node);
  }, [onNodeClick]);

  // 搜索高亮
  const isMatch = (node: TreeNode): boolean => {
    if (!searchQuery) return false;
    const query = searchQuery.toLowerCase();
    return (
      node.label.toLowerCase().includes(query) ||
      node.description?.toLowerCase().includes(query) ||
      false
    );
  };

  // 递归渲染节点
  const renderTreeNode = (node: TreeNode, depth = 0): React.ReactNode => {
    const isExpanded = expandedNodes.has(node.id);
    const hasChildren = node.children && node.children.length > 0;
    const isSelected = selectedNode === node.id;
    const matched = isMatch(node);

    const getNodeColor = () => {
      switch (node.type) {
        case 'root': return 'bg-blue-100 border-blue-300 text-blue-800';
        case 'branch': return 'bg-green-100 border-green-300 text-green-800';
        case 'leaf': return 'bg-gray-50 border-gray-200 text-gray-700';
        default: return 'bg-white border-gray-200 text-gray-700';
      }
    };

    return (
      <div key={node.id} className="select-none">
        <div
          className={cn(
            'flex items-center gap-1 py-1.5 px-2 rounded-lg transition-all cursor-pointer',
            getNodeColor(),
            isSelected && 'ring-2 ring-blue-500 ring-offset-1',
            matched && 'ring-2 ring-yellow-400 ring-offset-1',
            'hover:shadow-sm'
          )}
          style={{ marginLeft: depth * 24 }}
        >
          {/* Expand/Collapse Button */}
          {hasChildren ? (
            <button
              onClick={(e) => {
                e.stopPropagation();
                toggleNode(node);
              }}
              className="p-0.5 rounded hover:bg-black/5 transition-colors"
            >
              {isExpanded ? (
                <ChevronDown className="w-4 h-4" />
              ) : (
                <ChevronRight className="w-4 h-4" />
              )}
            </button>
          ) : (
            <span className="w-5" />
          )}

          {/* Node Content */}
          <div
            className="flex-1 min-w-0"
            onClick={() => handleNodeClick(node)}
          >
            {renderNode ? (
              renderNode(node, isExpanded)
            ) : (
              <div className="flex flex-col">
                <span className="font-medium truncate">{node.label}</span>
                {node.description && (
                  <span className="text-xs opacity-70 truncate">{node.description}</span>
                )}
              </div>
            )}
          </div>

          {/* Child Count */}
          {hasChildren && (
            <span className="text-xs px-1.5 py-0.5 bg-black/10 rounded-full">
              {node.children?.length}
            </span>
          )}
        </div>

        {/* Children */}
        {hasChildren && isExpanded && (
          <div className="mt-1">
            {node.children?.map(child => renderTreeNode(child, depth + 1))}
          </div>
        )}
      </div>
    );
  };

  return (
    <div
      className={cn(
        'flex flex-col bg-white rounded-lg border border-gray-200 overflow-hidden transition-all',
        isFullscreen && 'fixed inset-0 z-50 rounded-none',
        className
      )}
    >
      {/* Toolbar */}
      <div className="flex items-center justify-between gap-2 p-3 border-b border-gray-200 bg-gray-50">
        <div className="flex items-center gap-2">
          {searchable && (
            <div className="relative">
              <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 w-4 h-4 text-gray-400" />
              <input
                type="text"
                placeholder="搜索节点..."
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
                className="pl-9 pr-3 py-1.5 text-sm border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500 w-48"
              />
            </div>
          )}
        </div>

        <div className="flex items-center gap-1">
          <button
            onClick={expandAll}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title="展开全部"
          >
            <Plus className="w-4 h-4" />
          </button>
          <button
            onClick={collapseAll}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title="折叠全部"
          >
            <Minus className="w-4 h-4" />
          </button>
          {zoomable && (
            <>
              <button
                onClick={() => setZoom(z => Math.max(0.5, z - 0.1))}
                className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
                title="缩小"
              >
                <span className="text-sm font-bold">−</span>
              </button>
              <span className="text-xs text-gray-500 w-12 text-center">
                {Math.round(zoom * 100)}%
              </span>
              <button
                onClick={() => setZoom(z => Math.min(2, z + 0.1))}
                className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
                title="放大"
              >
                <span className="text-sm font-bold">+</span>
              </button>
            </>
          )}
          <button
            onClick={() => setZoom(1)}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title="重置"
          >
            <RotateCcw className="w-4 h-4" />
          </button>
          <button
            onClick={() => setIsFullscreen(!isFullscreen)}
            className="p-1.5 text-gray-500 hover:text-gray-700 hover:bg-gray-200 rounded-lg transition-colors"
            title={isFullscreen ? '退出全屏' : '全屏'}
          >
            {isFullscreen ? <Minimize2 className="w-4 h-4" /> : <Maximize2 className="w-4 h-4" />}
          </button>
        </div>
      </div>

      {/* Tree Content */}
      <div
        className="flex-1 overflow-auto p-3"
        style={{ 
          transform: `scale(${zoom})`,
          transformOrigin: 'top left',
          minHeight: isFullscreen ? 'calc(100vh - 60px)' : 400
        }}
      >
        {renderTreeNode(data)}
      </div>

      {/* Status Bar */}
      <div className="px-3 py-2 border-t border-gray-200 bg-gray-50 text-xs text-gray-500">
        <span>已展开: {expandedNodes.size} 个节点</span>
        {searchQuery && (
          <span className="ml-4">搜索: "{searchQuery}"</span>
        )}
      </div>
    </div>
  );
};

/**
 * 将扁平数据转换为树形结构
 */
export function buildTree(
  items: Array<{ id: string; parentId: string | null; label: string; [key: string]: unknown }>,
  rootId: string | null = null
): TreeNode | null {
  const itemMap = new Map(items.map(item => [item.id, { ...item, children: [] as TreeNode[] }]));
  let root: TreeNode | null = null;

  items.forEach(item => {
    const node = itemMap.get(item.id)!;
    if (item.parentId === rootId) {
      root = node;
    } else {
      const parent = itemMap.get(item.parentId!);
      if (parent) {
        parent.children.push(node);
      }
    }
  });

  return root;
}

export default InteractiveTree;
