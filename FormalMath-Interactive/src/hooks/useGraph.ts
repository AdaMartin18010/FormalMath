// ==================== 图数据Hook ====================

import { useState, useCallback, useMemo } from 'react';
import type { GraphData, GraphNode, GraphEdge, SearchFilter } from '@types';
import { 
  filterGraphData, 
  calculateGraphStats, 
  findShortestPath,
  calculateNodeCentrality 
} from '@utils/helpers';

interface UseGraphReturn {
  data: GraphData;
  setData: (data: GraphData) => void;
  selectedNodes: string[];
  selectedEdges: string[];
  selectNode: (nodeId: string, multi?: boolean) => void;
  selectEdge: (edgeId: string, multi?: boolean) => void;
  clearSelection: () => void;
  filteredData: GraphData;
  applyFilter: (filter: SearchFilter) => void;
  clearFilter: () => void;
  stats: ReturnType<typeof calculateGraphStats>;
  findPath: (startId: string, endId: string) => string[] | null;
  getNodeNeighbors: (nodeId: string) => { nodes: GraphNode[]; edges: GraphEdge[] };
  highlightPath: string[];
  setHighlightPath: (path: string[]) => void;
}

export function useGraph(initialData: GraphData = { nodes: [], edges: [] }): UseGraphReturn {
  const [data, setData] = useState<GraphData>(initialData);
  const [selectedNodes, setSelectedNodes] = useState<string[]>([]);
  const [selectedEdges, setSelectedEdges] = useState<string[]>([]);
  const [filter, setFilter] = useState<SearchFilter | null>(null);
  const [highlightPath, setHighlightPath] = useState<string[]>([]);

  // 节点选择
  const selectNode = useCallback((nodeId: string, multi = false) => {
    setSelectedNodes(prev => {
      if (multi) {
        return prev.includes(nodeId)
          ? prev.filter(id => id !== nodeId)
          : [...prev, nodeId];
      }
      return prev.includes(nodeId) && prev.length === 1 ? [] : [nodeId];
    });
  }, []);

  // 边选择
  const selectEdge = useCallback((edgeId: string, multi = false) => {
    setSelectedEdges(prev => {
      if (multi) {
        return prev.includes(edgeId)
          ? prev.filter(id => id !== edgeId)
          : [...prev, edgeId];
      }
      return prev.includes(edgeId) && prev.length === 1 ? [] : [edgeId];
    });
  }, []);

  // 清除选择
  const clearSelection = useCallback(() => {
    setSelectedNodes([]);
    setSelectedEdges([]);
  }, []);

  // 应用过滤器
  const applyFilter = useCallback((searchFilter: SearchFilter) => {
    setFilter(searchFilter);
  }, []);

  // 清除过滤器
  const clearFilter = useCallback(() => {
    setFilter(null);
  }, []);

  // 过滤后的数据
  const filteredData = useMemo(() => {
    if (!filter) return data;
    
    return filterGraphData(
      data,
      (node) => {
        if (filter.query && !node.label.toLowerCase().includes(filter.query.toLowerCase())) {
          return false;
        }
        if (filter.nodeTypes?.length && !filter.nodeTypes.includes(node.type)) {
          return false;
        }
        if (filter.status?.length && !filter.status.includes(node.status)) {
          return false;
        }
        return true;
      },
      (edge) => {
        // 可根据需要添加边的过滤条件
        return true;
      }
    );
  }, [data, filter]);

  // 统计信息
  const stats = useMemo(() => calculateGraphStats(filteredData), [filteredData]);

  // 查找路径
  const findPath = useCallback((startId: string, endId: string) => {
    return findShortestPath(data, startId, endId);
  }, [data]);

  // 获取节点邻居
  const getNodeNeighbors = useCallback((nodeId: string) => {
    const connectedEdgeIds = new Set<string>();
    const neighborNodeIds = new Set<string>();

    data.edges.forEach(edge => {
      if (edge.source === nodeId) {
        connectedEdgeIds.add(edge.id);
        neighborNodeIds.add(edge.target);
      } else if (edge.target === nodeId) {
        connectedEdgeIds.add(edge.id);
        neighborNodeIds.add(edge.source);
      }
    });

    return {
      nodes: data.nodes.filter(n => neighborNodeIds.has(n.id)),
      edges: data.edges.filter(e => connectedEdgeIds.has(e.id)),
    };
  }, [data]);

  return {
    data,
    setData,
    selectedNodes,
    selectedEdges,
    selectNode,
    selectEdge,
    clearSelection,
    filteredData,
    applyFilter,
    clearFilter,
    stats,
    findPath,
    getNodeNeighbors,
    highlightPath,
    setHighlightPath,
  };
}
