// ==================== 图数据API ====================

import { get, post, put, del } from './client';
import type { 
  GraphData, 
  KnowledgeGraphData, 
  GraphNode, 
  GraphEdge,
  SearchFilter,
  ApiResponse,
  EvolutionData 
} from '@types';

/**
 * 获取完整知识图谱
 */
export async function fetchKnowledgeGraph(): Promise<ApiResponse<KnowledgeGraphData>> {
  return get<KnowledgeGraphData>('/graph/knowledge');
}

/**
 * 获取子图（按领域）
 */
export async function fetchSubgraphByDomain(
  domain: string,
  depth: number = 2
): Promise<ApiResponse<GraphData>> {
  return get<GraphData>(`/graph/domain/${domain}`, { params: { depth } });
}

/**
 * 获取节点邻居
 */
export async function fetchNodeNeighbors(
  nodeId: string,
  depth: number = 1
): Promise<ApiResponse<GraphData>> {
  return get<GraphData>(`/graph/node/${nodeId}/neighbors`, { params: { depth } });
}

/**
 * 搜索节点
 */
export async function searchNodes(
  filter: SearchFilter
): Promise<ApiResponse<GraphNode[]>> {
  return post<GraphNode[]>('/graph/search', filter);
}

/**
 * 获取节点详情
 */
export async function fetchNodeDetail(nodeId: string): Promise<ApiResponse<GraphNode>> {
  return get<GraphNode>(`/graph/nodes/${nodeId}`);
}

/**
 * 创建节点
 */
export async function createNode(
  node: Omit<GraphNode, 'id'>
): Promise<ApiResponse<GraphNode>> {
  return post<GraphNode>('/graph/nodes', node);
}

/**
 * 更新节点
 */
export async function updateNode(
  nodeId: string,
  updates: Partial<GraphNode>
): Promise<ApiResponse<GraphNode>> {
  return put<GraphNode>(`/graph/nodes/${nodeId}`, updates);
}

/**
 * 删除节点
 */
export async function deleteNode(nodeId: string): Promise<ApiResponse<void>> {
  return del<void>(`/graph/nodes/${nodeId}`);
}

/**
 * 创建边
 */
export async function createEdge(
  edge: Omit<GraphEdge, 'id'>
): Promise<ApiResponse<GraphEdge>> {
  return post<GraphEdge>('/graph/edges', edge);
}

/**
 * 更新边
 */
export async function updateEdge(
  edgeId: string,
  updates: Partial<GraphEdge>
): Promise<ApiResponse<GraphEdge>> {
  return put<GraphEdge>(`/graph/edges/${edgeId}`, updates);
}

/**
 * 删除边
 */
export async function deleteEdge(edgeId: string): Promise<ApiResponse<void>> {
  return del<void>(`/graph/edges/${edgeId}`);
}

/**
 * 获取最短路径
 */
export async function fetchShortestPath(
  sourceId: string,
  targetId: string
): Promise<ApiResponse<{ path: string[]; distance: number }>> {
  return get('/graph/path', { params: { source: sourceId, target: targetId } });
}

/**
 * 获取图的演化历史
 */
export async function fetchGraphEvolution(
  nodeId?: string
): Promise<ApiResponse<EvolutionData>> {
  const url = nodeId ? `/graph/evolution?nodeId=${nodeId}` : '/graph/evolution';
  return get<EvolutionData>(url);
}

/**
 * 获取图统计信息
 */
export async function fetchGraphStats(): Promise<ApiResponse<{
  nodeCount: number;
  edgeCount: number;
  avgDegree: number;
  density: number;
  topNodes: { id: string; label: string; degree: number }[];
}>> {
  return get('/graph/stats');
}

/**
 * 批量导入图数据
 */
export async function importGraphData(
  data: GraphData
): Promise<ApiResponse<{ imported: number; failed: number }>> {
  return post('/graph/import', data);
}

/**
 * 导出图数据
 */
export async function exportGraphData(
  format: 'json' | 'csv' | 'graphml'
): Promise<Blob> {
  const response = await fetch(`/api/graph/export?format=${format}`);
  return response.blob();
}

/**
 * 获取推荐的节点连接
 */
export async function fetchRecommendedConnections(
  nodeId: string,
  limit: number = 5
): Promise<ApiResponse<{ node: GraphNode; score: number; reason: string }[]>> {
  return get(`/graph/nodes/${nodeId}/recommendations`, { params: { limit } });
}

/**
 * 获取图布局计算结果
 */
export async function calculateLayout(
  data: GraphData,
  algorithm: 'force' | 'hierarchical' | 'circular' = 'force'
): Promise<ApiResponse<GraphData>> {
  return post<GraphData>('/graph/layout', { data, algorithm });
}
