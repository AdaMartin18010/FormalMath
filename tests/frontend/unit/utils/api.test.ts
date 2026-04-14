import {
  fetchKnowledgeGraph,
  fetchSubgraphByDomain,
  fetchNodeNeighbors,
  searchNodes,
  fetchNodeDetail,
  createNode,
  updateNode,
  deleteNode,
  fetchShortestPath,
  fetchGraphStats,
  importGraphData,
  calculateLayout,
} from '@api/graph';

jest.mock('@api/client', () => ({
  get: jest.fn(),
  post: jest.fn(),
  put: jest.fn(),
  del: jest.fn(),
}));

import { get, post, put, del } from '@api/client';

describe('API图数据工具函数', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('fetchKnowledgeGraph 应该调用正确的接口', async () => {
    const mockData = { nodes: [], edges: [] };
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: mockData });

    const result = await fetchKnowledgeGraph();
    expect(get).toHaveBeenCalledWith('/graph/knowledge');
    expect(result).toEqual({ success: true, data: mockData });
  });

  it('fetchSubgraphByDomain 应该传递 domain 和 depth', async () => {
    const mockData = { nodes: [{ id: '1' }], edges: [] };
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: mockData });

    await fetchSubgraphByDomain('algebra', 3);
    expect(get).toHaveBeenCalledWith('/graph/domain/algebra', { params: { depth: 3 } });
  });

  it('fetchNodeNeighbors 应该传递 nodeId 和 depth', async () => {
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: {} });

    await fetchNodeNeighbors('node-1', 2);
    expect(get).toHaveBeenCalledWith('/graph/node/node-1/neighbors', { params: { depth: 2 } });
  });

  it('searchNodes 应该调用 post 并传递 filter', async () => {
    const mockResults = [{ id: '1', label: '群论' }];
    (post as jest.Mock).mockResolvedValueOnce({ success: true, data: mockResults });

    const filter = { query: '群论', types: ['concept'] };
    await searchNodes(filter);
    expect(post).toHaveBeenCalledWith('/graph/search', filter);
  });

  it('fetchNodeDetail 应该调用 get 并传递 nodeId', async () => {
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: {} });

    await fetchNodeDetail('node-1');
    expect(get).toHaveBeenCalledWith('/graph/nodes/node-1');
  });

  it('createNode 应该调用 post 并传递 node 数据', async () => {
    const node = { label: '新节点', type: 'concept' as const, size: 10 };
    (post as jest.Mock).mockResolvedValueOnce({ success: true, data: { id: 'new-1', ...node } });

    await createNode(node);
    expect(post).toHaveBeenCalledWith('/graph/nodes', node);
  });

  it('updateNode 应该调用 put 并传递 updates', async () => {
    const updates = { label: '更新后的节点' };
    (put as jest.Mock).mockResolvedValueOnce({ success: true, data: {} });

    await updateNode('node-1', updates);
    expect(put).toHaveBeenCalledWith('/graph/nodes/node-1', updates);
  });

  it('deleteNode 应该调用 del 并传递 nodeId', async () => {
    (del as jest.Mock).mockResolvedValueOnce({ success: true, data: undefined });

    await deleteNode('node-1');
    expect(del).toHaveBeenCalledWith('/graph/nodes/node-1');
  });

  it('fetchShortestPath 应该传递 source 和 target', async () => {
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: { path: [], distance: 0 } });

    await fetchShortestPath('a', 'b');
    expect(get).toHaveBeenCalledWith('/graph/path', { params: { source: 'a', target: 'b' } });
  });

  it('fetchGraphStats 应该调用 /graph/stats', async () => {
    (get as jest.Mock).mockResolvedValueOnce({ success: true, data: {} });

    await fetchGraphStats();
    expect(get).toHaveBeenCalledWith('/graph/stats');
  });

  it('importGraphData 应该调用 post 并传递数据', async () => {
    const data = { nodes: [], edges: [] };
    (post as jest.Mock).mockResolvedValueOnce({ success: true, data: { imported: 0, failed: 0 } });

    await importGraphData(data);
    expect(post).toHaveBeenCalledWith('/graph/import', data);
  });

  it('calculateLayout 应该调用 post 并传递算法参数', async () => {
    const data = { nodes: [], edges: [] };
    (post as jest.Mock).mockResolvedValueOnce({ success: true, data });

    await calculateLayout(data, 'hierarchical');
    expect(post).toHaveBeenCalledWith('/graph/layout', { data, algorithm: 'hierarchical' });
  });
});
