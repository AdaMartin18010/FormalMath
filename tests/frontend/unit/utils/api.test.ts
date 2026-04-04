import { 
  getConcepts, 
  getConceptById, 
  searchConcepts,
  getGraphData 
} from '../../../FormalMath-Interactive/src/api/graph';

// Mock fetch
global.fetch = jest.fn();

describe('API工具函数', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('getConcepts', () => {
    it('应该成功获取概念列表', async () => {
      const mockConcepts = [
        { id: '1', name: '群论' },
        { id: '2', name: '环论' }
      ];
      
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => mockConcepts
      });
      
      const result = await getConcepts();
      
      expect(fetch).toHaveBeenCalledWith('/api/concepts');
      expect(result).toEqual(mockConcepts);
    });

    it('应该处理API错误', async () => {
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error'
      });
      
      await expect(getConcepts()).rejects.toThrow('Failed to fetch concepts');
    });

    it('应该处理网络错误', async () => {
      (fetch as jest.Mock).mockRejectedValueOnce(new Error('Network error'));
      
      await expect(getConcepts()).rejects.toThrow('Network error');
    });
  });

  describe('getConceptById', () => {
    it('应该成功获取单个概念', async () => {
      const mockConcept = { id: '1', name: '群论', description: '代数结构' };
      
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => mockConcept
      });
      
      const result = await getConceptById('1');
      
      expect(fetch).toHaveBeenCalledWith('/api/concepts/1');
      expect(result).toEqual(mockConcept);
    });

    it('应该处理404错误', async () => {
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: false,
        status: 404,
        statusText: 'Not Found'
      });
      
      await expect(getConceptById('999')).rejects.toThrow('Concept not found');
    });
  });

  describe('searchConcepts', () => {
    it('应该成功搜索概念', async () => {
      const mockResults = [
        { id: '1', name: '群论', relevance: 0.95 },
        { id: '2', name: '群同态', relevance: 0.85 }
      ];
      
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => mockResults
      });
      
      const result = await searchConcepts('群');
      
      expect(fetch).toHaveBeenCalledWith('/api/concepts/search?q=群');
      expect(result).toEqual(mockResults);
    });

    it('应该处理空搜索词', async () => {
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => []
      });
      
      const result = await searchConcepts('');
      
      expect(result).toEqual([]);
    });
  });

  describe('getGraphData', () => {
    it('应该成功获取图谱数据', async () => {
      const mockGraphData = {
        nodes: [{ id: '1', name: '群论' }],
        edges: [{ source: '1', target: '2' }]
      };
      
      (fetch as jest.Mock).mockResolvedValueOnce({
        ok: true,
        json: async () => mockGraphData
      });
      
      const result = await getGraphData();
      
      expect(fetch).toHaveBeenCalledWith('/api/graph');
      expect(result).toEqual(mockGraphData);
    });
  });
});
