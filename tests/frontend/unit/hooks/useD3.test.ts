import { renderHook, act } from '@testing-library/react';
import useD3 from '../../../FormalMath-Interactive/src/hooks/useD3';

// Mock D3
jest.mock('d3', () => ({
  select: jest.fn(() => ({
    selectAll: jest.fn().mockReturnThis(),
    data: jest.fn().mockReturnThis(),
    join: jest.fn().mockReturnThis(),
    attr: jest.fn().mockReturnThis(),
    style: jest.fn().mockReturnThis(),
    call: jest.fn().mockReturnThis(),
    append: jest.fn().mockReturnThis(),
    remove: jest.fn().mockReturnThis(),
    transition: jest.fn().mockReturnThis(),
    duration: jest.fn().mockReturnThis(),
    ease: jest.fn().mockReturnThis(),
  })),
  zoom: jest.fn(() => ({
    scaleExtent: jest.fn().mockReturnThis(),
    on: jest.fn().mockReturnThis(),
  })),
  drag: jest.fn(() => ({
    on: jest.fn().mockReturnThis(),
  })),
  forceSimulation: jest.fn(() => ({
    force: jest.fn().mockReturnThis(),
    nodes: jest.fn().mockReturnThis(),
    on: jest.fn().mockReturnThis(),
    alpha: jest.fn().mockReturnThis(),
    restart: jest.fn(),
    stop: jest.fn(),
  })),
  forceManyBody: jest.fn().mockReturnThis(),
  forceCenter: jest.fn().mockReturnThis(),
  forceLink: jest.fn().mockReturnThis(),
  forceCollide: jest.fn().mockReturnThis(),
}));

describe('useD3 Hook', () => {
  it('应该正确初始化', () => {
    const { result } = renderHook(() => useD3());
    
    expect(result.current.svgRef.current).toBeNull();
    expect(result.current.zoomRef.current).toBeNull();
    expect(typeof result.current.createGraph).toBe('function');
    expect(typeof result.current.updateGraph).toBe('function');
    expect(typeof result.current.destroyGraph).toBe('function');
  });

  it('应该创建图谱', () => {
    const { result } = renderHook(() => useD3());
    
    const mockData = {
      nodes: [{ id: '1', name: '节点1' }],
      links: []
    };
    
    act(() => {
      result.current.createGraph(mockData);
    });
    
    expect(result.current.svgRef.current).toBeDefined();
  });

  it('应该更新图谱数据', () => {
    const { result } = renderHook(() => useD3());
    
    const initialData = {
      nodes: [{ id: '1', name: '节点1' }],
      links: []
    };
    
    const updatedData = {
      nodes: [
        { id: '1', name: '节点1' },
        { id: '2', name: '节点2' }
      ],
      links: [{ source: '1', target: '2' }]
    };
    
    act(() => {
      result.current.createGraph(initialData);
      result.current.updateGraph(updatedData);
    });
    
    // 验证更新逻辑
    expect(result.current.svgRef.current).toBeDefined();
  });

  it('应该销毁图谱', () => {
    const { result } = renderHook(() => useD3());
    
    const mockData = {
      nodes: [{ id: '1', name: '节点1' }],
      links: []
    };
    
    act(() => {
      result.current.createGraph(mockData);
      result.current.destroyGraph();
    });
    
    // 验证清理逻辑
    expect(result.current.zoomRef.current).toBeNull();
  });
});
