import { renderHook } from '@testing-library/react';
import useD3 from '@hooks/useD3';

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
  it('应该正确初始化并返回 svgRef', () => {
    const renderFn = jest.fn();
    const { result } = renderHook(() => useD3(renderFn, []));
    
    expect(result.current).toBeDefined();
    expect(result.current.current).toBeNull();
  });
});
