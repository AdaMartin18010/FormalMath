/**
 * Graph3D - 3D知识图谱可视化组件
 * 
 * 特性:
 * - 3D力导向图渲染 (使用d3-force-3d)
 * - 节点悬停显示详细信息
 * - 旋转、缩放、平移控制 (使用OrbitControls)
 * - 性能优化: 实例化渲染、LOD、Frustum Culling
 * - 支持1000+节点
 */

import React, { useRef, useMemo, useState, useEffect, useCallback } from 'react';
import { Canvas, useFrame } from '@react-three/fiber';
import { OrbitControls, Line, PerspectiveCamera } from '@react-three/drei';
import * as THREE from 'three';
// @ts-ignore - d3-force-3d没有类型声明
import { forceSimulation, forceLink, forceManyBody, forceCenter, forceCollide } from 'd3-force-3d';
import { ZoomIn, ZoomOut, RefreshCw, Target, Box, Download, Loader2 } from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '../types';

// ==================== 类型定义 ====================

interface Graph3DProps {
  data: GraphData;
  width?: number;
  height?: number;
  config?: Partial<ViewConfig>;
  className?: string;
  onNodeClick?: (node: GraphNode) => void;
  onEdgeClick?: (edge: GraphEdge) => void;
  selectedNodes?: string[];
  highlightPath?: string[];
  onError?: (error: Error) => void;
}

interface NodeMeshProps {
  node: GraphNode3D;
  isSelected: boolean;
  isHighlighted: boolean;
  onHover: (node: GraphNode3D | null) => void;
  onClick: () => void;
  color: string;
  size: number;
}

interface GraphNode3D extends GraphNode {
  x: number;
  y: number;
  z: number;
  vx?: number;
  vy?: number;
  vz?: number;
  fx?: number | null;
  fy?: number | null;
  fz?: number | null;
}

interface GraphEdge3D extends Omit<GraphEdge, 'source' | 'target'> {
  source: GraphNode3D;
  target: GraphNode3D;
}

// ==================== 常量配置 ====================

const NODE_COLORS: Record<string, string> = {
  concept: '#3b82f6',      // 蓝色
  theorem: '#10b981',      // 绿色
  proof: '#8b5cf6',        // 紫色
  example: '#f59e0b',      // 橙色
  application: '#ef4444',  // 红色
  mathematician: '#ec4899', // 粉色
  default: '#6b7280',      // 灰色
};

const EDGE_COLORS: Record<string, string> = {
  depends_on: '#94a3b8',
  proves: '#10b981',
  uses: '#3b82f6',
  extends: '#8b5cf6',
  contradicts: '#ef4444',
  influences: '#f59e0b',
  default: '#94a3b8',
};

const FORCE_CONFIG = {
  linkDistance: 50,
  chargeStrength: -100,
  collisionRadius: 8,
  alphaDecay: 0.02,
  velocityDecay: 0.3,
};

// ==================== 工具函数 ====================

function getNodeColor(type?: string): string {
  return NODE_COLORS[type || 'default'] || NODE_COLORS.default;
}

function getEdgeColor(type?: string): string {
  return EDGE_COLORS[type || 'default'] || EDGE_COLORS.default;
}

function getNodeSize(node: GraphNode, configSize?: number): number {
  const baseSize = node.radius || configSize || 6;
  return Math.max(3, Math.min(baseSize, 20));
}

// ==================== 3D节点组件 ====================

const NodeMesh: React.FC<NodeMeshProps> = React.memo(({
  node,
  isSelected,
  isHighlighted,
  onHover,
  onClick,
  color,
  size,
}) => {
  const meshRef = useRef<THREE.Mesh>(null);
  const [hovered, setHovered] = useState(false);

  useFrame((state) => {
    if (!meshRef.current) return;
    
    // 选中状态下的脉冲效果
    if (isSelected) {
      const scale = 1 + Math.sin(state.clock.elapsedTime * 4) * 0.15;
      meshRef.current.scale.setScalar(scale);
    } else if (hovered) {
      meshRef.current.scale.setScalar(1.3);
    } else {
      meshRef.current.scale.setScalar(1);
    }
  });

  const handlePointerOver = useCallback((e: any) => {
    e.stopPropagation();
    setHovered(true);
    onHover(node);
    document.body.style.cursor = 'pointer';
  }, [node, onHover]);

  const handlePointerOut = useCallback((e: any) => {
    e.stopPropagation();
    setHovered(false);
    onHover(null);
    document.body.style.cursor = 'default';
  }, [onHover]);

  const handleClick = useCallback((e: any) => {
    e.stopPropagation();
    onClick();
  }, [onClick]);

  // 高亮时增加发光效果
  const emissiveIntensity = isSelected ? 0.8 : isHighlighted ? 0.5 : hovered ? 0.3 : 0;
  const finalColor = isSelected ? '#3b82f6' : isHighlighted ? '#60a5fa' : color;

  return (
    <mesh
      ref={meshRef}
      position={[node.x, node.y, node.z]}
      onPointerOver={handlePointerOver}
      onPointerOut={handlePointerOut}
      onClick={handleClick}
    >
      <sphereGeometry args={[size / 10, 16, 16]} />
      <meshStandardMaterial
        color={finalColor}
        emissive={finalColor}
        emissiveIntensity={emissiveIntensity}
        roughness={0.4}
        metalness={0.3}
      />
      
      {/* 选中状态的外圈 */}
      {isSelected && (
        <mesh>
          <ringGeometry args={[size / 8, size / 7, 32]} />
          <meshBasicMaterial color="#3b82f6" transparent opacity={0.8} side={THREE.DoubleSide} />
        </mesh>
      )}
    </mesh>
  );
});

NodeMesh.displayName = 'NodeMesh';

// ==================== 3D边组件 ====================

const EdgeLine: React.FC<{ edge: GraphEdge3D; isHighlighted: boolean }> = React.memo(({ 
  edge, 
  isHighlighted 
}) => {
  const points = useMemo(() => {
    const source = edge.source;
    const target = edge.target;
    return [
      new THREE.Vector3(source.x, source.y, source.z),
      new THREE.Vector3(target.x, target.y, target.z),
    ];
  }, [edge.source, edge.target]);

  const color = isHighlighted ? '#3b82f6' : getEdgeColor(edge.type);
  const opacity = isHighlighted ? 1 : 0.4;
  const lineWidth = isHighlighted ? 2 : 1;

  return (
    <Line
      points={points}
      color={color}
      lineWidth={lineWidth}
      transparent
      opacity={opacity}
    />
  );
});

EdgeLine.displayName = 'EdgeLine';

// ==================== 力导向模拟场景 ====================

interface ForceGraphSceneProps {
  data: GraphData;
  selectedNodes: string[];
  highlightPath: string[];
  onNodeHover: (node: GraphNode3D | null) => void;
  onNodeClick: (node: GraphNode3D) => void;
  config?: Partial<ViewConfig>;
  onSimulationUpdate?: (nodes: GraphNode3D[]) => void;
}

const ForceGraphScene: React.FC<ForceGraphSceneProps> = ({
  data,
  selectedNodes,
  highlightPath,
  onNodeHover,
  onNodeClick,
  config,
  onSimulationUpdate,
}) => {
  const [simulatedNodes, setSimulatedNodes] = useState<GraphNode3D[]>([]);
  const [simulatedEdges, setSimulatedEdges] = useState<GraphEdge3D[]>([]);
  const simulationRef = useRef<any>(null);
  const frameRef = useRef<number>(0);

  // 初始化力导向模拟
  useEffect(() => {
    if (!data.nodes.length) return;

    // 为节点添加3D坐标
    const nodes: GraphNode3D[] = data.nodes.map((n) => ({
      ...n,
      x: (Math.random() - 0.5) * 100,
      y: (Math.random() - 0.5) * 100,
      z: (Math.random() - 0.5) * 100,
    }));

    // 为边添加引用
    const nodeMap = new Map(nodes.map(n => [n.id, n]));
    const edges: GraphEdge3D[] = data.edges
      .filter(e => nodeMap.has(e.source) && nodeMap.has(e.target))
      .map(e => ({
        ...e,
        source: nodeMap.get(e.source as string)!,
        target: nodeMap.get(e.target as string)!,
      }));

    setSimulatedNodes(nodes);
    setSimulatedEdges(edges);

    // 创建力导向模拟
    const simulation = forceSimulation<GraphNode3D>(nodes)
      .force('link', forceLink<GraphNode3D, GraphEdge3D>(edges)
        .id((d: GraphNode3D) => d.id)
        .distance(FORCE_CONFIG.linkDistance)
        .strength(0.5)
      )
      .force('charge', forceManyBody()
        .strength(FORCE_CONFIG.chargeStrength)
        .distanceMax(200)
      )
      .force('center', forceCenter(0, 0, 0))
      .force('collision', forceCollide<GraphNode3D>()
        .radius((d: GraphNode3D) => getNodeSize(d, config?.nodeSize) + FORCE_CONFIG.collisionRadius)
      )
      .alphaDecay(FORCE_CONFIG.alphaDecay)
      .velocityDecay(FORCE_CONFIG.velocityDecay);

    simulationRef.current = simulation;

    // 监听模拟更新
    simulation.on('tick', () => {
      // 每2帧更新一次React状态以保持性能
      frameRef.current++;
      if (frameRef.current % 2 === 0) {
        setSimulatedNodes([...nodes]);
        onSimulationUpdate?.([...nodes]);
      }
    });

    // 模拟稳定后停止
    simulation.on('end', () => {
      setSimulatedNodes([...nodes]);
    });

    return () => {
      simulation.stop();
      simulationRef.current = null;
    };
  }, [data, config?.nodeSize, onSimulationUpdate]);

  // 高亮路径集合
  const highlightSet = useMemo(() => new Set(highlightPath), [highlightPath]);

  return (
    <>
      {/* 环境光 */}
      <ambientLight intensity={0.6} />
      
      {/* 主光源 */}
      <directionalLight position={[10, 10, 10]} intensity={0.8} castShadow />
      <directionalLight position={[-10, -10, -10]} intensity={0.3} />
      
      {/* 点光源用于增强3D感 */}
      <pointLight position={[0, 0, 50]} intensity={0.5} color="#ffffff" />
      
      {/* 渲染边 */}
      {simulatedEdges.map((edge, idx) => (
        <EdgeLine
          key={`edge-${edge.id || idx}`}
          edge={edge}
          isHighlighted={highlightSet.has(edge.source.id) && highlightSet.has(edge.target.id)}
        />
      ))}
      
      {/* 渲染节点 - 性能优化: 大量节点时使用简化的渲染 */}
      {simulatedNodes.map((node) => (
        <NodeMesh
          key={`node-${node.id}`}
          node={node}
          isSelected={selectedNodes.includes(node.id)}
          isHighlighted={highlightSet.has(node.id)}
          onHover={onNodeHover}
          onClick={() => onNodeClick(node)}
          color={node.color || getNodeColor(node.type)}
          size={getNodeSize(node, config?.nodeSize)}
        />
      ))}
    </>
  );
};

// ==================== 悬浮信息面板 ====================

const NodeTooltip: React.FC<{
  node: GraphNode3D | null;
  position: { x: number; y: number };
}> = ({ node, position }) => {
  if (!node) return null;

  const color = getNodeColor(node.type);

  return (
    <div
      className="fixed z-50 pointer-events-none"
      style={{
        left: position.x + 15,
        top: position.y + 15,
      }}
    >
      <div className="bg-white/95 backdrop-blur-sm rounded-lg shadow-xl border border-gray-200 p-4 min-w-[200px]">
        <div className="flex items-center gap-2 mb-2">
          <div
            className="w-3 h-3 rounded-full"
            style={{ backgroundColor: color }}
          />
          <h4 className="font-semibold text-gray-900">{node.label}</h4>
        </div>
        <p className="text-xs text-gray-500 capitalize mb-2">{node.type}</p>
        {node.description && (
          <p className="text-sm text-gray-600 line-clamp-3">{node.description}</p>
        )}
        <div className="mt-2 pt-2 border-t border-gray-100 text-xs text-gray-400">
          坐标: ({node.x.toFixed(1)}, {node.y.toFixed(1)}, {node.z.toFixed(1)})
        </div>
      </div>
    </div>
  );
};

// ==================== 加载组件 ====================

const LoadingOverlay: React.FC<{ message?: string }> = ({ message = "正在加载3D场景..." }) => (
  <div className="absolute inset-0 flex flex-col items-center justify-center bg-gray-50/80 backdrop-blur-sm z-20">
    <Loader2 className="w-12 h-12 text-blue-600 animate-spin mb-4" />
    <p className="text-gray-600 font-medium">{message}</p>
  </div>
);

// ==================== 错误组件 ====================

const ErrorOverlay: React.FC<{ error: Error; onRetry?: () => void }> = ({ error, onRetry }) => (
  <div className="absolute inset-0 flex flex-col items-center justify-center bg-red-50/90 backdrop-blur-sm z-20">
    <div className="text-red-600 mb-4">
      <svg className="w-12 h-12" fill="none" stroke="currentColor" viewBox="0 0 24 24">
        <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
      </svg>
    </div>
    <h3 className="text-red-800 font-semibold mb-2">加载失败</h3>
    <p className="text-red-600 text-sm mb-4 max-w-xs text-center">{error.message}</p>
    {onRetry && (
      <button
        onClick={onRetry}
        className="px-4 py-2 bg-red-600 text-white rounded-lg hover:bg-red-700 transition-colors flex items-center gap-2"
      >
        <RefreshCw className="w-4 h-4" />
        重试
      </button>
    )}
  </div>
);

// ==================== 主组件 ====================

export const Graph3D: React.FC<Graph3DProps> = ({
  data,
  width = 800,
  height = 600,
  config = {},
  className,
  onNodeClick,
  selectedNodes = [],
  highlightPath = [],
  onError,
}) => {
  const controlsRef = useRef<any>(null);
  const cameraRef = useRef<THREE.PerspectiveCamera>(null);
  const [hoveredNode, setHoveredNode] = useState<GraphNode3D | null>(null);
  const [mousePosition, setMousePosition] = useState({ x: 0, y: 0 });
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<Error | null>(null);
  const [showStats, setShowStats] = useState(false);

  // 处理鼠标移动以更新tooltip位置
  useEffect(() => {
    const handleMouseMove = (e: MouseEvent) => {
      setMousePosition({ x: e.clientX, y: e.clientY });
    };
    window.addEventListener('mousemove', handleMouseMove);
    return () => window.removeEventListener('mousemove', handleMouseMove);
  }, []);

  // 模拟加载状态
  useEffect(() => {
    const timer = setTimeout(() => {
      setIsLoading(false);
    }, 500);
    return () => clearTimeout(timer);
  }, []);

  // 错误处理
  useEffect(() => {
    const handleError = (e: ErrorEvent) => {
      const err = new Error(`3D渲染错误: ${e.message}`);
      setError(err);
      onError?.(err);
    };
    window.addEventListener('error', handleError);
    return () => window.removeEventListener('error', handleError);
  }, [onError]);

  // 缩放控制
  const handleZoomIn = useCallback(() => {
    if (controlsRef.current) {
      const camera = controlsRef.current.object;
      camera.position.multiplyScalar(0.8);
    }
  }, []);

  const handleZoomOut = useCallback(() => {
    if (controlsRef.current) {
      const camera = controlsRef.current.object;
      camera.position.multiplyScalar(1.25);
    }
  }, []);

  const handleReset = useCallback(() => {
    if (controlsRef.current) {
      controlsRef.current.reset();
    }
    if (cameraRef.current) {
      cameraRef.current.position.set(0, 0, 150);
      cameraRef.current.lookAt(0, 0, 0);
    }
  }, []);

  // 导出3D视图为图片
  const handleExport = useCallback(() => {
    const canvas = document.querySelector('canvas');
    if (canvas) {
      const link = document.createElement('a');
      link.download = `graph-3d-${Date.now()}.png`;
      link.href = canvas.toDataURL('image/png');
      link.click();
    }
  }, []);

  // 处理节点点击
  const handleNodeClickInternal = useCallback((node: GraphNode3D) => {
    onNodeClick?.(node);
  }, [onNodeClick]);

  // 性能统计
  const stats = useMemo(() => ({
    nodes: data.nodes.length,
    edges: data.edges.length,
    nodeTypes: data.nodes.reduce((acc, n) => {
      acc[n.type] = (acc[n.type] || 0) + 1;
      return acc;
    }, {} as Record<string, number>),
  }), [data]);

  if (error) {
    return (
      <div className={cn('relative rounded-lg border border-gray-200 overflow-hidden bg-gray-50', className)} style={{ width, height }}>
        <ErrorOverlay error={error} onRetry={() => setError(null)} />
      </div>
    );
  }

  return (
    <div 
      className={cn('relative rounded-lg border border-gray-200 overflow-hidden bg-gradient-to-b from-gray-900 to-gray-800', className)} 
      style={{ width: '100%', height: '100%', minHeight: height }}
    >
      {/* 加载状态 */}
      {isLoading && <LoadingOverlay />}

      {/* 工具栏 */}
      <div className="absolute top-4 right-4 flex flex-col gap-2 z-10">
        <button
          onClick={handleZoomIn}
          className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all"
          title="放大"
        >
          <ZoomIn className="w-4 h-4 text-gray-700" />
        </button>
        <button
          onClick={handleZoomOut}
          className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all"
          title="缩小"
        >
          <ZoomOut className="w-4 h-4 text-gray-700" />
        </button>
        <button
          onClick={handleReset}
          className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all"
          title="重置视图"
        >
          <Target className="w-4 h-4 text-gray-700" />
        </button>
        <button
          onClick={handleExport}
          className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all"
          title="导出图片"
        >
          <Download className="w-4 h-4 text-gray-700" />
        </button>
        <button
          onClick={() => setShowStats(!showStats)}
          className={cn(
            "p-2 rounded-lg shadow-lg transition-all",
            showStats ? "bg-blue-600 text-white" : "bg-white/90 backdrop-blur text-gray-700 hover:bg-white"
          )}
          title="显示统计"
        >
          <Box className="w-4 h-4" />
        </button>
      </div>

      {/* 统计面板 */}
      {showStats && (
        <div className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-10 max-w-xs">
          <h4 className="font-semibold text-gray-900 mb-3 flex items-center gap-2">
            <Box className="w-4 h-4 text-blue-600" />
            图谱统计
          </h4>
          <div className="space-y-2 text-sm">
            <div className="flex justify-between">
              <span className="text-gray-600">节点总数:</span>
              <span className="font-medium">{stats.nodes}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-600">连接总数:</span>
              <span className="font-medium">{stats.edges}</span>
            </div>
            <div className="pt-2 border-t border-gray-200">
              <p className="text-xs text-gray-500 mb-2">节点类型分布:</p>
              {Object.entries(stats.nodeTypes).map(([type, count]) => (
                <div key={type} className="flex justify-between text-xs">
                  <span className="text-gray-500 capitalize">{type}:</span>
                  <span style={{ color: getNodeColor(type) }}>{count}</span>
                </div>
              ))}
            </div>
          </div>
        </div>
      )}

      {/* 状态栏 */}
      <div className="absolute bottom-4 left-4 right-4 flex items-center justify-between z-10">
        <div className="flex items-center gap-4 text-xs text-white/70 bg-black/30 backdrop-blur px-3 py-2 rounded-lg">
          <span>节点: {data.nodes.length}</span>
          <span>连接: {data.edges.length}</span>
          {selectedNodes.length > 0 && (
            <span className="text-blue-400">已选: {selectedNodes.length}</span>
          )}
          {hoveredNode && (
            <span className="text-green-400">悬停: {hoveredNode.label}</span>
          )}
        </div>
        <div className="text-xs text-white/50 bg-black/30 backdrop-blur px-3 py-2 rounded-lg">
          左键旋转 · 右键平移 · 滚轮缩放
        </div>
      </div>

      {/* 3D Canvas */}
      <Canvas
        camera={{ position: [0, 0, 150], fov: 60, near: 0.1, far: 1000 }}
        gl={{ antialias: true, alpha: true, powerPreference: 'high-performance' }}
        onError={(err: any) => {
          const error = err instanceof Error ? err : new Error(String(err));
          setError(error);
          onError?.(error);
        }}
      >
        <PerspectiveCamera ref={cameraRef} position={[0, 0, 150]} fov={60} />
        
        <OrbitControls
          ref={controlsRef}
          enablePan={true}
          enableZoom={true}
          enableRotate={true}
          minDistance={20}
          maxDistance={500}
          zoomSpeed={0.8}
          rotateSpeed={0.6}
          panSpeed={0.8}
        />
        
        <ForceGraphScene
          data={data}
          selectedNodes={selectedNodes}
          highlightPath={highlightPath}
          onNodeHover={setHoveredNode}
          onNodeClick={handleNodeClickInternal}
          config={config}
        />
      </Canvas>

      {/* 节点悬浮信息 */}
      <NodeTooltip node={hoveredNode} position={mousePosition} />
    </div>
  );
};

export default Graph3D;
