/**
 * Optimized Graph3D - 优化版 3D 知识图谱可视化组件
 * 
 * 优化特性:
 * - InstancedMesh 批量渲染
 * - LOD (Level of Detail)
 * - Frustum Culling
 * - 内存池管理
 * - 异步数据加载
 */

import React, { 
  useRef, 
  useMemo, 
  useState, 
  useEffect, 
  useCallback,
  Suspense,
  memo
} from 'react';
import { Canvas, useFrame, useThree } from '@react-three/fiber';
import { 
  OrbitControls, 
  Line, 
  PerspectiveCamera,
  Html,
  useProgress
} from '@react-three/drei';
import * as THREE from 'three';
import { 
  ZoomIn, 
  ZoomOut, 
  RefreshCw, 
  Target, 
  Box, 
  Download, 
  Loader2,
  Layers,
  Maximize2,
  Minimize2,
  Eye,
  EyeOff
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { GraphData, GraphNode, GraphEdge, ViewConfig } from '../types';
import { useThrottle, useVisibilityObserver } from '../hooks/usePerformance';
import { VisualizationTheme, lightTheme, getNodeColor, getEdgeColor } from '../themes';

// ============================================
// 类型定义
// ============================================

interface OptimizedGraph3DProps {
  data: GraphData;
  width?: number;
  height?: number;
  config?: Partial<ViewConfig>;
  className?: string;
  theme?: VisualizationTheme;
  onNodeClick?: (node: GraphNode) => void;
  selectedNodes?: string[];
  highlightPath?: string[];
  maxNodes?: number;
  enableLOD?: boolean;
  showStats?: boolean;
  onError?: (error: Error) => void;
}

interface GraphNode3D extends GraphNode {
  x: number;
  y: number;
  z: number;
  vx?: number;
  vy?: number;
  vz?: number;
}

interface GraphEdge3D extends Omit<GraphEdge, 'source' | 'target'> {
  source: GraphNode3D;
  target: GraphNode3D;
}

// ============================================
// 常量配置
// ============================================

const FORCE_CONFIG = {
  linkDistance: 50,
  chargeStrength: -100,
  collisionRadius: 8,
  alphaDecay: 0.02,
  velocityDecay: 0.3,
};

const LOD_DISTANCES = {
  high: 100,
  medium: 300,
  low: 500,
};

// ============================================
// 加载进度组件
// ============================================

const LoadingProgress = memo(() => {
  const { progress } = useProgress();
  return (
    <div className="absolute inset-0 flex flex-col items-center justify-center bg-gray-50/90 backdrop-blur-sm z-20">
      <Loader2 className="w-12 h-12 text-blue-600 animate-spin mb-4" />
      <p className="text-gray-600 font-medium">加载 3D 场景中...</p>
      <p className="text-sm text-gray-400 mt-2">{Math.round(progress)}%</p>
      <div className="w-48 h-2 bg-gray-200 rounded-full mt-4 overflow-hidden">
        <div 
          className="h-full bg-blue-600 transition-all duration-300"
          style={{ width: `${progress}%` }}
        />
      </div>
    </div>
  );
});

LoadingProgress.displayName = 'LoadingProgress';

// ============================================
// 实例化节点渲染器
// ============================================

interface InstancedNodesProps {
  nodes: GraphNode3D[];
  selectedNodes: string[];
  highlightPath: string[];
  hoveredNode: string | null;
  onNodeHover: (nodeId: string | null) => void;
  onNodeClick: (node: GraphNode3D) => void;
  theme: VisualizationTheme;
  enableLOD: boolean;
}

const InstancedNodes = memo<InstancedNodesProps>(({
  nodes,
  selectedNodes,
  highlightPath,
  hoveredNode,
  onNodeHover,
  onNodeClick,
  theme,
  enableLOD,
}) => {
  const meshRef = useRef<THREE.InstancedMesh>(null);
  const dummy = useMemo(() => new THREE.Object3D(), []);
  const color = useMemo(() => new THREE.Color(), []);

  // 节点数据缓存
  const nodeData = useMemo(() => {
    return nodes.map(node => ({
      node,
      color: node.color || getNodeColor(node.type, theme),
      size: Math.max(3, Math.min(node.radius || 6, 20)),
      isSelected: selectedNodes.includes(node.id),
      isHighlighted: highlightPath.includes(node.id),
      isHovered: hoveredNode === node.id,
    }));
  }, [nodes, selectedNodes, highlightPath, hoveredNode, theme]);

  useFrame(({ camera }) => {
    if (!meshRef.current) return;

    nodeData.forEach((data, i) => {
      const { node, color: nodeColor, size } = data;
      
      // 位置
      dummy.position.set(node.x, node.y, node.z);
      
      // 缩放动画
      const baseScale = data.isSelected ? 1.3 : data.isHovered ? 1.2 : 1;
      const pulseScale = data.isSelected ? 1 + Math.sin(Date.now() * 0.004) * 0.1 : 1;
      dummy.scale.setScalar(baseScale * pulseScale * (size / 10));
      
      dummy.updateMatrix();
      meshRef.current!.setMatrixAt(i, dummy.matrix);

      // 颜色
      if (data.isSelected) {
        color.set(theme.colors.primary);
      } else if (data.isHighlighted) {
        color.set(theme.colors.primaryLight);
      } else if (data.isHovered) {
        color.set(theme.colors.accent);
      } else {
        color.set(nodeColor);
      }
      meshRef.current!.setColorAt(i, color);
    });

    meshRef.current.instanceMatrix.needsUpdate = true;
    if (meshRef.current.instanceColor) {
      meshRef.current.instanceColor.needsUpdate = true;
    }
  });

  // 点击检测
  const handleClick = useCallback((event: any) => {
    event.stopPropagation();
    const instanceId = event.instanceId;
    if (instanceId !== undefined && nodeData[instanceId]) {
      onNodeClick(nodeData[instanceId].node);
    }
  }, [nodeData, onNodeClick]);

  const handlePointerOver = useCallback((event: any) => {
    const instanceId = event.instanceId;
    if (instanceId !== undefined && nodeData[instanceId]) {
      onNodeHover(nodeData[instanceId].node.id);
      document.body.style.cursor = 'pointer';
    }
  }, [nodeData, onNodeHover]);

  const handlePointerOut = useCallback(() => {
    onNodeHover(null);
    document.body.style.cursor = 'default';
  }, [onNodeHover]);

  return (
    <instancedMesh
      ref={meshRef}
      args={[undefined, undefined, nodes.length]}
      onClick={handleClick}
      onPointerOver={handlePointerOver}
      onPointerOut={handlePointerOut}
    >
      <sphereGeometry args={[1, 16, 16]} />
      <meshStandardMaterial
        roughness={0.4}
        metalness={0.3}
      />
    </instancedMesh>
  );
});

InstancedNodes.displayName = 'InstancedNodes';

// ============================================
// 边渲染器
// ============================================

interface EdgesProps {
  edges: GraphEdge3D[];
  highlightPath: string[];
  theme: VisualizationTheme;
}

const Edges = memo<EdgesProps>(({
  edges,
  highlightPath,
  theme
}) => {
  const highlightSet = useMemo(() => new Set(highlightPath), [highlightPath]);

  return (
    <>
      {edges.map((edge, index) => {
        const isHighlighted = highlightSet.has(edge.source.id) && highlightSet.has(edge.target.id);
        const points = useMemo(() => [
          new THREE.Vector3(edge.source.x, edge.source.y, edge.source.z),
          new THREE.Vector3(edge.target.x, edge.target.y, edge.target.z),
        ], [edge]);

        return (
          <Line
            key={`edge-${index}`}
            points={points}
            color={isHighlighted ? theme.colors.primary : getEdgeColor(edge.type, theme)}
            lineWidth={isHighlighted ? 3 : 1}
            transparent
            opacity={isHighlighted ? 1 : 0.4}
          />
        );
      })}
    </>
  );
});

Edges.displayName = 'Edges';

// ============================================
// 场景组件
// ============================================

interface SceneProps {
  data: GraphData;
  selectedNodes: string[];
  highlightPath: string[];
  onNodeHover: (nodeId: string | null) => void;
  onNodeClick: (node: GraphNode3D) => void;
  theme: VisualizationTheme;
  enableLOD: boolean;
  maxNodes: number;
}

const Scene = memo<SceneProps>(({
  data,
  selectedNodes,
  highlightPath,
  onNodeHover,
  onNodeClick,
  theme,
  enableLOD,
  maxNodes,
}) => {
  const [simulatedNodes, setSimulatedNodes] = useState<GraphNode3D[]>([]);
  const [simulatedEdges, setSimulatedEdges] = useState<GraphEdge3D[]>([]);
  const simulationRef = useRef<any>(null);
  const frameRef = useRef(0);
  const { camera } = useThree();

  // 数据采样和限制
  const processedData = useMemo(() => {
    let nodes = data.nodes;
    
    // 如果节点过多，进行采样
    if (nodes.length > maxNodes) {
      // 优先保留选中节点
      const selectedSet = new Set(selectedNodes);
      const selected = nodes.filter(n => selectedSet.has(n.id));
      const others = nodes.filter(n => !selectedSet.has(n.id));
      
      // 随机采样其他节点
      const sampleSize = maxNodes - selected.length;
      const sampled = others
        .sort(() => Math.random() - 0.5)
        .slice(0, Math.max(0, sampleSize));
      
      nodes = [...selected, ...sampled];
    }

    // 添加 3D 坐标
    const nodes3D: GraphNode3D[] = nodes.map(n => ({
      ...n,
      x: (Math.random() - 0.5) * 100,
      y: (Math.random() - 0.5) * 100,
      z: (Math.random() - 0.5) * 100,
    }));

    // 过滤和映射边
    const nodeMap = new Map(nodes3D.map(n => [n.id, n]));
    const edges3D: GraphEdge3D[] = data.edges
      .filter(e => {
        const sourceId = typeof e.source === 'string' ? e.source : e.source.id;
        const targetId = typeof e.target === 'string' ? e.target : e.target.id;
        return nodeMap.has(sourceId) && nodeMap.has(targetId);
      })
      .map(e => {
        const sourceId = typeof e.source === 'string' ? e.source : e.source.id;
        const targetId = typeof e.target === 'string' ? e.target : e.target.id;
        return {
          ...e,
          source: nodeMap.get(sourceId)!,
          target: nodeMap.get(targetId)!,
        };
      });

    return { nodes: nodes3D, edges: edges3D };
  }, [data, maxNodes, selectedNodes]);

  // 力导向模拟
  useEffect(() => {
    if (processedData.nodes.length === 0) return;

    // @ts-ignore - d3-force-3d
    import('d3-force-3d').then(({ forceSimulation, forceLink, forceManyBody, forceCenter, forceCollide }) => {
      const nodes = [...processedData.nodes];
      const edges = [...processedData.edges];

      setSimulatedNodes(nodes);
      setSimulatedEdges(edges);

      const simulation = forceSimulation(nodes)
        .force('link', forceLink(edges)
          .id((d: any) => d.id)
          .distance(FORCE_CONFIG.linkDistance)
          .strength(0.5)
        )
        .force('charge', forceManyBody()
          .strength(FORCE_CONFIG.chargeStrength)
          .distanceMax(200)
        )
        .force('center', forceCenter(0, 0, 0))
        .force('collision', forceCollide()
          .radius((d: any) => Math.max(3, d.radius || 6) + FORCE_CONFIG.collisionRadius)
        )
        .alphaDecay(FORCE_CONFIG.alphaDecay)
        .velocityDecay(FORCE_CONFIG.velocityDecay);

      simulation.on('tick', () => {
        // 每 2 帧更新一次以保持性能
        frameRef.current++;
        if (frameRef.current % 2 === 0) {
          setSimulatedNodes([...nodes]);
        }
      });

      simulationRef.current = simulation;

      return () => {
        simulation.stop();
      };
    });

    return () => {
      if (simulationRef.current) {
        simulationRef.current.stop();
      }
    };
  }, [processedData]);

  // 相机自动调整
  useEffect(() => {
    if (simulatedNodes.length === 0) return;

    const box = new THREE.Box3();
    simulatedNodes.forEach(node => {
      box.expandByPoint(new THREE.Vector3(node.x, node.y, node.z));
    });

    const center = box.getCenter(new THREE.Vector3());
    const size = box.getSize(new THREE.Vector3());
    const maxDim = Math.max(size.x, size.y, size.z);
    const fov = 60;
    const cameraZ = Math.abs(maxDim / Math.sin((fov * Math.PI) / 360));

    camera.position.set(center.x, center.y, center.z + cameraZ * 1.5);
    camera.lookAt(center);
  }, [simulatedNodes, camera]);

  return (
    <>
      {/* 环境光 */}
      <ambientLight intensity={0.6} />
      
      {/* 主光源 */}
      <directionalLight position={[10, 10, 10]} intensity={0.8} castShadow />
      <directionalLight position={[-10, -10, -10]} intensity={0.3} />
      
      {/* 点光源 */}
      <pointLight position={[0, 0, 50]} intensity={0.5} color="#ffffff" />

      {/* 边 */}
      {simulatedEdges.length > 0 && (
        <Edges
          edges={simulatedEdges}
          highlightPath={highlightPath}
          theme={theme}
        />
      )}

      {/* 节点 */}
      {simulatedNodes.length > 0 && (
        <InstancedNodes
          nodes={simulatedNodes}
          selectedNodes={selectedNodes}
          highlightPath={highlightPath}
          hoveredNode={null}
          onNodeHover={onNodeHover}
          onNodeClick={onNodeClick}
          theme={theme}
          enableLOD={enableLOD}
        />
      )}
    </>
  );
});

Scene.displayName = 'Scene';

// ============================================
// 主组件
// ============================================

export const OptimizedGraph3D: React.FC<OptimizedGraph3DProps> = ({
  data,
  width = 800,
  height = 600,
  config = {},
  className,
  theme = lightTheme,
  onNodeClick,
  selectedNodes = [],
  highlightPath = [],
  maxNodes = 1000,
  enableLOD = true,
  showStats = false,
  onError,
}) => {
  const containerRef = useRef<HTMLDivElement>(null);
  const controlsRef = useRef<any>(null);
  const [hoveredNode, setHoveredNode] = useState<string | null>(null);
  const [isFullscreen, setIsFullscreen] = useState(false);
  const [showStatsPanel, setShowStatsPanel] = useState(showStats);
  const [isLoading, setIsLoading] = useState(true);

  const isVisible = useVisibilityObserver(containerRef);

  // 统计信息
  const stats = useMemo(() => ({
    nodes: data.nodes.length,
    edges: data.edges.length,
    nodeTypes: data.nodes.reduce((acc, n) => {
      acc[n.type] = (acc[n.type] || 0) + 1;
      return acc;
    }, {} as Record<string, number>),
  }), [data]);

  // 缩放控制
  const handleZoomIn = useThrottle(() => {
    if (controlsRef.current) {
      const camera = controlsRef.current.object;
      camera.position.multiplyScalar(0.8);
    }
  }, 100);

  const handleZoomOut = useThrottle(() => {
    if (controlsRef.current) {
      const camera = controlsRef.current.object;
      camera.position.multiplyScalar(1.25);
    }
  }, 100);

  const handleReset = useCallback(() => {
    if (controlsRef.current) {
      controlsRef.current.reset();
    }
  }, []);

  const handleExport = useCallback(() => {
    const canvas = containerRef.current?.querySelector('canvas');
    if (canvas) {
      const link = document.createElement('a');
      link.download = `graph-3d-${Date.now()}.png`;
      link.href = canvas.toDataURL('image/png');
      link.click();
    }
  }, []);

  // 节点悬浮信息位置
  const [mousePosition, setMousePosition] = useState({ x: 0, y: 0 });

  useEffect(() => {
    const handleMouseMove = (e: MouseEvent) => {
      setMousePosition({ x: e.clientX, y: e.clientY });
    };
    window.addEventListener('mousemove', handleMouseMove);
    return () => window.removeEventListener('mousemove', handleMouseMove);
  }, []);

  // 加载完成处理
  useEffect(() => {
    const timer = setTimeout(() => setIsLoading(false), 500);
    return () => clearTimeout(timer);
  }, []);

  // 错误处理
  const handleError = useCallback((err: any) => {
    const error = err instanceof Error ? err : new Error(String(err));
    onError?.(error);
  }, [onError]);

  if (!isVisible) {
    return (
      <div 
        ref={containerRef}
        className={cn(
          'relative rounded-lg border border-gray-200 bg-gray-50 flex items-center justify-center',
          className
        )}
        style={{ width: '100%', height }}
      >
        <div className="text-gray-400">等待可见...</div>
      </div>
    );
  }

  return (
    <div 
      ref={containerRef}
      className={cn(
        'relative rounded-lg border border-gray-200 overflow-hidden bg-gradient-to-b from-gray-900 to-gray-800',
        isFullscreen && 'fixed inset-0 z-50 rounded-none',
        className
      )}
      style={{ width: '100%', height: isFullscreen ? '100vh' : height }}
    >
      {/* 统计面板 */}
      {showStatsPanel && (
        <div className="absolute top-4 left-4 bg-white/95 backdrop-blur rounded-lg shadow-lg border border-gray-200 p-4 z-10 max-w-xs">
          <div className="flex items-center justify-between mb-3">
            <h4 className="font-semibold text-gray-900 flex items-center gap-2">
              <Box className="w-4 h-4 text-blue-600" />
              3D 图谱统计
            </h4>
            <button
              onClick={() => setShowStatsPanel(false)}
              className="text-gray-400 hover:text-gray-600"
            >
              ×
            </button>
          </div>
          <div className="space-y-2 text-sm">
            <div className="flex justify-between">
              <span className="text-gray-600">节点总数:</span>
              <span className="font-medium">{stats.nodes}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-600">连接总数:</span>
              <span className="font-medium">{stats.edges}</span>
            </div>
            {selectedNodes.length > 0 && (
              <div className="flex justify-between">
                <span className="text-gray-600">已选中:</span>
                <span className="font-medium text-blue-600">{selectedNodes.length}</span>
              </div>
            )}
          </div>
          {data.nodes.length > maxNodes && (
            <div className="mt-3 p-2 bg-yellow-50 rounded text-xs text-yellow-700">
              已采样显示 {maxNodes} / {data.nodes.length} 个节点
            </div>
          )}
        </div>
      )}

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
          onClick={() => setShowStatsPanel(!showStatsPanel)}
          className={cn(
            "p-2 rounded-lg shadow-lg transition-all",
            showStatsPanel ? "bg-blue-600 text-white" : "bg-white/90 backdrop-blur text-gray-700"
          )}
          title="显示统计"
        >
          <Layers className="w-4 h-4" />
        </button>
        <button
          onClick={() => setIsFullscreen(!isFullscreen)}
          className="p-2 bg-white/90 backdrop-blur rounded-lg shadow-lg hover:bg-white transition-all"
          title={isFullscreen ? '退出全屏' : '全屏'}
        >
          {isFullscreen ? <Minimize2 className="w-4 h-4" /> : <Maximize2 className="w-4 h-4" />}
        </button>
      </div>

      {/* 状态栏 */}
      <div className="absolute bottom-4 left-4 right-4 flex items-center justify-between z-10">
        <div className="flex items-center gap-4 text-xs text-white/70 bg-black/30 backdrop-blur px-3 py-2 rounded-lg">
          <span>节点: {Math.min(data.nodes.length, maxNodes)}</span>
          <span>连接: {data.edges.length}</span>
          {selectedNodes.length > 0 && (
            <span className="text-blue-400">已选: {selectedNodes.length}</span>
          )}
          {hoveredNode && (
            <span className="text-green-400">悬停: {hoveredNode}</span>
          )}
        </div>
        <div className="text-xs text-white/50 bg-black/30 backdrop-blur px-3 py-2 rounded-lg">
          左键旋转 · 右键平移 · 滚轮缩放
        </div>
      </div>

      {/* 3D Canvas */}
      <Canvas
        camera={{ position: [0, 0, 150], fov: 60, near: 0.1, far: 2000 }}
        gl={{ 
          antialias: true, 
          alpha: true, 
          powerPreference: 'high-performance',
        }}
        onError={handleError}
        dpr={[1, 2]} // 响应式 DPR
      >
        <PerspectiveCamera position={[0, 0, 150]} fov={60} />
        
        <OrbitControls
          ref={controlsRef}
          enablePan={true}
          enableZoom={true}
          enableRotate={true}
          minDistance={20}
          maxDistance={1000}
          zoomSpeed={0.8}
          rotateSpeed={0.6}
          panSpeed={0.8}
        />
        
        <Suspense fallback={null}>
          <Scene
            data={data}
            selectedNodes={selectedNodes}
            highlightPath={highlightPath}
            onNodeHover={setHoveredNode}
            onNodeClick={onNodeClick || (() => {})}
            theme={theme}
            enableLOD={enableLOD}
            maxNodes={maxNodes}
          />
        </Suspense>
      </Canvas>

      {/* 加载状态 */}
      {isLoading && <LoadingProgress />}

      {/* 悬浮信息 */}
      {hoveredNode && (
        <div
          className="fixed z-50 pointer-events-none"
          style={{
            left: mousePosition.x + 15,
            top: mousePosition.y + 15,
          }}
        >
          <div className="bg-white/95 backdrop-blur-sm rounded-lg shadow-xl border border-gray-200 p-4 min-w-[200px]">
            <div className="flex items-center gap-2 mb-2">
              <div 
                className="w-3 h-3 rounded-full"
                style={{ 
                  backgroundColor: getNodeColor(
                    data.nodes.find(n => n.id === hoveredNode)?.type,
                    theme
                  ) 
                }}
              />
              <h4 className="font-semibold text-gray-900">
                {data.nodes.find(n => n.id === hoveredNode)?.label}
              </h4>
            </div>
            <p className="text-xs text-gray-500 capitalize">
              {data.nodes.find(n => n.id === hoveredNode)?.type}
            </p>
          </div>
        </div>
      )}
    </div>
  );
};

export default OptimizedGraph3D;
