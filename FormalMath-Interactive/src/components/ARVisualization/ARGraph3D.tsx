import React, { useRef, useMemo } from 'react';
import { Canvas, useFrame } from '@react-three/fiber';
import { OrbitControls, Text, Line, Sphere, Html } from '@react-three/drei';
import * as THREE from 'three';

// 节点数据类型
interface GraphNode {
  id: string;
  label: string;
  position: [number, number, number];
  color?: string;
  size?: number;
  type?: 'concept' | 'theorem' | 'definition' | 'example';
}

// 边数据类型
interface GraphEdge {
  from: string;
  to: string;
  label?: string;
  color?: string;
  width?: number;
}

// 3D 图谱数据
interface Graph3DData {
  nodes: GraphNode[];
  edges: GraphEdge[];
}

interface ARGraph3DProps {
  data: Graph3DData;
  width?: number;
  height?: number;
  showLabels?: boolean;
  interactive?: boolean;
  onNodeClick?: (node: GraphNode) => void;
  className?: string;
}

// 节点组件
const Node: React.FC<{
  node: GraphNode;
  isHovered: boolean;
  onHover: (id: string | null) => void;
  onClick: () => void;
  showLabel: boolean;
}> = ({ node, isHovered, onHover, onClick, showLabel }) => {
  const meshRef = useRef<THREE.Mesh>(null);
  
  const colorMap: Record<string, string> = {
    concept: '#3b82f6',
    theorem: '#10b981',
    definition: '#f59e0b',
    example: '#8b5cf6',
  };

  const color = node.color || colorMap[node.type || 'concept'] || '#3b82f6';
  const size = node.size || 0.5;

  useFrame((state) => {
    if (meshRef.current && isHovered) {
      meshRef.current.scale.setScalar(1.2 + Math.sin(state.clock.elapsedTime * 3) * 0.05);
    } else if (meshRef.current) {
      meshRef.current.scale.setScalar(1);
    }
  });

  return (
    <group position={node.position}>
      <Sphere
        ref={meshRef}
        args={[size, 32, 32]}
        onPointerOver={() => onHover(node.id)}
        onPointerOut={() => onHover(null)}
        onClick={onClick}
      >
        <meshStandardMaterial
          color={color}
          emissive={isHovered ? color : '#000000'}
          emissiveIntensity={isHovered ? 0.3 : 0}
          roughness={0.3}
          metalness={0.2}
        />
      </Sphere>
      
      {showLabel && (
        <Html distanceFactor={10}>
          <div className="bg-black/70 text-white px-2 py-1 rounded text-xs whitespace-nowrap pointer-events-none">
            {node.label}
          </div>
        </Html>
      )}

      {isHovered && (
        <Html distanceFactor={8} position={[0, size + 0.5, 0]}>
          <div className="bg-white text-gray-800 px-3 py-2 rounded-lg shadow-lg whitespace-nowrap">
            <p className="font-medium">{node.label}</p>
            <p className="text-xs text-gray-500 capitalize">{node.type}</p>
          </div>
        </Html>
      )}
    </group>
  );
};

// 边组件
const Edge: React.FC<{
  edge: GraphEdge;
  nodes: GraphNode[];
}> = ({ edge, nodes }) => {
  const fromNode = nodes.find(n => n.id === edge.from);
  const toNode = nodes.find(n => n.id === edge.to);

  if (!fromNode || !toNode) return null;

  const points: [THREE.Vector3, THREE.Vector3] = [
    new THREE.Vector3(...fromNode.position),
    new THREE.Vector3(...toNode.position),
  ];

  return (
    <Line
      points={points}
      color={edge.color || '#94a3b8'}
      lineWidth={edge.width || 2}
    />
  );
};

// 场景组件
const Scene: React.FO<{
  data: Graph3DData;
  showLabels: boolean;
  interactive: boolean;
  onNodeClick?: (node: GraphNode) => void;
}> = ({ data, showLabels, interactive, onNodeClick }) => {
  const [hoveredNode, setHoveredNode] = React.useState<string | null>(null);
  const groupRef = useRef<THREE.Group>(null);

  useFrame((state) => {
    if (groupRef.current && !interactive) {
      groupRef.current.rotation.y = state.clock.elapsedTime * 0.1;
    }
  });

  // 计算场景中心
  const center = useMemo(() => {
    if (data.nodes.length === 0) return [0, 0, 0] as [number, number, number];
    
    const avgX = data.nodes.reduce((sum, n) => sum + n.position[0], 0) / data.nodes.length;
    const avgY = data.nodes.reduce((sum, n) => sum + n.position[1], 0) / data.nodes.length;
    const avgZ = data.nodes.reduce((sum, n) => sum + n.position[2], 0) / data.nodes.length;
    
    return [avgX, avgY, avgZ] as [number, number, number];
  }, [data.nodes]);

  return (
    <>
      <ambientLight intensity={0.5} />
      <pointLight position={[10, 10, 10]} intensity={1} />
      <pointLight position={[-10, -10, -10]} intensity={0.5} />
      
      <group ref={groupRef}>
        {/* 渲染边 */}
        {data.edges.map((edge, index) => (
          <Edge key={`edge-${index}`} edge={edge} nodes={data.nodes} />
        ))}

        {/* 渲染节点 */}
        {data.nodes.map((node) => (
          <Node
            key={node.id}
            node={node}
            isHovered={hoveredNode === node.id}
            onHover={interactive ? setHoveredNode : () => {}}
            onClick={() => interactive && onNodeClick?.(node)}
            showLabel={showLabels}
          />
        ))}
      </group>

      {/* 控制器 */}
      {interactive && (
        <OrbitControls
          target={center}
          enablePan={true}
          enableZoom={true}
          enableRotate={true}
        />
      )}
    </>
  );
};

// 主组件
export const ARGraph3D: React.FC<ARGraph3DProps> = ({
  data,
  width = 800,
  height = 600,
  showLabels = true,
  interactive = true,
  onNodeClick,
  className = '',
}) => {
  return (
    <div className={`rounded-lg overflow-hidden ${className}`} style={{ width, height }}>
      <Canvas
        camera={{ position: [10, 10, 10], fov: 50 }}
        style={{ background: '#0f172a' }}
      >
        <Scene
          data={data}
          showLabels={showLabels}
          interactive={interactive}
          onNodeClick={onNodeClick}
        />
      </Canvas>
    </div>
  );
};

// 示例数据生成器
export const generateSampleGraph = (): Graph3DData => {
  const nodes: GraphNode[] = [
    { id: '1', label: '数学分析', position: [0, 0, 0], type: 'concept', size: 0.8 },
    { id: '2', label: '极限', position: [3, 2, 1], type: 'definition', size: 0.6 },
    { id: '3', label: '连续性', position: [-2, 3, -1], type: 'concept', size: 0.6 },
    { id: '4', label: '导数', position: [2, -2, 2], type: 'definition', size: 0.6 },
    { id: '5', label: '积分', position: [-3, -1, 3], type: 'definition', size: 0.6 },
    { id: '6', label: '微积分基本定理', position: [0, 3, -2], type: 'theorem', size: 0.7 },
    { id: '7', label: '中值定理', position: [-2, -3, -2], type: 'theorem', size: 0.6 },
    { id: '8', label: '泰勒展开', position: [3, 0, -3], type: 'theorem', size: 0.6 },
    { id: '9', label: '函数极值', position: [1, 2, 3], type: 'example', size: 0.5 },
    { id: '10', label: '曲线面积', position: [-1, -2, 3], type: 'example', size: 0.5 },
  ];

  const edges: GraphEdge[] = [
    { from: '1', to: '2', label: '包含' },
    { from: '1', to: '3', label: '包含' },
    { from: '1', to: '4', label: '包含' },
    { from: '1', to: '5', label: '包含' },
    { from: '2', to: '3', label: '推导' },
    { from: '4', to: '6', label: '应用' },
    { from: '5', to: '6', label: '应用' },
    { from: '4', to: '7', label: '基础' },
    { from: '4', to: '8', label: '基础' },
    { from: '4', to: '9', label: '应用' },
    { from: '5', to: '10', label: '应用' },
  ];

  return { nodes, edges };
};

// 力导向布局计算器
export const calculateForceLayout = (
  nodes: GraphNode[],
  edges: GraphEdge[],
  iterations: number = 100
): GraphNode[] => {
  const newNodes = nodes.map(n => ({ ...n, position: [...n.position] as [number, number, number] }));
  
  const repulsionForce = 1;
  const attractionForce = 0.01;
  const springLength = 3;
  
  for (let i = 0; i < iterations; i++) {
    // 斥力
    for (let j = 0; j < newNodes.length; j++) {
      for (let k = j + 1; k < newNodes.length; k++) {
        const dx = newNodes[j].position[0] - newNodes[k].position[0];
        const dy = newNodes[j].position[1] - newNodes[k].position[1];
        const dz = newNodes[j].position[2] - newNodes[k].position[2];
        const dist = Math.sqrt(dx * dx + dy * dy + dz * dz) || 0.1;
        
        const force = repulsionForce / (dist * dist);
        const fx = (dx / dist) * force;
        const fy = (dy / dist) * force;
        const fz = (dz / dist) * force;
        
        newNodes[j].position[0] += fx;
        newNodes[j].position[1] += fy;
        newNodes[j].position[2] += fz;
        newNodes[k].position[0] -= fx;
        newNodes[k].position[1] -= fy;
        newNodes[k].position[2] -= fz;
      }
    }
    
    // 引力
    for (const edge of edges) {
      const fromNode = newNodes.find(n => n.id === edge.from);
      const toNode = newNodes.find(n => n.id === edge.to);
      
      if (fromNode && toNode) {
        const dx = toNode.position[0] - fromNode.position[0];
        const dy = toNode.position[1] - fromNode.position[1];
        const dz = toNode.position[2] - fromNode.position[2];
        const dist = Math.sqrt(dx * dx + dy * dy + dz * dz) || 0.1;
        
        const force = (dist - springLength) * attractionForce;
        const fx = (dx / dist) * force;
        const fy = (dy / dist) * force;
        const fz = (dz / dist) * force;
        
        fromNode.position[0] += fx;
        fromNode.position[1] += fy;
        fromNode.position[2] += fz;
        toNode.position[0] -= fx;
        toNode.position[1] -= fy;
        toNode.position[2] -= fz;
      }
    }
    
    // 中心引力（防止节点飞散）
    for (const node of newNodes) {
      node.position[0] *= 0.99;
      node.position[1] *= 0.99;
      node.position[2] *= 0.99;
    }
  }
  
  return newNodes;
};

export default ARGraph3D;
