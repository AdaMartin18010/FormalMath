import React, { useMemo, useState } from 'react';
import { Canvas } from '@react-three/fiber';
import { OrbitControls, Grid, Html } from '@react-three/drei';
import * as THREE from 'three';

// 函数类型
interface MathFunction {
  id: string;
  name: string;
  expression: string;
  func: (x: number, y: number) => number;
  color?: string;
  domain?: { xMin: number; xMax: number; yMin: number; yMax: number };
  range?: { zMin: number; zMax: number };
}

interface FunctionPlot3DProps {
  functions: MathFunction[];
  width?: number;
  height?: number;
  resolution?: number;
  showGrid?: boolean;
  showAxes?: boolean;
  showLabels?: boolean;
  interactive?: boolean;
  className?: string;
}

// 3D 曲面组件
const FunctionSurface: React.FC<{
  mathFunc: MathFunction;
  resolution: number;
}> = ({ mathFunc, resolution }) => {
  const geometry = useMemo(() => {
    const domain = mathFunc.domain || { xMin: -5, xMax: 5, yMin: -5, yMax: 5 };
    const { xMin, xMax, yMin, yMax } = domain;
    
    const positions: number[] = [];
    const colors: number[] =;
    const indices: number[] = [];
    
    const color = new THREE.Color(mathFunc.color || '#3b82f6');
    
    // 生成网格点
    for (let i = 0; i <= resolution; i++) {
      for (let j = 0; j <= resolution; j++) {
        const x = xMin + (xMax - xMin) * (i / resolution);
        const y = yMin + (yMax - yMin) * (j / resolution);
        const z = mathFunc.func(x, y);
        
        positions.push(x, z, y);
        
        // 根据高度设置颜色
        const heightRatio = (z + 5) / 10;
        const pointColor = color.clone().multiplyScalar(0.5 + heightRatio * 0.5);
        colors.push(pointColor.r, pointColor.g, pointColor.b);
      }
    }
    
    // 生成索引
    for (let i = 0; i < resolution; i++) {
      for (let j = 0; j < resolution; j++) {
        const a = i * (resolution + 1) + j;
        const b = a + 1;
        const c = (i + 1) * (resolution + 1) + j;
        const d = c + 1;
        
        indices.push(a, c, b);
        indices.push(b, c, d);
      }
    }
    
    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
    geo.setAttribute('color', new THREE.Float32BufferAttribute(colors, 3));
    geo.setIndex(indices);
    geo.computeVertexNormals();
    
    return geo;
  }, [mathFunc, resolution]);

  return (
    <mesh geometry={geometry}>
      <meshStandardMaterial
        vertexColors
        side={THREE.DoubleSide}
        roughness={0.5}
        metalness={0.1}
        wireframe={false}
      />
    </mesh>
  );
};

// 坐标轴组件
const Axes: React.FC<{ size: number }> = ({ size }) => {
  return (
    <group>
      {/* X轴 - 红色 */}
      <line>
        <bufferGeometry>
          <bufferAttribute
            attach="attributes-position"
            count={2}
            array={new Float32Array([-size, 0, 0, size, 0, 0])}
            itemSize={3}
          />
        </bufferGeometry>
        <lineBasicMaterial color="#ef4444" linewidth={2} />
      </line>
      
      {/* Y轴 - 绿色 */}
      <line>
        <bufferGeometry>
          <bufferAttribute
            attach="attributes-position"
            count={2}
            array={new Float32Array([0, -size, 0, 0, size, 0])}
            itemSize={3}
          />
        </bufferGeometry>
        <lineBasicMaterial color="#22c55e" linewidth={2} />
      </line>
      
      {/* Z轴 - 蓝色 */}
      <line>
        <bufferGeometry>
          <bufferAttribute
            attach="attributes-position"
            count={2}
            array={new Float32Array([0, 0, -size, 0, 0, size])}
            itemSize={3}
          />
        </bufferGeometry>
        <lineBasicMaterial color="#3b82f6" linewidth={2} />
      </line>

      {/* 轴标签 */}
      <Html position={[size + 0.5, 0, 0]}>
        <div className="text-red-500 font-bold text-lg">X</div>
      </Html>
      <Html position={[0, size + 0.5, 0]}>
        <div className="text-green-500 font-bold text-lg">Y</div>
      </Html>
      <Html position={[0, 0, size + 0.5]}>
        <div className="text-blue-500 font-bold text-lg">Z</div>
      </Html>
    </group>
  );
};

// 主组件
export const FunctionPlot3D: React.FC<FunctionPlot3DProps> = ({
  functions,
  width = 800,
  height = 600,
  resolution = 50,
  showGrid = true,
  showAxes = true,
  showLabels = true,
  interactive = true,
  className = '',
}) => {
  const [selectedFunction, setSelectedFunction] = useState<string>(functions[0]?.id || '');
  const [wireframe, setWireframe] = useState(false);

  const currentFunction = functions.find(f => f.id === selectedFunction);

  return (
    <div className={`${className}`}>
      {/* 控制面板 */}
      <div className="mb-4 flex flex-wrap items-center gap-4">
        <select
          value={selectedFunction}
          onChange={(e) => setSelectedFunction(e.target.value)}
          className="px-4 py-2 border border-gray-300 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
        >
          {functions.map((f) => (
            <option key={f.id} value={f.id}>
              {f.name} ({f.expression})
            </option>
          ))}
        </select>

        <label className="flex items-center gap-2 cursor-pointer">
          <input
            type="checkbox"
            checked={wireframe}
            onChange={(e) => setWireframe(e.target.checked)}
            className="rounded"
          />
          <span className="text-sm text-gray-700">线框模式</span>
        </label>

        {currentFunction && (
          <div className="text-sm text-gray-600">
            定义域: x∈[{currentFunction.domain?.xMin ?? -5}, {currentFunction.domain?.xMax ?? 5}], 
            y∈[{currentFunction.domain?.yMin ?? -5}, {currentFunction.domain?.yMax ?? 5}]
          </div>
        )}
      </div>

      {/* 3D 画布 */}
      <div 
        className="rounded-lg overflow-hidden border border-gray-200"
        style={{ width, height }}
      >
        <Canvas
          camera={{ position: [8, 8, 8], fov: 50 }}
          style={{ background: '#f8fafc' }}
        >
          <ambientLight intensity={0.6} />
          <directionalLight position={[5, 10, 5]} intensity={1} />
          <directionalLight position={[-5, -10, -5]} intensity={0.3} />

          {showGrid && (
            <Grid
              args={[20, 20]}
              cellSize={1}
              cellThickness={0.5}
              cellColor="#94a3b8"
              sectionSize={5}
              sectionThickness={1}
              sectionColor="#64748b"
              fadeDistance={25}
              fadeStrength={1}
              infiniteGrid
            />
          )}

          {showAxes && <Axes size={6} />}

          {currentFunction && (
            <group>
              <FunctionSurface 
                mathFunc={currentFunction} 
                resolution={resolution} 
              />
              {wireframe && (
                <FunctionSurface 
                  mathFunc={{ ...currentFunction, color: '#000000' }} 
                  resolution={resolution} 
                />
              )}
            </group>
          )}

          {interactive && (
            <OrbitControls
              enablePan={true}
              enableZoom={true}
              enableRotate={true}
              minDistance={3}
              maxDistance={30}
            />
          )}
        </Canvas>
      </div>

      {/* 函数信息 */}
      {currentFunction && (
        <div className="mt-4 p-4 bg-gray-50 rounded-lg">
          <h4 className="font-medium text-gray-800">{currentFunction.name}</h4>
          <p className="text-gray-600 mt-1">表达式: {currentFunction.expression}</p>
          <div 
            className="mt-2 inline-block w-4 h-4 rounded"
            style={{ backgroundColor: currentFunction.color || '#3b82f6' }}
          />
          <span className="ml-2 text-sm text-gray-500">函数颜色</span>
        </div>
      )}
    </div>
  );
};

// 预设函数库
export const presetFunctions: MathFunction[] = [
  {
    id: 'sine-2d',
    name: '正弦波',
    expression: 'z = sin(x) + sin(y)',
    func: (x, y) => Math.sin(x) + Math.sin(y),
    color: '#3b82f6',
    domain: { xMin: -6, xMax: 6, yMin: -6, yMax: 6 },
  },
  {
    id: 'paraboloid',
    name: '抛物面',
    expression: 'z = x² + y²',
    func: (x, y) => x * x + y * y,
    color: '#ef4444',
    domain: { xMin: -3, xMax: 3, yMin: -3, yMax: 3 },
  },
  {
    id: 'saddle',
    name: '马鞍面',
    expression: 'z = x² - y²',
    func: (x, y) => x * x - y * y,
    color: '#22c55e',
    domain: { xMin: -3, xMax: 3, yMin: -3, yMax: 3 },
  },
  {
    id: 'ripple',
    name: '涟漪',
    expression: 'z = sin(√(x²+y²)) / √(x²+y²)',
    func: (x, y) => {
      const r = Math.sqrt(x * x + y * y);
      return r === 0 ? 1 : Math.sin(r * 3) / (r * 0.5);
    },
    color: '#8b5cf6',
    domain: { xMin: -8, xMax: 8, yMin: -8, yMax: 8 },
  },
  {
    id: 'gaussian',
    name: '高斯分布',
    expression: 'z = e^(-(x²+y²)/2)',
    func: (x, y) => Math.exp(-(x * x + y * y) / 2),
    color: '#f59e0b',
    domain: { xMin: -4, xMax: 4, yMin: -4, yMax: 4 },
  },
  {
    id: 'peaks',
    name: '峰函数',
    expression: 'z = 3(1-x)²e^(-x²-(y+1)²) - ...',
    func: (x, y) => {
      return (
        3 * Math.pow(1 - x, 2) * Math.exp(-x * x - Math.pow(y + 1, 2)) -
        10 * (x / 5 - Math.pow(x, 3) - Math.pow(y, 5)) * Math.exp(-x * x - y * y) -
        1 / 3 * Math.exp(-Math.pow(x + 1, 2) - y * y)
      );
    },
    color: '#ec4899',
    domain: { xMin: -3, xMax: 3, yMin: -3, yMax: 3 },
  },
  {
    id: 'sombrero',
    name: '墨西哥帽',
    expression: 'z = sin(√(x²+y²)) / √(x²+y²)',
    func: (x, y) => {
      const r = Math.sqrt(x * x + y * y);
      return r === 0 ? 1 : Math.sin(r) / r;
    },
    color: '#14b8a6',
    domain: { xMin: -10, xMax: 10, yMin: -10, yMax: 10 },
  },
  {
    id: 'hyperbolic',
    name: '双曲抛物面',
    expression: 'z = xy',
    func: (x, y) => x * y,
    color: '#f97316',
    domain: { xMin: -4, xMax: 4, yMin: -4, yMax: 4 },
  },
];

export default FunctionPlot3D;
