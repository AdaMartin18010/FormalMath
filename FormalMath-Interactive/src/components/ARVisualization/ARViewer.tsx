import React, { useState, useEffect, useRef, useCallback } from 'react';
import { Camera, X, RotateCcw, Expand, Info, Layers } from 'lucide-react';

// WebXR 类型声明
declare global {
  interface Navigator {
    xr?: XRSystem;
  }
}

interface XRSystem {
  isSessionSupported(mode: 'inline' | 'immersive-vr' | 'immersive-ar'): Promise<boolean>;
  requestSession(mode: 'immersive-ar', options?: XRSessionInit): Promise<XRSession>;
}

interface XRSessionInit {
  requiredFeatures?: string[];
  optionalFeatures?: string[];
}

interface XRSession {
  addEventListener(event: string, callback: () => void): void;
  removeEventListener(event: string, callback: () => void): void;
  requestReferenceSpace(type: 'local' | 'local-floor' | 'viewer'): Promise<XRReferenceSpace>;
  requestAnimationFrame(callback: (time: number, frame: XRFrame) => void): number;
  end(): Promise<void>;
  renderState: XRRenderState;
  updateRenderState(state: { baseLayer?: XRWebGLLayer }): void;
}

interface XRRenderState {
  baseLayer?: XRWebGLLayer;
}

interface XRReferenceSpace {
  // 简化类型定义
}

interface XRFrame {
  getViewerPose(referenceSpace: XRReferenceSpace): XRViewerPose | null;
  session: XRSession;
}

interface XRViewerPose {
  views: XRView[];
  transform: XRRigidTransform;
}

interface XRView {
  eye: 'left' | 'right' | 'none';
  projectionMatrix: Float32Array;
  transform: XRRigidTransform;
}

interface XRRigidTransform {
  position: DOMPointReadOnly;
  orientation: DOMPointReadOnly;
  matrix: Float32Array;
  inverse: XRRigidTransform;
}

interface XRWebGLLayer {
  framebuffer: WebGLFramebuffer;
  framebufferWidth: number;
  framebufferHeight: number;
  getViewport(view: XRView): XRViewport;
}

interface XRViewport {
  x: number;
  y: number;
  width: number;
  height: number;
}

interface DOMPointReadOnly {
  x: number;
  y: number;
  z: number;
  w: number;
}

// AR 模型类型
interface ARModel {
  id: string;
  name: string;
  type: 'geometry' | 'graph' | 'function' | 'molecule' | 'crystal';
  url: string;
  thumbnail?: string;
  description?: string;
  scale: number;
  position?: { x: number; y: number; z: number };
  rotation?: { x: number; y: number; z: number };
}

interface ARViewerProps {
  model?: ARModel;
  models?: ARModel[];
  onClose?: () => void;
  onModelSelect?: (model: ARModel) => void;
  showModelSelector?: boolean;
  className?: string;
}

export const ARViewer: React.FC<ARViewerProps> = ({
  model,
  models = [],
  onClose,
  onModelSelect,
  showModelSelector = true,
  className = '',
}) => {
  const [isSupported, setIsSupported] = useState<boolean | null>(null);
  const [isSessionActive, setIsSessionActive] = useState(false);
  const [selectedModel, setSelectedModel] = useState<ARModel | null>(model || null);
  const [showInfo, setShowInfo] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [placementMode, setPlacementMode] = useState(true);
  
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const sessionRef = useRef<XRSession | null>(null);
  const glRef = useRef<WebGLRenderingContext | null>(null);
  const animationFrameRef = useRef<number | null>(null);
  const referenceSpaceRef = useRef<XRReferenceSpace | null>(null);

  // 检查 WebXR 支持
  useEffect(() => {
    const checkSupport = async () => {
      if (!navigator.xr) {
        setIsSupported(false);
        return;
      }

      try {
        const supported = await navigator.xr.isSessionSupported('immersive-ar');
        setIsSupported(supported);
      } catch {
        setIsSupported(false);
      }
    };

    checkSupport();
  }, []);

  // 启动 AR 会话
  const startARSession = async () => {
    if (!navigator.xr || !canvasRef.current) return;

    try {
      const session = await navigator.xr.requestSession('immersive-ar', {
        requiredFeatures: ['hit-test', 'dom-overlay'],
        optionalFeatures: ['light-estimation'],
      });

      sessionRef.current = session;

      // 初始化 WebGL
      const gl = canvasRef.current.getContext('webgl', { 
        xrCompatible: true,
        alpha: true,
      });
      
      if (!gl) {
        throw new Error('无法初始化 WebGL');
      }

      glRef.current = gl;

      // 创建 XR WebGL 层
      const xrLayer = new XRWebGLLayer(session, gl);
      session.updateRenderState({ baseLayer: xrLayer });

      // 获取参考空间
      const referenceSpace = await session.requestReferenceSpace('local');
      referenceSpaceRef.current = referenceSpace;

      // 设置会话事件监听
      session.addEventListener('end', onSessionEnd);

      setIsSessionActive(true);
      setPlacementMode(true);

      // 开始渲染循环
      renderLoop();
    } catch (err) {
      setError(`启动 AR 失败: ${err instanceof Error ? err.message : String(err)}`);
    }
  };

  // 结束 AR 会话
  const endARSession = async () => {
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
      animationFrameRef.current = null;
    }

    if (sessionRef.current) {
      await sessionRef.current.end();
      sessionRef.current = null;
    }

    setIsSessionActive(false);
  };

  // 会话结束回调
  const onSessionEnd = () => {
    sessionRef.current = null;
    setIsSessionActive(false);
  };

  // 渲染循环
  const renderLoop = () => {
    if (!sessionRef.current || !glRef.current) return;

    const onXRFrame = (time: number, frame: XRFrame) => {
      if (!sessionRef.current) return;

      const session = frame.session;
      const gl = glRef.current!;
      const xrLayer = session.renderState.baseLayer;

      if (!xrLayer) return;

      const pose = frame.getViewerPose(referenceSpaceRef.current!);

      if (pose) {
        // 绑定 framebuffer
        gl.bindFramebuffer(gl.FRAMEBUFFER, xrLayer.framebuffer);
        gl.clearColor(0, 0, 0, 0);
        gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

        // 渲染每个视图
        for (const view of pose.views) {
          const viewport = xrLayer.getViewport(view);
          gl.viewport(viewport.x, viewport.y, viewport.width, viewport.height);

          // 这里应该调用实际的 3D 渲染逻辑
          renderScene(gl, view, pose);
        }
      }

      animationFrameRef.current = session.requestAnimationFrame(onXRFrame);
    };

    animationFrameRef.current = sessionRef.current.requestAnimationFrame(onXRFrame);
  };

  // 渲染场景（简化版）
  const renderScene = (
    gl: WebGLRenderingContext, 
    view: XRView, 
    pose: XRViewerPose
  ) => {
    // 这是一个简化的渲染示例
    // 实际实现中应该加载和渲染 3D 模型
    
    // 设置视图矩阵和投影矩阵
    const viewMatrix = view.transform.inverse.matrix;
    const projectionMatrix = view.projectionMatrix;

    // 这里可以添加实际的模型渲染代码
    // 例如使用 Three.js 或其他 3D 库
  };

  // 选择模型
  const handleModelSelect = (model: ARModel) => {
    setSelectedModel(model);
    onModelSelect?.(model);
  };

  // 重置模型位置
  const resetModelPosition = () => {
    setPlacementMode(true);
  };

  // 清理
  useEffect(() => {
    return () => {
      endARSession();
    };
  }, []);

  if (isSupported === null) {
    return (
      <div className={`flex items-center justify-center p-8 ${className}`}>
        <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-500" />
      </div>
    );
  }

  if (isSupported === false) {
    return (
      <div className={`p-6 bg-yellow-50 rounded-lg ${className}`}>
        <div className="flex items-start gap-3">
          <Info className="text-yellow-600 mt-0.5" size={20} />
          <div>
            <h3 className="font-medium text-yellow-800">AR 不支持</h3>
            <p className="mt-1 text-sm text-yellow-700">
              您的设备或浏览器不支持 WebXR AR 功能。请使用支持 AR 的移动设备，如 Android 设备上的 Chrome 浏览器。
            </p>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className={`relative ${className}`}>
      {/* AR Canvas */}
      <canvas
        ref={canvasRef}
        className={`w-full h-full ${isSessionActive ? 'block' : 'hidden'}`}
        style={{ touchAction: 'none' }}
      />

      {/* 启动界面 */}
      {!isSessionActive && (
        <div className="bg-gray-900 rounded-lg overflow-hidden">
          {/* 模型选择器 */}
          {showModelSelector && models.length > 0 && (
            <div className="p-4">
              <h3 className="text-white font-medium mb-3">选择 3D 模型</h3>
              <div className="grid grid-cols-2 sm:grid-cols-3 gap-3">
                {models.map((m) => (
                  <button
                    key={m.id}
                    onClick={() => handleModelSelect(m)}
                    className={`
                      p-3 rounded-lg border-2 transition-all
                      ${selectedModel?.id === m.id
                        ? 'border-blue-500 bg-blue-500/20'
                        : 'border-gray-700 bg-gray-800 hover:border-gray-600'
                      }
                    `}
                  >
                    {m.thumbnail ? (
                      <img
                        src={m.thumbnail}
                        alt={m.name}
                        className="w-full aspect-square object-cover rounded mb-2"
                      />
                    ) : (
                      <div className="w-full aspect-square bg-gray-700 rounded mb-2 flex items-center justify-center">
                        <Layers className="text-gray-500" size={24} />
                      </div>
                    )}
                    <p className="text-white text-sm font-medium truncate">{m.name}</p>
                    <p className="text-gray-400 text-xs truncate">{m.type}</p>
                  </button>
                ))}
              </div>
            </div>
          )}

          {/* 选中模型信息 */}
          {selectedModel && (
            <div className="px-4 pb-4">
              <div className="bg-gray-800 rounded-lg p-4">
                <h4 className="text-white font-medium">{selectedModel.name}</h4>
                <p className="text-gray-400 text-sm mt-1">
                  {selectedModel.description || '暂无描述'}
                </p>
                <button
                  onClick={() => setShowInfo(!showInfo)}
                  className="mt-2 text-blue-400 text-sm hover:text-blue-300"
                >
                  {showInfo ? '收起信息' : '查看更多信息'}
                </button>
                
                {showInfo && (
                  <div className="mt-3 pt-3 border-t border-gray-700 text-sm text-gray-300">
                    <p>类型: {selectedModel.type}</p>
                    <p>默认缩放: {selectedModel.scale}x</p>
                  </div>
                )}
              </div>
            </div>
          )}

          {/* 启动按钮 */}
          <div className="p-4 pt-0">
            <button
              onClick={startARSession}
              disabled={!selectedModel}
              className={`
                w-full py-4 rounded-lg font-medium flex items-center justify-center gap-2
                transition-all
                ${selectedModel
                  ? 'bg-blue-500 hover:bg-blue-600 text-white'
                  : 'bg-gray-700 text-gray-400 cursor-not-allowed'
                }
              `}
            >
              <Camera size={24} />
              {selectedModel ? '启动 AR 查看器' : '请先选择一个模型'}
            </button>
          </div>
        </div>
      )}

      {/* AR 控制面板 */}
      {isSessionActive && (
        <>
          {/* 关闭按钮 */}
          <button
            onClick={endARSession}
            className="absolute top-4 right-4 p-3 bg-white/90 backdrop-blur rounded-full shadow-lg"
          >
            <X size={24} className="text-gray-800" />
          </button>

          {/* 模型控制 */}
          <div className="absolute bottom-8 left-1/2 -translate-x-1/2 flex items-center gap-4">
            <button
              onClick={resetModelPosition}
              className="p-4 bg-white/90 backdrop-blur rounded-full shadow-lg"
            >
              <RotateCcw size={24} className="text-gray-800" />
            </button>
            
            <div className="px-6 py-3 bg-white/90 backdrop-blur rounded-full shadow-lg">
              <p className="text-gray-800 font-medium">
                {placementMode ? '点击平面放置模型' : '双指缩放旋转'}
              </p>
            </div>
            
            <button
              onClick={() => setShowInfo(!showInfo)}
              className="p-4 bg-white/90 backdrop-blur rounded-full shadow-lg"
            >
              <Info size={24} className="text-gray-800" />
            </button>
          </div>

          {/* 模型信息浮动窗 */}
          {showInfo && selectedModel && (
            <div className="absolute bottom-28 left-4 right-4 bg-white/95 backdrop-blur rounded-lg p-4 shadow-lg">
              <h4 className="font-medium text-gray-800">{selectedModel.name}</h4>
              <p className="text-gray-600 text-sm mt-1">
                {selectedModel.description}
              </p>
            </div>
          )}
        </>
      )}

      {/* 错误提示 */}
      {error && (
        <div className="absolute inset-0 flex items-center justify-center bg-black/50">
          <div className="bg-white rounded-lg p-6 max-w-sm mx-4">
            <h3 className="text-red-600 font-medium mb-2">出错了</h3>
            <p className="text-gray-600 text-sm">{error}</p>
            <button
              onClick={() => setError(null)}
              className="mt-4 w-full py-2 bg-gray-100 hover:bg-gray-200 rounded-lg text-gray-800"
            >
              确定
            </button>
          </div>
        </div>
      )}
    </div>
  );
};

// 3D 几何模型预览组件
interface GeometryPreviewProps {
  geometry: 'cube' | 'sphere' | 'cone' | 'cylinder' | 'torus';
  size?: number;
  color?: string;
  className?: string;
}

export const GeometryPreview: React.FC<GeometryPreviewProps> = ({
  geometry,
  size = 200,
  color = '#3b82f6',
  className = '',
}) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    // 设置 canvas 大小
    canvas.width = size;
    canvas.height = size;

    const centerX = size / 2;
    const centerY = size / 2;

    // 清空画布
    ctx.clearRect(0, 0, size, size);

    // 绘制几何图形
    ctx.strokeStyle = color;
    ctx.fillStyle = color + '40'; // 添加透明度
    ctx.lineWidth = 2;

    switch (geometry) {
      case 'cube':
        // 绘制简化的立方体
        drawCube(ctx, centerX, centerY, size * 0.3);
        break;
      case 'sphere':
        // 绘制球体
        drawSphere(ctx, centerX, centerY, size * 0.35);
        break;
      case 'cone':
        // 绘制圆锥
        drawCone(ctx, centerX, centerY, size * 0.3);
        break;
      case 'cylinder':
        // 绘制圆柱
        drawCylinder(ctx, centerX, centerY, size * 0.25);
        break;
      case 'torus':
        // 绘制圆环
        drawTorus(ctx, centerX, centerY, size * 0.3);
        break;
    }
  }, [geometry, size, color]);

  // 绘制立方体
  const drawCube = (
    ctx: CanvasRenderingContext2D, 
    x: number, 
    y: number, 
    size: number
  ) => {
    const offset = size * 0.3;
    
    // 前面
    ctx.beginPath();
    ctx.rect(x - size, y - size, size * 2, size * 2);
    ctx.fill();
    ctx.stroke();
    
    // 顶面
    ctx.beginPath();
    ctx.moveTo(x - size, y - size);
    ctx.lineTo(x - size + offset, y - size - offset);
    ctx.lineTo(x + size + offset, y - size - offset);
    ctx.lineTo(x + size, y - size);
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
    
    // 右面
    ctx.beginPath();
    ctx.moveTo(x + size, y - size);
    ctx.lineTo(x + size + offset, y - size - offset);
    ctx.lineTo(x + size + offset, y + size - offset);
    ctx.lineTo(x + size, y + size);
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
  };

  // 绘制球体
  const drawSphere = (
    ctx: CanvasRenderingContext2D, 
    x: number, 
    y: number, 
    radius: number
  ) => {
    // 主圆
    ctx.beginPath();
    ctx.arc(x, y, radius, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    
    // 经线
    ctx.beginPath();
    ctx.ellipse(x, y, radius * 0.3, radius, 0, 0, Math.PI * 2);
    ctx.stroke();
    
    // 纬线
    ctx.beginPath();
    ctx.ellipse(x, y - radius * 0.4, radius * 0.7, radius * 0.2, 0, 0, Math.PI * 2);
    ctx.stroke();
  };

  // 绘制圆锥
  const drawCone = (
    ctx: CanvasRenderingContext2D, 
    x: number, 
    y: number, 
    size: number
  ) => {
    // 底面椭圆
    ctx.beginPath();
    ctx.ellipse(x, y + size * 0.5, size, size * 0.3, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    
    // 锥面
    ctx.beginPath();
    ctx.moveTo(x - size, y + size * 0.5);
    ctx.lineTo(x, y - size);
    ctx.lineTo(x + size, y + size * 0.5);
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
    
    // 隐藏的后半部分底面
    ctx.beginPath();
    ctx.ellipse(x, y + size * 0.5, size, size * 0.3, 0, Math.PI, 0);
    ctx.stroke();
  };

  // 绘制圆柱
  const drawCylinder = (
    ctx: CanvasRenderingContext2D, 
    x: number, 
    y: number, 
    radius: number
  ) => {
    const height = radius * 3;
    
    // 底面
    ctx.beginPath();
    ctx.ellipse(x, y + height / 2, radius, radius * 0.3, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    
    // 顶面
    ctx.beginPath();
    ctx.ellipse(x, y - height / 2, radius, radius * 0.3, 0, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
    
    // 侧面
    ctx.beginPath();
    ctx.moveTo(x - radius, y - height / 2);
    ctx.lineTo(x - radius, y + height / 2);
    ctx.moveTo(x + radius, y - height / 2);
    ctx.lineTo(x + radius, y + height / 2);
    ctx.stroke();
  };

  // 绘制圆环
  const drawTorus = (
    ctx: CanvasRenderingContext2D, 
    x: number, 
    y: number, 
    size: number
  ) => {
    const tubeRadius = size * 0.3;
    
    // 外圆
    ctx.beginPath();
    ctx.arc(x, y, size + tubeRadius, 0, Math.PI * 2);
    ctx.stroke();
    
    // 内圆
    ctx.beginPath();
    ctx.arc(x, y, size - tubeRadius, 0, Math.PI * 2);
    ctx.stroke();
    
    // 填充环
    ctx.beginPath();
    ctx.arc(x, y, size, 0, Math.PI * 2);
    ctx.lineWidth = tubeRadius * 2;
    ctx.stroke();
    ctx.lineWidth = 2;
  };

  return (
    <canvas
      ref={canvasRef}
      width={size}
      height={size}
      className={className}
      style={{ width: size, height: size }}
    />
  );
};

// 示例 AR 模型数据
export const sampleARModels: ARModel[] = [
  {
    id: 'cube-1',
    name: '立方体',
    type: 'geometry',
    url: '/models/cube.glb',
    thumbnail: '/thumbnails/cube.png',
    description: '三维空间中的基本几何形状，有6个面、12条边和8个顶点',
    scale: 1,
  },
  {
    id: 'sphere-1',
    name: '球体',
    type: 'geometry',
    url: '/models/sphere.glb',
    thumbnail: '/thumbnails/sphere.png',
    description: '空间中到定点距离相等的所有点的集合',
    scale: 1,
  },
  {
    id: 'function-1',
    name: '正弦函数',
    type: 'function',
    url: '/models/sine-wave.glb',
    thumbnail: '/thumbnails/sine.png',
    description: 'y = sin(x) 的三维可视化',
    scale: 0.5,
  },
  {
    id: 'graph-1',
    name: '知识图谱',
    type: 'graph',
    url: '/models/graph.glb',
    thumbnail: '/thumbnails/graph.png',
    description: '数学概念关系网络的三维展示',
    scale: 0.8,
  },
];

export default ARViewer;
