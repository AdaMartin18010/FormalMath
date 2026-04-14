/**
 * FormalMath 学习路径动画组件
 * 动态展示学习路径的探索和推荐过程
 */

import React, { useEffect, useRef, useState } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import { 
  Play, Pause, RotateCcw, FastForward, 
  Target, Zap, Award, Clock, MapPin, CheckCircle, Lock
} from 'lucide-react';
import { cn } from '@utils/classNames';

// 路径节点类型
export interface PathNode {
  id: string;
  conceptId: string;
  label: string;
  description?: string;
  x: number;
  y: number;
  status: 'locked' | 'available' | 'in_progress' | 'completed' | 'recommended';
  mastery: number; // 0-100
  difficulty: number; // 1-10
  estimatedTime: number; // minutes
  prerequisites: string[];
  rewards?: string[];
  isMilestone?: boolean;
  isShortcut?: boolean;
}

// 路径连接
export interface PathConnection {
  from: string;
  to: string;
  type: 'required' | 'recommended' | 'shortcut';
  strength?: number;
}

// 动画事件
export interface PathEvent {
  timestamp: number;
  type: 'start' | 'complete' | 'unlock' | 'recommend' | 'milestone';
  nodeId: string;
  message: string;
}

// 组件Props
export interface PathAnimationProps {
  nodes: PathNode[];
  connections: PathConnection[];
  width?: number;
  height?: number;
  className?: string;
  autoPlay?: boolean;
  playbackSpeed?: number;
  showParticlesProp?: boolean;
  showHeatmap?: boolean;
  onNodeClick?: (node: PathNode) => void;
  onAnimationComplete?: () => void;
}

// 节点状态配置
const STATUS_CONFIG: Record<PathNode['status'], { 
  color: string; 
  bgColor: string; 
  borderColor: string;
  icon: React.ReactNode;
  label: string;
}> = {
  locked: {
    color: '#9ca3af',
    bgColor: '#f3f4f6',
    borderColor: '#d1d5db',
    icon: <Lock className="w-4 h-4" />,
    label: '未解锁',
  },
  available: {
    color: '#3b82f6',
    bgColor: '#eff6ff',
    borderColor: '#60a5fa',
    icon: <Target className="w-4 h-4" />,
    label: '可学习',
  },
  in_progress: {
    color: '#8b5cf6',
    bgColor: '#f5f3ff',
    borderColor: '#a78bfa',
    icon: <Zap className="w-4 h-4" />,
    label: '学习中',
  },
  completed: {
    color: '#10b981',
    bgColor: '#ecfdf5',
    borderColor: '#34d399',
    icon: <CheckCircle className="w-4 h-4" />,
    label: '已完成',
  },
  recommended: {
    color: '#f59e0b',
    bgColor: '#fffbeb',
    borderColor: '#fbbf24',
    icon: <Award className="w-4 h-4" />,
    label: '推荐',
  },
};

// 连接类型配置
const CONNECTION_CONFIG: Record<PathConnection['type'], { 
  color: string; 
  strokeDasharray: string;
  width: number;
}> = {
  required: { color: '#3b82f6', strokeDasharray: '0', width: 3 },
  recommended: { color: '#8b5cf6', strokeDasharray: '5,5', width: 2 },
  shortcut: { color: '#10b981', strokeDasharray: '10,5', width: 2 },
};

export const PathAnimation: React.FC<PathAnimationProps> = ({
  nodes,
  connections,
  width = 900,
  height = 600,
  className,
  autoPlay = false,
  playbackSpeed = 1,
  showParticlesProp = true,
  showHeatmap = false,
  onNodeClick,
  onAnimationComplete,
}) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const [animatedNodes, setAnimatedNodes] = useState<PathNode[]>(nodes);
  const [isPlaying, setIsPlaying] = useState(autoPlay);
  const [currentSpeed, setCurrentSpeed] = useState(playbackSpeed);
  const [progress, setProgress] = useState(0);
  const [activeNode, setActiveNode] = useState<string | null>(null);
  const [particles, setParticles] = useState<Array<{ id: string; x: number; y: number; targetX: number; targetY: number }>>([]);
  const [showTrails, setShowTrails] = useState(true);
  const [showParticles, setShowParticles] = useState(showParticlesProp ?? false);
  const animationRef = useRef<number | null>(null);
  const startTimeRef = useRef<number | null>(null);

  // 初始化动画
  useEffect(() => {
    setAnimatedNodes(nodes.map(n => ({ ...n, status: 'locked' })));
  }, [nodes]);

  // 动画循环
  useEffect(() => {
    if (!isPlaying) {
      if (animationRef.current) cancelAnimationFrame(animationRef.current);
      return;
    }

    const animate = (timestamp: number) => {
      if (!startTimeRef.current) startTimeRef.current = timestamp;
      const elapsed = (timestamp - startTimeRef.current) * currentSpeed;
      
      // 模拟学习进度
      const totalDuration = nodes.length * 2000; // 每个节点2秒
      const currentProgress = Math.min(elapsed / totalDuration, 1);
      setProgress(currentProgress);

      // 更新节点状态
      const nodeIndex = Math.floor(currentProgress * nodes.length);
      setAnimatedNodes(prev => prev.map((node, idx) => {
        if (idx < nodeIndex) return { ...node, status: 'completed', mastery: 100 };
        if (idx === nodeIndex) return { ...node, status: 'in_progress', mastery: (currentProgress * nodes.length - nodeIndex) * 100 };
        if (idx === nodeIndex + 1) return { ...node, status: 'available' };
        return node;
      }));

      // 设置活跃节点
      if (nodes[nodeIndex]) {
        setActiveNode(nodes[nodeIndex].id);
      }

      // 生成粒子效果
      if (showParticles && Math.random() < 0.1 * currentSpeed) {
        generateParticle();
      }

      if (currentProgress < 1) {
        animationRef.current = requestAnimationFrame(animate);
      } else {
        setIsPlaying(false);
        onAnimationComplete?.();
      }
    };

    animationRef.current = requestAnimationFrame(animate);

    return () => {
      if (animationRef.current) cancelAnimationFrame(animationRef.current);
    };
  }, [isPlaying, currentSpeed, nodes, showParticles, onAnimationComplete]);

  // 生成粒子
  const generateParticle = () => {
    const completedNodes = animatedNodes.filter(n => n.status === 'completed');
    if (completedNodes.length < 2) return;

    const fromNode = completedNodes[completedNodes.length - 2];
    const toNode = completedNodes[completedNodes.length - 1];

    const newParticle = {
      id: Math.random().toString(36).substr(2, 9),
      x: fromNode.x,
      y: fromNode.y,
      targetX: toNode.x,
      targetY: toNode.y,
    };

    setParticles(prev => [...prev.slice(-20), newParticle]);
  };

  // 绘制Canvas
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    ctx.clearRect(0, 0, width, height);

    // 绘制热力图背景
    if (showHeatmap) {
      drawHeatmap(ctx);
    }

    // 绘制轨迹
    if (showTrails) {
      drawTrails(ctx);
    }

    // 绘制连接
    connections.forEach(conn => {
      const fromNode = animatedNodes.find(n => n.id === conn.from);
      const toNode = animatedNodes.find(n => n.id === conn.to);
      if (fromNode && toNode) {
        drawConnection(ctx, fromNode, toNode, conn);
      }
    });

    // 绘制粒子
    if (showParticles) {
      particles.forEach(particle => {
        drawParticle(ctx, particle);
      });
    }
  }, [animatedNodes, connections, particles, showHeatmap, showTrails, width, height]);

  // 绘制热力图
  const drawHeatmap = (ctx: CanvasRenderingContext2D) => {
    const gradient = ctx.createRadialGradient(
      width / 2, height / 2, 0,
      width / 2, height / 2, Math.max(width, height) / 2
    );
    gradient.addColorStop(0, 'rgba(59, 130, 246, 0.1)');
    gradient.addColorStop(0.5, 'rgba(139, 92, 246, 0.05)');
    gradient.addColorStop(1, 'rgba(16, 185, 129, 0.02)');
    
    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, width, height);
  };

  // 绘制轨迹
  const drawTrails = (ctx: CanvasRenderingContext2D) => {
    const completedNodes = animatedNodes.filter(n => n.status === 'completed');
    if (completedNodes.length < 2) return;

    ctx.beginPath();
    ctx.moveTo(completedNodes[0].x, completedNodes[0].y);
    
    for (let i = 1; i < completedNodes.length; i++) {
      const prev = completedNodes[i - 1];
      const curr = completedNodes[i];
      
      // 使用贝塞尔曲线创建平滑路径
      const cpX = (prev.x + curr.x) / 2;
      ctx.quadraticCurveTo(cpX, prev.y, curr.x, curr.y);
    }

    ctx.strokeStyle = 'rgba(59, 130, 246, 0.3)';
    ctx.lineWidth = 8;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    ctx.stroke();
  };

  // 绘制连接
  const drawConnection = (
    ctx: CanvasRenderingContext2D,
    from: PathNode,
    to: PathNode,
    conn: PathConnection
  ) => {
    const config = CONNECTION_CONFIG[conn.type];
    
    ctx.beginPath();
    ctx.moveTo(from.x, from.y);
    
    // 曲线连接
    const midX = (from.x + to.x) / 2;
    const midY = (from.y + to.y) / 2 - 30;
    ctx.quadraticCurveTo(midX, midY, to.x, to.y);

    ctx.strokeStyle = config.color;
    ctx.lineWidth = config.width;
    ctx.setLineDash(config.strokeDasharray.split(',').map(Number));
    ctx.stroke();
    ctx.setLineDash([]);

    // 绘制箭头
    const angle = Math.atan2(to.y - midY, to.x - midX);
    const arrowLength = 10;
    const arrowX = to.x - 25 * Math.cos(angle);
    const arrowY = to.y - 25 * Math.sin(angle);

    ctx.beginPath();
    ctx.moveTo(arrowX, arrowY);
    ctx.lineTo(
      arrowX - arrowLength * Math.cos(angle - Math.PI / 6),
      arrowY - arrowLength * Math.sin(angle - Math.PI / 6)
    );
    ctx.moveTo(arrowX, arrowY);
    ctx.lineTo(
      arrowX - arrowLength * Math.cos(angle + Math.PI / 6),
      arrowY - arrowLength * Math.sin(angle + Math.PI / 6)
    );
    ctx.strokeStyle = config.color;
    ctx.lineWidth = 2;
    ctx.stroke();
  };

  // 绘制粒子
  const drawParticle = (
    ctx: CanvasRenderingContext2D,
    particle: { x: number; y: number; targetX: number; targetY: number }
  ) => {
    const progress = 0.5;
    const x = particle.x + (particle.targetX - particle.x) * progress;
    const y = particle.y + (particle.targetY - particle.y) * progress;

    ctx.beginPath();
    ctx.arc(x, y, 4, 0, Math.PI * 2);
    ctx.fillStyle = '#fbbf24';
    ctx.fill();

    // 光晕效果
    ctx.beginPath();
    ctx.arc(x, y, 8, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(251, 191, 36, 0.3)';
    ctx.fill();
  };

  // 控制函数
  const handlePlay = () => setIsPlaying(!isPlaying);
  const handleReset = () => {
    setIsPlaying(false);
    setProgress(0);
    setAnimatedNodes(nodes.map(n => ({ ...n, status: 'locked' })));
    setParticles([]);
    startTimeRef.current = null;
  };

  // 统计
  const stats = React.useMemo(() => {
    const completed = animatedNodes.filter(n => n.status === 'completed').length;
    const inProgress = animatedNodes.filter(n => n.status === 'in_progress').length;
    const available = animatedNodes.filter(n => n.status === 'available').length;
    const totalTime = animatedNodes
      .filter(n => n.status === 'completed' || n.status === 'in_progress')
      .reduce((sum, n) => sum + n.estimatedTime, 0);
    
    return { completed, inProgress, available, totalTime };
  }, [animatedNodes]);

  return (
    <div ref={containerRef} className={cn('bg-white rounded-lg border border-gray-200', className)}>
      {/* 工具栏 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-gray-200">
        <div className="flex items-center gap-3">
          <div className="p-2 bg-purple-100 rounded-lg">
            <MapPin className="w-5 h-5 text-purple-600" />
          </div>
          <div>
            <h3 className="font-semibold text-gray-800">学习路径动画</h3>
            <p className="text-sm text-gray-500">动态探索知识图谱</p>
          </div>
        </div>

        {/* 播放控制 */}
        <div className="flex items-center gap-2">
          <button
            onClick={handleReset}
            className="p-2 hover:bg-gray-100 rounded-lg transition-colors"
            title="重置"
          >
            <RotateCcw className="w-4 h-4 text-gray-600" />
          </button>
          <button
            onClick={handlePlay}
            className="p-2 bg-purple-500 hover:bg-purple-600 rounded-lg transition-colors"
            title={isPlaying ? '暂停' : '播放'}
          >
            {isPlaying ? (
              <Pause className="w-4 h-4 text-white" />
            ) : (
              <Play className="w-4 h-4 text-white" />
            )}
          </button>
          <button
            onClick={() => setCurrentSpeed(s => s === 1 ? 2 : s === 2 ? 0.5 : 1)}
            className="flex items-center gap-1 px-3 py-2 bg-gray-100 hover:bg-gray-200 rounded-lg transition-colors"
          >
            <FastForward className="w-4 h-4 text-gray-600" />
            <span className="text-sm text-gray-600">{currentSpeed}x</span>
          </button>
        </div>

        {/* 选项 */}
        <div className="flex items-center gap-2">
          <button
            onClick={() => setShowTrails(!showTrails)}
            className={cn(
              'px-3 py-1.5 text-sm rounded-lg transition-colors',
              showTrails ? 'bg-blue-100 text-blue-700' : 'bg-gray-100 text-gray-600'
            )}
          >
            轨迹
          </button>
          <button
            onClick={() => setShowParticles(!showParticles)}
            className={cn(
              'px-3 py-1.5 text-sm rounded-lg transition-colors',
              showParticles ? 'bg-amber-100 text-amber-700' : 'bg-gray-100 text-gray-600'
            )}
          >
            粒子
          </button>
        </div>
      </div>

      {/* 进度条 */}
      <div className="px-4 py-2 bg-gray-50 border-b border-gray-200">
        <div className="flex items-center gap-4">
          <span className="text-sm text-gray-500">进度</span>
          <div className="flex-1 h-2 bg-gray-200 rounded-full overflow-hidden">
            <motion.div
              className="h-full bg-gradient-to-r from-blue-500 to-purple-500"
              initial={{ width: 0 }}
              animate={{ width: `${progress * 100}%` }}
              transition={{ duration: 0.3 }}
            />
          </div>
          <span className="text-sm font-medium text-gray-700">{Math.round(progress * 100)}%</span>
        </div>
      </div>

      {/* 主可视化区域 */}
      <div className="relative" style={{ width, height }}>
        <canvas
          ref={canvasRef}
          width={width}
          height={height}
          className="absolute inset-0"
        />

        {/* 节点渲染 */}
        {animatedNodes.map((node, index) => {
          const config = STATUS_CONFIG[node.status];
          const isActive = activeNode === node.id;
          
          return (
            <motion.div
              key={node.id}
              className="absolute"
              style={{ left: node.x - 30, top: node.y - 30 }}
              initial={{ scale: 0, opacity: 0 }}
              animate={{ 
                scale: isActive ? 1.1 : 1, 
                opacity: 1,
              }}
              transition={{ 
                type: 'spring',
                stiffness: 300,
                damping: 20,
                delay: index * 0.05
              }}
            >
              <button
                onClick={() => onNodeClick?.(node)}
                className={cn(
                  'relative w-[60px] h-[60px] rounded-full flex flex-col items-center justify-center',
                  'border-2 transition-all duration-300 hover:scale-110',
                  isActive && 'ring-4 ring-purple-200'
                )}
                style={{
                  backgroundColor: config.bgColor,
                  borderColor: config.borderColor,
                }}
              >
                {/* 状态图标 */}
                <span style={{ color: config.color }}>{config.icon}</span>
                
                {/* 掌握度环 */}
                {node.mastery > 0 && (
                  <svg className="absolute inset-0 w-full h-full -rotate-90">
                    <circle
                      cx="30"
                      cy="30"
                      r="27"
                      fill="none"
                      stroke="#e5e7eb"
                      strokeWidth="3"
                    />
                    <circle
                      cx="30"
                      cy="30"
                      r="27"
                      fill="none"
                      stroke={config.color}
                      strokeWidth="3"
                      strokeDasharray={`${node.mastery * 1.7} 170`}
                      className="transition-all duration-500"
                    />
                  </svg>
                )}

                {/* 里程碑标记 */}
                {node.isMilestone && (
                  <div className="absolute -top-1 -right-1 w-5 h-5 bg-amber-400 rounded-full flex items-center justify-center">
                    <Award className="w-3 h-3 text-white" />
                  </div>
                )}

                {/* 捷径标记 */}
                {node.isShortcut && (
                  <div className="absolute -bottom-1 -right-1 w-5 h-5 bg-green-400 rounded-full flex items-center justify-center">
                    <Zap className="w-3 h-3 text-white" />
                  </div>
                )}
              </button>

              {/* 节点标签 */}
              <div className="absolute top-full mt-2 left-1/2 -translate-x-1/2 text-center w-32">
                <p className="text-xs font-medium text-gray-700 truncate">{node.label}</p>
                <p className="text-[10px] text-gray-400">{config.label}</p>
              </div>
            </motion.div>
          );
        })}

        {/* 活跃节点详情 */}
        <AnimatePresence>
          {activeNode && (
            <motion.div
              initial={{ opacity: 0, x: 20 }}
              animate={{ opacity: 1, x: 0 }}
              exit={{ opacity: 0, x: 20 }}
              className="absolute top-4 right-4 bg-white rounded-lg shadow-lg border border-gray-200 p-4 w-64 z-10"
            >
              {(() => {
                const node = animatedNodes.find(n => n.id === activeNode);
                if (!node) return null;
                
                return (
                  <>
                    <div className="flex items-center gap-2 mb-3">
                      <div 
                        className="w-3 h-3 rounded-full"
                        style={{ backgroundColor: STATUS_CONFIG[node.status].color }}
                      />
                      <h4 className="font-semibold text-gray-800">{node.label}</h4>
                    </div>
                    <p className="text-sm text-gray-600 mb-3">{node.description}</p>
                    <div className="space-y-2 text-sm">
                      <div className="flex justify-between">
                        <span className="text-gray-500">掌握度:</span>
                        <span className="font-medium">{Math.round(node.mastery)}%</span>
                      </div>
                      <div className="flex justify-between">
                        <span className="text-gray-500">难度:</span>
                        <span className="font-medium">{node.difficulty}/10</span>
                      </div>
                      <div className="flex justify-between">
                        <span className="text-gray-500">预计时间:</span>
                        <span className="font-medium">{node.estimatedTime}分钟</span>
                      </div>
                    </div>
                  </>
                );
              })()}
            </motion.div>
          )}
        </AnimatePresence>
      </div>

      {/* 底部统计 */}
      <div className="px-4 py-3 border-t border-gray-200 bg-gray-50">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-6">
            <div className="flex items-center gap-2">
              <CheckCircle className="w-4 h-4 text-green-500" />
              <span className="text-sm text-gray-600">已完成: {stats.completed}</span>
            </div>
            <div className="flex items-center gap-2">
              <Zap className="w-4 h-4 text-purple-500" />
              <span className="text-sm text-gray-600">学习中: {stats.inProgress}</span>
            </div>
            <div className="flex items-center gap-2">
              <Target className="w-4 h-4 text-blue-500" />
              <span className="text-sm text-gray-600">可学习: {stats.available}</span>
            </div>
          </div>
          <div className="flex items-center gap-2">
            <Clock className="w-4 h-4 text-gray-400" />
            <span className="text-sm text-gray-600">已学习时间: {stats.totalTime}分钟</span>
          </div>
        </div>
      </div>
    </div>
  );
};

export default PathAnimation;
