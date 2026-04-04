/**
 * FormalMath 学习路径可视化数据整合
 * 将学习路径数据转换为可视化格式
 */

import { adaptiveApi } from '../api/adaptive';
import { diagnosisApi } from '../api/diagnosis';
import type {
  LearningPath,
  LearningNode,
  VisualPath,
  VisualPathNode,
  PathConnection,
  PathProgress,
  MasteryLevel,
} from '../types/learning';

// 路径布局配置
const PATH_CONFIG = {
  nodeSpacing: 120,
  levelSpacing: 150,
  startX: 100,
  startY: 100,
  milestoneSpacing: 4, // 每N个节点设置一个里程碑
};

/**
 * 获取可视化学习路径
 * @param userId 用户ID
 * @returns 可视化路径数据
 */
export async function getVisualLearningPath(userId: string): Promise<VisualPath> {
  const [learningPath, recommendations] = await Promise.all([
    adaptiveApi.getLearningPath(userId),
    diagnosisApi.getRecommendations(userId, 10).catch(() => []),
  ]);

  // 构建可视化节点
  const nodes = buildVisualNodes(learningPath.path, recommendations);
  
  // 构建连接
  const connections = buildPathConnections(learningPath.path);
  
  // 计算进度
  const progress = calculatePathProgress(learningPath.path);

  return {
    nodes,
    connections,
    progress,
  };
}

/**
 * 构建可视化节点
 */
function buildVisualNodes(
  nodes: LearningNode[],
  recommendations: Array<{ targetId: string; type: string }>
): VisualPathNode[] {
  const recommendedSet = new Set(
    recommendations.filter(r => r.type === 'concept').map(r => r.targetId)
  );

  // 构建节点层级
  const nodeLevels = calculateNodeLevels(nodes);
  
  return nodes.map((node, index) => {
    const level = nodeLevels.get(node.id) || 0;
    const siblingsAtLevel = nodes.filter(n => nodeLevels.get(n.id) === level);
    const indexInLevel = siblingsAtLevel.findIndex(n => n.id === node.id);
    
    // 计算位置（蛇形布局）
    const x = PATH_CONFIG.startX + level * PATH_CONFIG.levelSpacing;
    const yOffset = (indexInLevel % 2 === 0 ? 1 : -1) * Math.floor(indexInLevel / 2) * 80;
    const y = PATH_CONFIG.startY + yOffset;

    return {
      id: node.id,
      conceptId: node.conceptId,
      position: { x, y },
      status: node.status,
      mastery: estimateMasteryFromStatus(node.status),
      estimatedTime: node.estimatedTime,
      isMilestone: index % PATH_CONFIG.milestoneSpacing === 0 && index > 0,
    };
  });
}

/**
 * 计算节点层级（基于依赖关系）
 */
function calculateNodeLevels(nodes: LearningNode[]): Map<string, number> {
  const levels = new Map<string, number>();
  const nodeMap = new Map(nodes.map(n => [n.id, n]));
  
  // 初始化
  nodes.forEach(node => levels.set(node.id, 0));
  
  // 迭代计算层级
  let changed = true;
  let iterations = 0;
  while (changed && iterations < 50) {
    changed = false;
    iterations++;
    
    nodes.forEach(node => {
      const currentLevel = levels.get(node.id) || 0;
      
      node.dependencies.forEach(depId => {
        const depNode = nodeMap.get(depId);
        if (depNode) {
          const depLevel = levels.get(depId) || 0;
          const newLevel = Math.max(currentLevel, depLevel + 1);
          
          if (newLevel > currentLevel) {
            levels.set(node.id, newLevel);
            changed = true;
          }
        }
      });
    });
  }
  
  return levels;
}

/**
 * 从状态估计掌握度
 */
function estimateMasteryFromStatus(status: string): MasteryLevel {
  switch (status) {
    case 'completed': return 4;
    case 'in_progress': return 2;
    case 'available': return 0;
    case 'locked': return 0;
    case 'skipped': return 1;
    default: return 0;
  }
}

/**
 * 构建路径连接
 */
function buildPathConnections(nodes: LearningNode[]): PathConnection[] {
  const connections: PathConnection[] = [];
  const nodeMap = new Map(nodes.map(n => [n.id, n]));
  
  nodes.forEach(node => {
    // 主要依赖连接
    node.dependencies.forEach(depId => {
      if (nodeMap.has(depId)) {
        connections.push({
          from: depId,
          to: node.id,
          type: 'main',
        });
      }
    });
  });
  
  // 识别替代路径（如果有并行节点）
  for (let i = 0; i < nodes.length - 1; i++) {
    const current = nodes[i];
    const next = nodes[i + 1];
    
    // 如果没有直接依赖关系，创建快捷连接
    if (!current.dependencies.includes(next.id) && !next.dependencies.includes(current.id)) {
      const hasSharedDep = current.dependencies.some(dep => 
        next.dependencies.includes(dep)
      );
      
      if (hasSharedDep) {
        connections.push({
          from: current.id,
          to: next.id,
          type: 'shortcut',
        });
      }
    }
  }
  
  return connections;
}

/**
 * 计算路径进度
 */
function calculatePathProgress(nodes: LearningNode[]): PathProgress {
  const completed = nodes.filter(n => n.status === 'completed').length;
  const total = nodes.length;
  
  const remainingNodes = nodes.filter(n => 
    n.status !== 'completed' && n.status !== 'skipped'
  );
  
  const estimatedRemaining = remainingNodes.reduce(
    (sum, n) => sum + n.estimatedTime, 
    0
  );
  
  const currentNode = nodes.find(n => n.status === 'in_progress');

  return {
    completed,
    total,
    estimatedRemaining,
    currentNode: currentNode?.id,
  };
}

/**
 * 调整路径布局
 * @param visualPath 当前可视化路径
 * @param adjustment 调整选项
 * @returns 调整后的路径
 */
export function adjustPathLayout(
  visualPath: VisualPath,
  adjustment: LayoutAdjustment
): VisualPath {
  const { nodes, connections, progress } = visualPath;
  
  let adjustedNodes = [...nodes];
  
  // 应用缩放
  if (adjustment.scale) {
    adjustedNodes = adjustedNodes.map(node => ({
      ...node,
      position: {
        x: PATH_CONFIG.startX + (node.position.x - PATH_CONFIG.startX) * adjustment.scale!,
        y: PATH_CONFIG.startY + (node.position.y - PATH_CONFIG.startY) * adjustment.scale!,
      },
    }));
  }
  
  // 应用偏移
  if (adjustment.offsetX || adjustment.offsetY) {
    adjustedNodes = adjustedNodes.map(node => ({
      ...node,
      position: {
        x: node.position.x + (adjustment.offsetX || 0),
        y: node.position.y + (adjustment.offsetY || 0),
      },
    }));
  }
  
  // 聚焦特定节点
  if (adjustment.focusNodeId) {
    const focusNode = adjustedNodes.find(n => n.id === adjustment.focusNodeId);
    if (focusNode) {
      // 将焦点节点移到中心
      const centerX = 400;
      const centerY = 300;
      const dx = centerX - focusNode.position.x;
      const dy = centerY - focusNode.position.y;
      
      adjustedNodes = adjustedNodes.map(node => ({
        ...node,
        position: {
          x: node.position.x + dx,
          y: node.position.y + dy,
        },
      }));
    }
  }

  return {
    nodes: adjustedNodes,
    connections,
    progress,
  };
}

/**
 * 获取路径时间预估
 * @param userId 用户ID
 * @returns 时间统计
 */
export async function getPathTimeEstimate(userId: string): Promise<PathTimeEstimate> {
  const [learningPath, stats] = await Promise.all([
    adaptiveApi.getLearningPath(userId),
    adaptiveApi.getLearningStats(userId),
  ]);

  const remainingNodes = learningPath.path.filter(n => 
    n.status !== 'completed' && n.status !== 'skipped'
  );
  
  const totalEstimatedTime = remainingNodes.reduce(
    (sum, n) => sum + n.estimatedTime, 
    0
  );
  
  // 根据用户学习速度调整
  const velocity = stats.velocity.nodesPerDay;
  const estimatedDays = velocity > 0 ? remainingNodes.length / velocity : 0;

  return {
    totalMinutes: totalEstimatedTime,
    totalHours: Math.round(totalEstimatedTime / 60 * 10) / 10,
    estimatedDays: Math.ceil(estimatedDays),
    estimatedCompletionDate: stats.velocity.estimatedCompletionDate,
    breakdown: {
      learning: remainingNodes.filter(n => n.type === 'learn').reduce((s, n) => s + n.estimatedTime, 0),
      practice: remainingNodes.filter(n => n.type === 'practice').reduce((s, n) => s + n.estimatedTime, 0),
      assessment: remainingNodes.filter(n => n.type === 'assess').reduce((s, n) => s + n.estimatedTime, 0),
      review: remainingNodes.filter(n => n.type === 'review').reduce((s, n) => s + n.estimatedTime, 0),
    },
  };
}

/**
 * 获取路径对比（当前 vs 推荐）
 * @param userId 用户ID
 * @returns 路径对比数据
 */
export async function getPathComparison(userId: string): Promise<PathComparison> {
  const currentPath = await adaptiveApi.getLearningPath(userId);
  const optimizedPath = await adaptiveApi.generatePath(userId, {
    prioritizeWeakPoints: true,
    difficultyPreference: 'balanced',
  });

  const currentCompleted = currentPath.path.filter(n => n.status === 'completed').length;
  const optimizedTotal = optimizedPath.path.length;

  return {
    currentPath: {
      totalNodes: currentPath.path.length,
      completedNodes: currentCompleted,
      remainingNodes: currentPath.path.length - currentCompleted,
      estimatedTime: currentPath.estimatedTime,
    },
    optimizedPath: {
      totalNodes: optimizedTotal,
      estimatedTime: optimizedPath.estimatedTime,
      difficulty: optimizedPath.overallDifficulty,
    },
    potentialSavings: currentPath.estimatedTime - optimizedPath.estimatedTime,
    recommendations: generatePathRecommendations(currentPath, optimizedPath),
  };
}

/**
 * 生成路径建议
 */
function generatePathRecommendations(
  current: LearningPath,
  optimized: LearningPath
): string[] {
  const recommendations: string[] = [];
  
  if (optimized.estimatedTime < current.estimatedTime * 0.9) {
    recommendations.push('优化后的路径可节省约 ' + 
      Math.round((1 - optimized.estimatedTime / current.estimatedTime) * 100) + 
      '% 的学习时间');
  }
  
  const weakPointFocus = optimized.path.filter(n => 
    current.path.find(cn => cn.conceptId === n.conceptId)?.status !== 'completed'
  );
  
  if (weakPointFocus.length > 0) {
    recommendations.push(`建议优先关注 ${weakPointFocus.length} 个薄弱概念`);
  }
  
  return recommendations;
}

// 类型定义
export interface LayoutAdjustment {
  scale?: number;
  offsetX?: number;
  offsetY?: number;
  focusNodeId?: string;
}

export interface PathTimeEstimate {
  totalMinutes: number;
  totalHours: number;
  estimatedDays: number;
  estimatedCompletionDate: string;
  breakdown: {
    learning: number;
    practice: number;
    assessment: number;
    review: number;
  };
}

export interface PathComparison {
  currentPath: {
    totalNodes: number;
    completedNodes: number;
    remainingNodes: number;
    estimatedTime: number;
  };
  optimizedPath: {
    totalNodes: number;
    estimatedTime: number;
    difficulty: number;
  };
  potentialSavings: number;
  recommendations: string[];
}

// 导出服务
export const learningPathService = {
  getVisualLearningPath,
  adjustPathLayout,
  getPathTimeEstimate,
  getPathComparison,
  PATH_CONFIG,
};

export default learningPathService;
