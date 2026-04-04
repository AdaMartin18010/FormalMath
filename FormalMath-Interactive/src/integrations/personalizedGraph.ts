/**
 * FormalMath 个性化知识图谱数据整合
 * 将诊断结果与知识图谱结合，生成个性化视图
 */

import { diagnosisApi } from '../api/diagnosis';
import { adaptiveApi } from '../api/adaptive';
import type {
  Concept,
  DiagnosisReport,
  PersonalizedGraphData,
  PersonalizedNode,
  GraphEdge,
  UserProgressSummary,
  MasteryLevel,
  LearningPath,
} from '../types/learning';

// 颜色配置
const MASTERY_COLORS: Record<MasteryLevel, string> = {
  0: '#ef4444', // L0 - 红色 (未掌握)
  1: '#f97316', // L1 - 橙色 (初学)
  2: '#eab308', // L2 - 黄色 (理解)
  3: '#22c55e', // L3 - 绿色 (熟练)
  4: '#3b82f6', // L4 - 蓝色 (精通)
};

const MASTERY_OPACITY: Record<MasteryLevel, number> = {
  0: 1.0,
  1: 1.0,
  2: 1.0,
  3: 0.7,
  4: 0.4,
};

const NODE_SIZES: Record<MasteryLevel, number> = {
  0: 40,
  1: 35,
  2: 30,
  3: 25,
  4: 20,
};

/**
 * 获取个性化知识图谱数据
 * @param userId 用户ID
 * @param conceptGraph 基础概念图谱
 * @returns 个性化图谱数据
 */
export async function getPersonalizedGraph(
  userId: string,
  conceptGraph: ConceptGraph
): Promise<PersonalizedGraphData> {
  // 并行获取诊断结果和学习路径
  const [diagnosis, learningPath] = await Promise.all([
    diagnosisApi.getDiagnosis(userId).catch(() => null),
    adaptiveApi.getLearningPath(userId).catch(() => null),
  ]);

  // 构建个性化节点
  const nodes = buildPersonalizedNodes(
    conceptGraph.nodes,
    conceptGraph.edges,
    diagnosis,
    learningPath
  );

  // 构建边
  const edges = buildGraphEdges(conceptGraph.edges);

  // 计算用户进度摘要
  const userProgress = calculateUserProgress(nodes);

  return {
    nodes,
    edges,
    userProgress,
  };
}

/**
 * 构建个性化节点
 */
function buildPersonalizedNodes(
  concepts: Concept[],
  edges: ConceptEdge[],
  diagnosis: DiagnosisReport | null,
  learningPath: LearningPath | null
): PersonalizedNode[] {
  const knowledgeLevels = diagnosis?.knowledgeLevels || {};
  const weakPoints = new Set(diagnosis?.weakPoints.map(wp => wp.conceptId) || []);
  const recommendedConcepts = new Set(
    diagnosis?.recommendations.map(r => r.targetId) || []
  );
  const pathConcepts = new Set(
    learningPath?.path.map(node => node.conceptId) || []
  );
  const currentFocus = learningPath?.path.find(n => n.status === 'in_progress')?.conceptId;

  // 计算节点位置（使用力导向布局简化版）
  const positions = calculateNodePositions(concepts, edges);

  return concepts.map((concept, index) => {
    const mastery = (knowledgeLevels[concept.id] ?? 0) as MasteryLevel;
    const isWeakPoint = weakPoints.has(concept.id);
    const isRecommended = recommendedConcepts.has(concept.id);
    const isInPath = pathConcepts.has(concept.id);
    const isCurrentFocus = currentFocus === concept.id;
    const position = positions[index];

    // 节点大小根据重要性和掌握度调整
    const size = calculateNodeSize(concept, mastery, isWeakPoint, isRecommended);

    // 节点颜色根据掌握度
    let color = MASTERY_COLORS[mastery];
    
    // 特殊标记覆盖
    if (isCurrentFocus) {
      color = '#8b5cf6'; // 紫色标记当前焦点
    } else if (isWeakPoint) {
      color = '#dc2626'; // 深红色标记薄弱点
    } else if (isRecommended) {
      color = '#06b6d4'; // 青色标记推荐
    }

    return {
      id: concept.id,
      conceptId: concept.id,
      label: concept.name,
      mastery,
      isWeakPoint,
      isRecommended: isRecommended || isInPath,
      isCurrentFocus,
      x: position.x,
      y: position.y,
      size,
      color,
      opacity: isCurrentFocus ? 1.0 : isRecommended ? 0.9 : MASTERY_OPACITY[mastery],
    };
  });
}

/**
 * 计算节点大小
 */
function calculateNodeSize(
  concept: Concept,
  mastery: MasteryLevel,
  isWeakPoint: boolean,
  isRecommended: boolean
): number {
  let size = NODE_SIZES[mastery];
  
  // 薄弱点放大
  if (isWeakPoint) {
    size *= 1.3;
  }
  
  // 推荐概念放大
  if (isRecommended) {
    size *= 1.2;
  }
  
  // 难度影响
  size += concept.difficulty * 2;
  
  return Math.min(size, 60); // 最大60px
}

/**
 * 计算节点位置（简化版力导向布局）
 */
function calculateNodePositions(
  concepts: Concept[],
  edges: ConceptEdge[]
): Array<{ x: number; y: number }> {
  const positions: Array<{ x: number; y: number }> = [];
  const width = 1000;
  const height = 800;
  
  // 构建层级结构
  const levels = calculateHierarchyLevels(concepts, edges);
  
  concepts.forEach((concept, index) => {
    const level = levels.get(concept.id) || 0;
    const siblings = Array.from(levels.entries())
      .filter(([, l]) => l === level)
      .map(([id]) => id);
    const siblingIndex = siblings.indexOf(concept.id);
    
    // 计算位置
    const y = (level / (Math.max(...levels.values()) + 1)) * height * 0.8 + height * 0.1;
    const x = ((siblingIndex + 1) / (siblings.length + 1)) * width;
    
    // 添加随机偏移避免重叠
    const jitterX = (Math.random() - 0.5) * 50;
    const jitterY = (Math.random() - 0.5) * 30;
    
    positions.push({
      x: Math.max(50, Math.min(width - 50, x + jitterX)),
      y: Math.max(50, Math.min(height - 50, y + jitterY)),
    });
  });
  
  return positions;
}

/**
 * 计算层级（拓扑排序）
 */
function calculateHierarchyLevels(
  concepts: Concept[],
  edges: ConceptEdge[]
): Map<string, number> {
  const levels = new Map<string, number>();
  const conceptIds = new Set(concepts.map(c => c.id));
  
  // 初始化
  conceptIds.forEach(id => levels.set(id, 0));
  
  // 迭代更新层级
  let changed = true;
  let iterations = 0;
  while (changed && iterations < 100) {
    changed = false;
    iterations++;
    
    edges.forEach(edge => {
      if (edge.type === 'prerequisite') {
        const currentLevel = levels.get(edge.target) || 0;
        const prereqLevel = levels.get(edge.source) || 0;
        const newLevel = Math.max(currentLevel, prereqLevel + 1);
        
        if (newLevel > currentLevel) {
          levels.set(edge.target, newLevel);
          changed = true;
        }
      }
    });
  }
  
  return levels;
}

/**
 * 构建图谱边
 */
function buildGraphEdges(edges: ConceptEdge[]): GraphEdge[] {
  return edges.map(edge => ({
    source: edge.source,
    target: edge.target,
    type: edge.type,
  }));
}

/**
 * 计算用户进度摘要
 */
function calculateUserProgress(nodes: PersonalizedNode[]): UserProgressSummary {
  const totalConcepts = nodes.length;
  const masteredConcepts = nodes.filter(n => n.mastery >= 3).length;
  const inProgressConcepts = nodes.filter(n => n.mastery === 1 || n.mastery === 2).length;
  const weakPointsCount = nodes.filter(n => n.isWeakPoint).length;
  const overallCompletion = totalConcepts > 0
    ? nodes.reduce((sum, n) => sum + n.mastery, 0) / (totalConcepts * 4)
    : 0;

  return {
    totalConcepts,
    masteredConcepts,
    inProgressConcepts,
    weakPointsCount,
    overallCompletion: Math.round(overallCompletion * 100),
  };
}

/**
 * 获取薄弱概念高亮数据
 * @param userId 用户ID
 * @returns 薄弱概念列表
 */
export async function getWeakPointHighlights(userId: string): Promise<WeakPointHighlight[]> {
  const weakPoints = await diagnosisApi.getWeakPoints(userId);
  
  return weakPoints.map(wp => ({
    conceptId: wp.conceptId,
    conceptName: wp.conceptName,
    currentLevel: wp.currentLevel,
    targetLevel: wp.targetLevel,
    gap: wp.gap,
    priority: wp.priority,
    color: getPriorityColor(wp.priority),
    recommendedAction: getRecommendedAction(wp),
  }));
}

/**
 * 获取优先级颜色
 */
function getPriorityColor(priority: 'high' | 'medium' | 'low'): string {
  switch (priority) {
    case 'high': return '#dc2626';
    case 'medium': return '#f97316';
    case 'low': return '#eab308';
    default: return '#6b7280';
  }
}

/**
 * 获取推荐行动
 */
function getRecommendedAction(weakPoint: {
  conceptId: string;
  currentLevel: MasteryLevel;
  targetLevel: MasteryLevel;
}): string {
  if (weakPoint.currentLevel === 0) {
    return '建议从基础概念开始学习';
  } else if (weakPoint.currentLevel === 1) {
    return '需要加强基础练习';
  } else if (weakPoint.gap >= 2) {
    return '建议系统复习并做进阶练习';
  }
  return '通过综合练习巩固提升';
}

// 类型定义
export interface ConceptGraph {
  nodes: Concept[];
  edges: ConceptEdge[];
}

export interface ConceptEdge {
  source: string;
  target: string;
  type: 'prerequisite' | 'related' | 'extension';
}

export interface WeakPointHighlight {
  conceptId: string;
  conceptName: string;
  currentLevel: MasteryLevel;
  targetLevel: MasteryLevel;
  gap: number;
  priority: 'high' | 'medium' | 'low';
  color: string;
  recommendedAction: string;
}

// 导出服务
export const personalizedGraphService = {
  getPersonalizedGraph,
  getWeakPointHighlights,
  MASTERY_COLORS,
  NODE_SIZES,
};

export default personalizedGraphService;
