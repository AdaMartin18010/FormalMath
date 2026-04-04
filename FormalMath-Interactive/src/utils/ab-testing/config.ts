/**
 * A/B测试配置
 * 实验管理和分析
 */

import { v4 as uuidv4 } from 'uuid';

// 实验类型定义
export type ExperimentId = 
  | 'homepage_layout'
  | 'button_color'
  | 'onboarding_flow'
  | 'search_algorithm'
  | 'navigation_style';

export type VariantId = string;

export interface Variant {
  id: VariantId;
  name: string;
  weight: number;
  config?: Record<string, unknown>;
}

export interface Experiment {
  id: ExperimentId;
  name: string;
  description: string;
  variants: Variant[];
  startDate: Date;
  endDate?: Date;
  trafficAllocation: number;
  targetAudience?: string[];
  goals: string[];
}

// 实验配置
export const experiments: Record<ExperimentId, Experiment> = {
  homepage_layout: {
    id: 'homepage_layout',
    name: '首页布局优化',
    description: '测试不同首页布局对用户参与度的影响',
    variants: [
      { id: 'control', name: '原始布局', weight: 0.5 },
      { id: 'variant_a', name: '卡片式布局', weight: 0.25 },
      { id: 'variant_b', name: '列表式布局', weight: 0.25 },
    ],
    startDate: new Date('2026-01-01'),
    trafficAllocation: 1.0,
    goals: ['engagement', 'conversion', 'time_on_page'],
  },
  button_color: {
    id: 'button_color',
    name: '按钮颜色测试',
    description: '测试不同按钮颜色对点击率的影响',
    variants: [
      { id: 'control', name: '蓝色按钮', weight: 0.5, config: { color: 'blue' } },
      { id: 'variant_green', name: '绿色按钮', weight: 0.25, config: { color: 'green' } },
      { id: 'variant_red', name: '红色按钮', weight: 0.25, config: { color: 'red' } },
    ],
    startDate: new Date('2026-01-15'),
    trafficAllocation: 0.5,
    goals: ['click_rate', 'conversion'],
  },
  onboarding_flow: {
    id: 'onboarding_flow',
    name: '新用户引导流程',
    description: '优化新用户首次使用体验',
    variants: [
      { id: 'control', name: '原有流程', weight: 0.5 },
      { id: 'variant_simplified', name: '简化流程', weight: 0.3 },
      { id: 'variant_interactive', name: '交互式引导', weight: 0.2 },
    ],
    startDate: new Date('2026-02-01'),
    trafficAllocation: 0.3,
    targetAudience: ['new_users'],
    goals: ['completion_rate', 'retention'],
  },
  search_algorithm: {
    id: 'search_algorithm',
    name: '搜索算法优化',
    description: '测试新搜索算法的效果',
    variants: [
      { id: 'control', name: '现有算法', weight: 0.5 },
      { id: 'variant_ml', name: '机器学习算法', weight: 0.5 },
    ],
    startDate: new Date('2026-02-15'),
    trafficAllocation: 0.2,
    goals: ['search_success_rate', 'time_to_result'],
  },
  navigation_style: {
    id: 'navigation_style',
    name: '导航样式测试',
    description: '测试不同导航样式',
    variants: [
      { id: 'control', name: '侧边栏', weight: 0.5 },
      { id: 'variant_top', name: '顶部导航', weight: 0.25 },
      { id: 'variant_hamburger', name: '汉堡菜单', weight: 0.25 },
    ],
    startDate: new Date('2026-03-01'),
    trafficAllocation: 0.4,
    goals: ['navigation_efficiency', 'user_satisfaction'],
  },
};

// 用户分配存储键
const STORAGE_KEY = 'ab_test_assignments';
const USER_ID_KEY = 'ab_test_user_id';

/**
 * 获取或创建用户ID
 */
export function getUserId(): string {
  let userId = localStorage.getItem(USER_ID_KEY);
  if (!userId) {
    userId = uuidv4();
    localStorage.setItem(USER_ID_KEY, userId);
  }
  return userId;
}

/**
 * 根据用户ID和实验ID生成变体分配
 */
export function assignVariant(experimentId: ExperimentId): VariantId {
  const experiment = experiments[experimentId];
  if (!experiment) {
    throw new Error(`Experiment ${experimentId} not found`);
  }

  // 检查是否在实验期间
  const now = new Date();
  if (now < experiment.startDate || (experiment.endDate && now > experiment.endDate)) {
    return 'control';
  }

  // 检查是否已分配
  const assignments = getAssignments();
  if (assignments[experimentId]) {
    return assignments[experimentId];
  }

  // 根据权重随机分配
  const userId = getUserId();
  const hash = hashString(`${userId}:${experimentId}`);
  const random = (hash % 1000) / 1000;

  let cumulativeWeight = 0;
  for (const variant of experiment.variants) {
    cumulativeWeight += variant.weight;
    if (random <= cumulativeWeight) {
      // 保存分配
      assignments[experimentId] = variant.id;
      saveAssignments(assignments);
      return variant.id;
    }
  }

  // 默认返回第一个变体
  return experiment.variants[0].id;
}

/**
 * 获取变体配置
 */
export function getVariantConfig(experimentId: ExperimentId): Record<string, unknown> | undefined {
  const experiment = experiments[experimentId];
  if (!experiment) return undefined;

  const variantId = assignVariant(experimentId);
  const variant = experiment.variants.find(v => v.id === variantId);
  return variant?.config;
}

/**
 * 记录实验事件
 */
export function trackExperimentEvent(
  experimentId: ExperimentId,
  event: string,
  metadata?: Record<string, unknown>
): void {
  const variantId = assignVariant(experimentId);
  const eventData = {
    experimentId,
    variantId,
    event,
    metadata,
    timestamp: new Date().toISOString(),
    userId: getUserId(),
  };

  // 发送到分析服务
  console.log('[A/B Test Event]', eventData);
  
  // 这里可以发送到实际的分析服务
  // analytics.track('experiment_event', eventData);
}

/**
 * 获取用户所有实验分配
 */
export function getUserAssignments(): Record<ExperimentId, VariantId> {
  const assignments: Record<ExperimentId, VariantId> = {} as Record<ExperimentId, VariantId>;
  
  (Object.keys(experiments) as ExperimentId[]).forEach(experimentId => {
    assignments[experimentId] = assignVariant(experimentId);
  });

  return assignments;
}

// 辅助函数：获取存储的分配
function getAssignments(): Record<string, VariantId> {
  try {
    const stored = localStorage.getItem(STORAGE_KEY);
    return stored ? JSON.parse(stored) : {};
  } catch {
    return {};
  }
}

// 辅助函数：保存分配
function saveAssignments(assignments: Record<string, VariantId>): void {
  localStorage.setItem(STORAGE_KEY, JSON.stringify(assignments));
}

// 辅助函数：哈希字符串
function hashString(str: string): number {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return Math.abs(hash);
}

export default experiments;
