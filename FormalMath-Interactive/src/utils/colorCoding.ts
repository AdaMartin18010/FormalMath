/**
 * FormalMath 颜色编码工具
 * 概念掌握度、优先级、状态的颜色映射
 */

import type { MasteryLevel } from '../types/learning';

// 掌握度颜色配置
export const MASTERY_COLORS: Record<MasteryLevel, { bg: string; text: string; border: string; light: string }> = {
  0: {
    bg: 'bg-red-500',
    text: 'text-red-700',
    border: 'border-red-500',
    light: 'bg-red-100',
  },
  1: {
    bg: 'bg-orange-500',
    text: 'text-orange-700',
    border: 'border-orange-500',
    light: 'bg-orange-100',
  },
  2: {
    bg: 'bg-yellow-500',
    text: 'text-yellow-700',
    border: 'border-yellow-500',
    light: 'bg-yellow-100',
  },
  3: {
    bg: 'bg-green-500',
    text: 'text-green-700',
    border: 'border-green-500',
    light: 'bg-green-100',
  },
  4: {
    bg: 'bg-blue-500',
    text: 'text-blue-700',
    border: 'border-blue-500',
    light: 'bg-blue-100',
  },
};

// 掌握度十六进制颜色（用于 Canvas）
export const MASTERY_HEX_COLORS: Record<MasteryLevel, string> = {
  0: '#ef4444',
  1: '#f97316',
  2: '#eab308',
  3: '#22c55e',
  4: '#3b82f6',
};

// 优先级颜色
export const PRIORITY_COLORS: Record<'high' | 'medium' | 'low', { bg: string; text: string; badge: string }> = {
  high: {
    bg: 'bg-red-50',
    text: 'text-red-700',
    badge: 'bg-red-100 text-red-800',
  },
  medium: {
    bg: 'bg-orange-50',
    text: 'text-orange-700',
    badge: 'bg-orange-100 text-orange-800',
  },
  low: {
    bg: 'bg-yellow-50',
    text: 'text-yellow-700',
    badge: 'bg-yellow-100 text-yellow-800',
  },
};

// 学习节点状态颜色
export const NODE_STATUS_COLORS: Record<string, { bg: string; text: string; border: string }> = {
  locked: {
    bg: 'bg-gray-200',
    text: 'text-gray-500',
    border: 'border-gray-300',
  },
  available: {
    bg: 'bg-blue-50',
    text: 'text-blue-700',
    border: 'border-blue-300',
  },
  in_progress: {
    bg: 'bg-purple-50',
    text: 'text-purple-700',
    border: 'border-purple-300',
  },
  completed: {
    bg: 'bg-green-50',
    text: 'text-green-700',
    border: 'border-green-300',
  },
  skipped: {
    bg: 'bg-gray-100',
    text: 'text-gray-400',
    border: 'border-gray-200',
  },
};

// 徽章稀有度颜色
export const RARITY_COLORS: Record<'common' | 'rare' | 'epic' | 'legendary', { bg: string; text: string; gradient: string }> = {
  common: {
    bg: 'bg-gray-100',
    text: 'text-gray-600',
    gradient: 'from-gray-200 to-gray-300',
  },
  rare: {
    bg: 'bg-blue-100',
    text: 'text-blue-600',
    gradient: 'from-blue-200 to-blue-300',
  },
  epic: {
    bg: 'bg-purple-100',
    text: 'text-purple-600',
    gradient: 'from-purple-200 to-purple-300',
  },
  legendary: {
    bg: 'bg-yellow-100',
    text: 'text-yellow-600',
    gradient: 'from-yellow-200 to-amber-300',
  },
};

// 技能维度颜色（用于雷达图）
export const SKILL_DIMENSION_COLORS: Record<string, string> = {
  knowledge: '#3b82f6',
  problemSolving: '#22c55e',
  proofAbility: '#f59e0b',
  application: '#ec4899',
  innovation: '#8b5cf6',
};

// 趋势颜色
export const TREND_COLORS: Record<'improving' | 'stable' | 'declining', { color: string; icon: string }> = {
  improving: {
    color: 'text-green-600',
    icon: '📈',
  },
  stable: {
    color: 'text-gray-600',
    icon: '➡️',
  },
  declining: {
    color: 'text-red-600',
    icon: '📉',
  },
};

/**
 * 根据掌握度获取颜色配置
 */
export function getMasteryColorConfig(level: MasteryLevel) {
  return MASTERY_COLORS[level];
}

/**
 * 根据掌握度获取十六进制颜色
 */
export function getMasteryHexColor(level: MasteryLevel): string {
  return MASTERY_HEX_COLORS[level];
}

/**
 * 根据掌握度获取标签
 */
export function getMasteryLabel(level: MasteryLevel): string {
  const labels: Record<MasteryLevel, string> = {
    0: '未掌握',
    1: '初学',
    2: '理解',
    3: '熟练',
    4: '精通',
  };
  return labels[level];
}

/**
 * 根据掌握度获取短标签
 */
export function getMasteryShortLabel(level: MasteryLevel): string {
  const labels: Record<MasteryLevel, string> = {
    0: 'L0',
    1: 'L1',
    2: 'L2',
    3: 'L3',
    4: 'L4',
  };
  return labels[level];
}

/**
 * 根据数值获取掌握度等级
 */
export function getMasteryLevelFromValue(value: number): MasteryLevel {
  if (value >= 90) return 4;
  if (value >= 75) return 3;
  if (value >= 50) return 2;
  if (value >= 25) return 1;
  return 0;
}

/**
 * 获取优先级颜色配置
 */
export function getPriorityColorConfig(priority: 'high' | 'medium' | 'low') {
  return PRIORITY_COLORS[priority];
}

/**
 * 获取节点状态颜色配置
 */
export function getNodeStatusColorConfig(status: string) {
  return NODE_STATUS_COLORS[status] || NODE_STATUS_COLORS.locked;
}

/**
 * 获取徽章稀有度颜色配置
 */
export function getRarityColorConfig(rarity: 'common' | 'rare' | 'epic' | 'legendary') {
  return RARITY_COLORS[rarity];
}

/**
 * 获取趋势颜色配置
 */
export function getTrendColorConfig(trend: 'improving' | 'stable' | 'declining') {
  return TREND_COLORS[trend];
}

/**
 * 生成渐变色
 */
export function generateGradient(color1: string, color2: string, steps: number): string[] {
  const gradients: string[] = [];
  for (let i = 0; i < steps; i++) {
    const ratio = i / (steps - 1);
    gradients.push(interpolateColor(color1, color2, ratio));
  }
  return gradients;
}

/**
 * 颜色插值
 */
function interpolateColor(color1: string, color2: string, ratio: number): string {
  const hex1 = color1.replace('#', '');
  const hex2 = color2.replace('#', '');
  
  const r1 = parseInt(hex1.substring(0, 2), 16);
  const g1 = parseInt(hex1.substring(2, 4), 16);
  const b1 = parseInt(hex1.substring(4, 6), 16);
  
  const r2 = parseInt(hex2.substring(0, 2), 16);
  const g2 = parseInt(hex2.substring(2, 4), 16);
  const b2 = parseInt(hex2.substring(4, 6), 16);
  
  const r = Math.round(r1 + (r2 - r1) * ratio);
  const g = Math.round(g1 + (g2 - g1) * ratio);
  const b = Math.round(b1 + (b2 - b1) * ratio);
  
  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}

// 默认导出
export default {
  MASTERY_COLORS,
  MASTERY_HEX_COLORS,
  PRIORITY_COLORS,
  NODE_STATUS_COLORS,
  RARITY_COLORS,
  SKILL_DIMENSION_COLORS,
  TREND_COLORS,
  getMasteryColorConfig,
  getMasteryHexColor,
  getMasteryLabel,
  getMasteryShortLabel,
  getMasteryLevelFromValue,
  getPriorityColorConfig,
  getNodeStatusColorConfig,
  getRarityColorConfig,
  getTrendColorConfig,
  generateGradient,
};
