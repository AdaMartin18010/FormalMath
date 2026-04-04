/**
 * FormalMath 进度追踪数据整合
 * 实时更新与成就系统
 */

import { adaptiveApi } from '../api/adaptive';
import { evaluationApi } from '../api/evaluation';
import type {
  ProgressUpdateRequest,
  ProgressUpdateResponse,
  Achievement,
  Badge,
  LearningStats,
  MasteryLevel,
} from '../types/learning';

// 成就定义
const ACHIEVEMENT_DEFINITIONS: AchievementDefinition[] = [
  {
    id: 'first_step',
    title: '初出茅庐',
    description: '完成第一个概念学习',
    condition: (stats) => stats.nodesCompleted >= 1,
  },
  {
    id: 'quick_learner',
    title: '快速学习者',
    description: '一天内完成5个概念',
    condition: (stats) => {
      const today = new Date().toISOString().split('T')[0];
      const todayProgress = stats.weeklyProgress.find(p => p.date === today);
      return (todayProgress?.nodesCompleted || 0) >= 5;
    },
  },
  {
    id: 'consistent_student',
    title: '持之以恒',
    description: '连续学习7天',
    condition: (stats) => stats.streakDays >= 7,
  },
  {
    id: 'master_scholar',
    title: '学术大师',
    description: '掌握50个概念',
    condition: (stats) => stats.conceptDistribution.filter(c => c.mastery >= 75).length >= 50,
  },
  {
    id: 'speed_demon',
    title: '速度与激情',
    description: '平均每个概念学习时间少于15分钟',
    condition: (stats) => {
      const avgTime = stats.totalTimeSpent / Math.max(stats.nodesCompleted, 1);
      return avgTime < 15;
    },
  },
  {
    id: 'deep_thinker',
    title: '深度思考者',
    description: '累计学习超过100小时',
    condition: (stats) => stats.totalTimeSpent >= 6000,
  },
];

// 徽章定义
const BADGE_DEFINITIONS: BadgeDefinition[] = [
  {
    id: 'bronze_explorer',
    name: '青铜探索者',
    icon: '🥉',
    rarity: 'common',
    condition: (stats) => stats.nodesCompleted >= 10,
  },
  {
    id: 'silver_scholar',
    name: '白银学者',
    icon: '🥈',
    rarity: 'rare',
    condition: (stats) => stats.nodesCompleted >= 50,
  },
  {
    id: 'gold_master',
    name: '黄金大师',
    icon: '🥇',
    rarity: 'epic',
    condition: (stats) => stats.conceptDistribution.filter(c => c.mastery >= 90).length >= 20,
  },
  {
    id: 'diamond_guru',
    name: '钻石导师',
    icon: '💎',
    rarity: 'legendary',
    condition: (stats) => stats.conceptDistribution.every(c => c.mastery >= 80),
  },
  {
    id: 'fire_streak',
    name: '火焰连胜',
    icon: '🔥',
    rarity: 'rare',
    condition: (stats) => stats.streakDays >= 30,
  },
  {
    id: 'time_lord',
    name: '时间领主',
    icon: '⏰',
    rarity: 'epic',
    condition: (stats) => stats.totalTimeSpent >= 10000,
  },
];

/**
 * 更新学习进度（带成就检查）
 * @param request 进度更新请求
 * @returns 更新结果和成就通知
 */
export async function updateProgressWithAchievements(
  request: ProgressUpdateRequest
): Promise<ProgressUpdateWithAchievements> {
  // 更新进度
  const progressResponse = await adaptiveApi.updateProgress(request);
  
  // 检查新成就
  const newAchievements = await checkNewAchievements(request.userId);
  
  // 检查新徽章
  const newBadges = await checkNewBadges(request.userId);
  
  return {
    ...progressResponse,
    newAchievements,
    newBadges,
    notifications: generateNotifications(newAchievements, newBadges),
  };
}

/**
 * 检查新成就
 */
async function checkNewAchievements(userId: string): Promise<Achievement[]> {
  const [currentAchievements, stats] = await Promise.all([
    evaluationApi.getAchievements(userId, false),
    adaptiveApi.getLearningStats(userId),
  ]);

  const achievedIds = new Set(currentAchievements.map(a => a.id));
  const newAchievements: Achievement[] = [];

  for (const def of ACHIEVEMENT_DEFINITIONS) {
    if (!achievedIds.has(def.id) && def.condition(stats)) {
      newAchievements.push({
        id: def.id,
        title: def.title,
        description: def.description,
        progress: 100,
        completed: true,
        completedAt: new Date().toISOString(),
      });
    }
  }

  return newAchievements;
}

/**
 * 检查新徽章
 */
async function checkNewBadges(userId: string): Promise<Badge[]> {
  const [currentBadges, stats] = await Promise.all([
    evaluationApi.getBadges(userId),
    adaptiveApi.getLearningStats(userId),
  ]);

  const badgeIds = new Set(currentBadges.map(b => b.id));
  const newBadges: Badge[] = [];

  for (const def of BADGE_DEFINITIONS) {
    if (!badgeIds.has(def.id) && def.condition(stats)) {
      newBadges.push({
        id: def.id,
        name: def.name,
        icon: def.icon,
        earnedAt: new Date().toISOString(),
        rarity: def.rarity,
      });
    }
  }

  return newBadges;
}

/**
 * 生成通知
 */
function generateNotifications(
  achievements: Achievement[],
  badges: Badge[]
): Notification[] {
  const notifications: Notification[] = [];

  achievements.forEach(achievement => {
    notifications.push({
      type: 'achievement',
      title: '🎉 成就解锁！',
      message: `恭喜获得成就：${achievement.title}`,
      data: achievement,
      priority: 'medium',
    });
  });

  badges.forEach(badge => {
    notifications.push({
      type: 'badge',
      title: '🏆 获得徽章！',
      message: `解锁徽章：${badge.name}`,
      data: badge,
      priority: badge.rarity === 'legendary' ? 'high' : 'medium',
    });
  });

  return notifications;
}

/**
 * 获取实时进度数据
 * @param userId 用户ID
 * @returns 实时进度数据
 */
export async function getRealtimeProgress(userId: string): Promise<RealtimeProgress> {
  const [stats, achievements, badges] = await Promise.all([
    adaptiveApi.getLearningStats(userId),
    evaluationApi.getAchievements(userId),
    evaluationApi.getBadges(userId),
  ]);

  // 计算掌握度分布
  const masteryDistribution = calculateMasteryDistribution(stats.conceptDistribution);
  
  // 计算本周进度
  const weeklyProgress = calculateWeeklyProgress(stats.weeklyProgress);
  
  // 计算技能增长
  const skillGrowth = await calculateSkillGrowth(userId);

  return {
    summary: {
      totalConcepts: stats.conceptDistribution.length,
      masteredConcepts: stats.conceptDistribution.filter(c => c.mastery >= 75).length,
      inProgressConcepts: stats.nodesInProgress,
      totalTimeSpent: stats.totalTimeSpent,
      streakDays: stats.streakDays,
    },
    masteryDistribution,
    weeklyProgress,
    skillGrowth,
    achievements: {
      total: ACHIEVEMENT_DEFINITIONS.length,
      completed: achievements.filter(a => a.completed).length,
      inProgress: achievements.filter(a => !a.completed),
    },
    badges: {
      total: badges.length,
      byRarity: {
        common: badges.filter(b => b.rarity === 'common').length,
        rare: badges.filter(b => b.rarity === 'rare').length,
        epic: badges.filter(b => b.rarity === 'epic').length,
        legendary: badges.filter(b => b.rarity === 'legendary').length,
      },
      recent: badges.slice(-3),
    },
    velocity: stats.velocity,
  };
}

/**
 * 计算掌握度分布
 */
function calculateMasteryDistribution(
  concepts: LearningStats['conceptDistribution']
): MasteryDistribution {
  const distribution: MasteryDistribution = {
    notStarted: 0,
    beginner: 0,
    intermediate: 0,
    advanced: 0,
    master: 0,
  };

  concepts.forEach(concept => {
    const mastery = concept.mastery;
    if (mastery === 0) distribution.notStarted++;
    else if (mastery < 25) distribution.beginner++;
    else if (mastery < 50) distribution.intermediate++;
    else if (mastery < 75) distribution.advanced++;
    else distribution.master++;
  });

  return distribution;
}

/**
 * 计算本周进度
 */
function calculateWeeklyProgress(
  weeklyData: LearningStats['weeklyProgress']
): WeeklyProgress {
  const now = new Date();
  const weekStart = new Date(now.setDate(now.getDate() - now.getDay()));
  
  const thisWeekData = weeklyData.filter(d => 
    new Date(d.date) >= weekStart
  );

  const nodesCompleted = thisWeekData.reduce((sum, d) => sum + d.nodesCompleted, 0);
  const timeSpent = thisWeekData.reduce((sum, d) => sum + d.timeSpent, 0);
  
  // 与上周对比
  const lastWeekStart = new Date(weekStart);
  lastWeekStart.setDate(lastWeekStart.getDate() - 7);
  
  const lastWeekData = weeklyData.filter(d => {
    const date = new Date(d.date);
    return date >= lastWeekStart && date < weekStart;
  });
  
  const lastWeekNodes = lastWeekData.reduce((sum, d) => sum + d.nodesCompleted, 0);
  const lastWeekTime = lastWeekData.reduce((sum, d) => sum + d.timeSpent, 0);

  return {
    nodesCompleted,
    timeSpent,
    comparison: {
      nodesChange: lastWeekNodes > 0 
        ? Math.round(((nodesCompleted - lastWeekNodes) / lastWeekNodes) * 100)
        : 0,
      timeChange: lastWeekTime > 0
        ? Math.round(((timeSpent - lastWeekTime) / lastWeekTime) * 100)
        : 0,
    },
    dailyBreakdown: thisWeekData.map(d => ({
      day: new Date(d.date).toLocaleDateString('zh-CN', { weekday: 'short' }),
      nodes: d.nodesCompleted,
      time: d.timeSpent,
    })),
  };
}

/**
 * 计算技能增长
 */
async function calculateSkillGrowth(userId: string): Promise<SkillGrowth> {
  const [currentEval, history] = await Promise.all([
    evaluationApi.getEvaluation(userId),
    evaluationApi.getEvaluationHistory(userId, 30),
  ]);

  const previousEval = history[1];
  
  if (!previousEval) {
    return {
      overall: currentEval.overallScore,
      changes: {
        knowledge: 0,
        problemSolving: 0,
        proofAbility: 0,
        application: 0,
        innovation: 0,
      },
      trend: 'stable',
    };
  }

  const changes = {
    knowledge: currentEval.dimensions.knowledge - previousEval.dimensions.knowledge,
    problemSolving: currentEval.dimensions.problemSolving - previousEval.dimensions.problemSolving,
    proofAbility: currentEval.dimensions.proofAbility - previousEval.dimensions.proofAbility,
    application: currentEval.dimensions.application - previousEval.dimensions.application,
    innovation: currentEval.dimensions.innovation - previousEval.dimensions.innovation,
  };

  const avgChange = Object.values(changes).reduce((a, b) => a + b, 0) / 5;

  return {
    overall: currentEval.overallScore,
    changes,
    trend: avgChange > 5 ? 'improving' : avgChange < -5 ? 'declining' : 'stable',
  };
}

/**
 * 获取掌握度颜色编码
 * @param mastery 掌握度百分比 (0-100)
 * @returns 颜色代码
 */
export function getMasteryColor(mastery: number): string {
  if (mastery >= 90) return '#3b82f6'; // 蓝色 - 精通
  if (mastery >= 75) return '#22c55e'; // 绿色 - 熟练
  if (mastery >= 50) return '#eab308'; // 黄色 - 理解
  if (mastery >= 25) return '#f97316'; // 橙色 - 初学
  return '#ef4444'; // 红色 - 未掌握
}

/**
 * 获取掌握度标签
 * @param mastery 掌握度百分比
 * @returns 标签文本
 */
export function getMasteryLabel(mastery: number): string {
  if (mastery >= 90) return '精通';
  if (mastery >= 75) return '熟练';
  if (mastery >= 50) return '理解';
  if (mastery >= 25) return '初学';
  return '未掌握';
}

/**
 * 获取掌握度等级
 * @param mastery 掌握度百分比
 * @returns 等级 (L0-L4)
 */
export function getMasteryLevel(mastery: number): MasteryLevel {
  if (mastery >= 90) return 4;
  if (mastery >= 75) return 3;
  if (mastery >= 50) return 2;
  if (mastery >= 25) return 1;
  return 0;
}

// 类型定义
interface AchievementDefinition {
  id: string;
  title: string;
  description: string;
  condition: (stats: LearningStats) => boolean;
}

interface BadgeDefinition {
  id: string;
  name: string;
  icon: string;
  rarity: 'common' | 'rare' | 'epic' | 'legendary';
  condition: (stats: LearningStats) => boolean;
}

export interface Notification {
  type: 'achievement' | 'badge' | 'level_up' | 'milestone';
  title: string;
  message: string;
  data?: unknown;
  priority: 'low' | 'medium' | 'high';
}

export interface ProgressUpdateWithAchievements extends ProgressUpdateResponse {
  newAchievements: Achievement[];
  newBadges: Badge[];
  notifications: Notification[];
}

interface MasteryDistribution {
  notStarted: number;
  beginner: number;
  intermediate: number;
  advanced: number;
  master: number;
}

interface WeeklyProgress {
  nodesCompleted: number;
  timeSpent: number;
  comparison: {
    nodesChange: number;
    timeChange: number;
  };
  dailyBreakdown: Array<{
    day: string;
    nodes: number;
    time: number;
  }>;
}

interface SkillGrowth {
  overall: number;
  changes: {
    knowledge: number;
    problemSolving: number;
    proofAbility: number;
    application: number;
    innovation: number;
  };
  trend: 'improving' | 'stable' | 'declining';
}

export interface RealtimeProgress {
  summary: {
    totalConcepts: number;
    masteredConcepts: number;
    inProgressConcepts: number;
    totalTimeSpent: number;
    streakDays: number;
  };
  masteryDistribution: MasteryDistribution;
  weeklyProgress: WeeklyProgress;
  skillGrowth: SkillGrowth;
  achievements: {
    total: number;
    completed: number;
    inProgress: Achievement[];
  };
  badges: {
    total: number;
    byRarity: {
      common: number;
      rare: number;
      epic: number;
      legendary: number;
    };
    recent: Badge[];
  };
  velocity: LearningStats['velocity'];
}

// 导出服务
export const progressTracker = {
  updateProgressWithAchievements,
  getRealtimeProgress,
  getMasteryColor,
  getMasteryLabel,
  getMasteryLevel,
  ACHIEVEMENT_DEFINITIONS,
  BADGE_DEFINITIONS,
};

export default progressTracker;
