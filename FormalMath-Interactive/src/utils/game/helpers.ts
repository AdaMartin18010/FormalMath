/**
 * FormalMath 游戏化工具函数
 * 提供游戏相关的辅助功能
 */

import type { 
  GameDifficulty, 
  PuzzleType, 
  BadgeRarity, 
  GameReward,
  LevelSystem,
} from '../../types/gamification';

// ==================== 难度相关 ====================

export const difficultyLabels: Record<GameDifficulty, string> = {
  easy: '简单',
  medium: '中等',
  hard: '困难',
  expert: '专家',
};

export const difficultyColors: Record<GameDifficulty, { bg: string; text: string; border: string }> = {
  easy: { bg: 'bg-green-100', text: 'text-green-700', border: 'border-green-300' },
  medium: { bg: 'bg-yellow-100', text: 'text-yellow-700', border: 'border-yellow-300' },
  hard: { bg: 'bg-orange-100', text: 'text-orange-700', border: 'border-orange-300' },
  expert: { bg: 'bg-red-100', text: 'text-red-700', border: 'border-red-300' },
};

export const difficultyScores: Record<GameDifficulty, number> = {
  easy: 20,
  medium: 40,
  hard: 80,
  expert: 150,
};

// ==================== 谜题类型相关 ====================

export const puzzleTypeLabels: Record<PuzzleType, string> = {
  math_riddle: '数学谜题',
  proof_construct: '证明构造',
  concept_match: '概念连线',
  equation_solve: '方程求解',
  pattern_recognize: '模式识别',
  logic_deduction: '逻辑推导',
};

export const puzzleTypeIcons: Record<PuzzleType, string> = {
  math_riddle: '🧩',
  proof_construct: '🎯',
  concept_match: '🔗',
  equation_solve: '📐',
  pattern_recognize: '🔍',
  logic_deduction: '⚡',
};

// ==================== 徽章稀有度相关 ====================

export const rarityLabels: Record<BadgeRarity, string> = {
  common: '普通',
  uncommon: '优秀',
  rare: '稀有',
  epic: '史诗',
  legendary: '传说',
};

export const rarityColors: Record<BadgeRarity, { bg: string; text: string; border: string }> = {
  common: { bg: 'bg-gray-100', text: 'text-gray-600', border: 'border-gray-300' },
  uncommon: { bg: 'bg-green-100', text: 'text-green-600', border: 'border-green-300' },
  rare: { bg: 'bg-blue-100', text: 'text-blue-600', border: 'border-blue-300' },
  epic: { bg: 'bg-purple-100', text: 'text-purple-600', border: 'border-purple-300' },
  legendary: { bg: 'bg-yellow-100', text: 'text-yellow-600', border: 'border-yellow-300' },
};

export const rarityOrder: BadgeRarity[] = ['common', 'uncommon', 'rare', 'epic', 'legendary'];

// ==================== 等级系统 ====================

export const levelThresholds: number[] = [
  0,      // Level 1
  100,    // Level 2
  250,    // Level 3
  450,    // Level 4
  700,    // Level 5
  1000,   // Level 6
  1350,   // Level 7
  1750,   // Level 8
  2200,   // Level 9
  2700,   // Level 10
];

export const levelTitles: Record<number, { title: string; icon: string }> = {
  1: { title: '数学新手', icon: '🌱' },
  5: { title: '数学学徒', icon: '📚' },
  10: { title: '数学爱好者', icon: '🧮' },
  20: { title: '数学达人', icon: '🔢' },
  35: { title: '数学专家', icon: '🎓' },
  50: { title: '数学大师', icon: '👑' },
  75: { title: '数学传奇', icon: '🏆' },
  100: { title: '数学之神', icon: '⭐' },
};

export function calculateLevel(xp: number): number {
  let level = 1;
  for (let i = 0; i < levelThresholds.length; i++) {
    if (xp >= levelThresholds[i]) {
      level = i + 1;
    } else {
      break;
    }
  }
  return level;
}

export function getLevelTitle(level: number): { title: string; icon: string } {
  const thresholds = Object.keys(levelTitles)
    .map(Number)
    .sort((a, b) => b - a);
  
  for (const threshold of thresholds) {
    if (level >= threshold) {
      return levelTitles[threshold];
    }
  }
  
  return levelTitles[1];
}

export function xpToNextLevel(currentLevel: number): number {
  if (currentLevel < levelThresholds.length) {
    return levelThresholds[currentLevel];
  }
  // 超过预设等级的计算公式
  return Math.floor(1000 * Math.pow(1.1, currentLevel - 10));
}

// ==================== 奖励计算 ====================

export function calculateScore(
  difficulty: GameDifficulty,
  timeSpent: number,
  hintsUsed: number,
  timeLimit: number
): number {
  let score = difficultyScores[difficulty];

  // 时间奖励（越快分数越高）
  const timeBonus = Math.max(0, (timeLimit - timeSpent) / timeLimit) * score * 0.5;
  score += Math.floor(timeBonus);

  // 提示惩罚
  score -= hintsUsed * 5;

  return Math.max(0, score);
}

export function calculateRewards(
  difficulty: GameDifficulty,
  score: number,
  isFirstCompletion: boolean = false
): GameReward[] {
  const rewards: GameReward[] = [];

  // 基础经验
  const baseXP = difficultyScores[difficulty];
  rewards.push({ type: 'xp', amount: baseXP });

  // 基础金币
  const baseCoins = Math.floor(baseXP / 2);
  rewards.push({ type: 'coin', amount: baseCoins });

  // 首次完成奖励
  if (isFirstCompletion) {
    rewards.push({ type: 'coin', amount: 10 });
  }

  return rewards;
}

// ==================== 时间格式化 ====================

export function formatTime(seconds: number): string {
  const mins = Math.floor(seconds / 60);
  const secs = seconds % 60;
  return `${mins}:${secs.toString().padStart(2, '0')}`;
}

export function formatDuration(seconds: number): string {
  const hours = Math.floor(seconds / 3600);
  const mins = Math.floor((seconds % 3600) / 60);
  
  if (hours > 0) {
    return `${hours}小时${mins}分钟`;
  }
  return `${mins}分钟`;
}

// ==================== 随机生成 ====================

export function generateRandomPuzzleId(): string {
  return `puzzle_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

export function generateSessionId(): string {
  return `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

export function generateBattleId(): string {
  return `battle_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// ==================== 进度计算 ====================

export function calculateProgress(current: number, total: number): number {
  if (total === 0) return 0;
  return Math.min(100, Math.round((current / total) * 100));
}

export function calculateStreakBonus(streak: number): number {
  // 连胜奖励：每连胜3次，奖励增加10%
  const bonusMultiplier = Math.floor(streak / 3) * 0.1;
  return Math.min(0.5, bonusMultiplier); // 最高50%奖励
}

// ==================== 成就检查 ====================

export function checkMilestone(value: number, milestones: number[]): number | null {
  for (const milestone of milestones) {
    if (value >= milestone) {
      return milestone;
    }
  }
  return null;
}

// ==================== 本地存储 ====================

const STORAGE_PREFIX = 'formalmath_game_';

export function saveGameProgress(key: string, data: unknown): void {
  try {
    localStorage.setItem(`${STORAGE_PREFIX}${key}`, JSON.stringify(data));
  } catch (error) {
    console.error('Failed to save game progress:', error);
  }
}

export function loadGameProgress<T>(key: string, defaultValue: T): T {
  try {
    const data = localStorage.getItem(`${STORAGE_PREFIX}${key}`);
    return data ? JSON.parse(data) : defaultValue;
  } catch (error) {
    console.error('Failed to load game progress:', error);
    return defaultValue;
  }
}

export function clearGameProgress(): void {
  try {
    Object.keys(localStorage)
      .filter((key) => key.startsWith(STORAGE_PREFIX))
      .forEach((key) => localStorage.removeItem(key));
  } catch (error) {
    console.error('Failed to clear game progress:', error);
  }
}
