/**
 * 成就系统 Hook
 * 提供徽章、成就、技能树和排行榜功能
 */

import { useState, useCallback, useEffect, useMemo } from 'react';
import useGameStore from '../../stores/gameStore';
import type {
  Badge,
  UserBadge,
  Achievement,
  SkillTree,
  SkillNode,
  Leaderboard,
  LevelSystem,
  GameReward,
  BadgeRarity,
  BadgeCategory,
} from '../../types/gamification';

interface UseAchievementsOptions {
  onBadgeUnlock?: (badge: Badge) => void;
  onAchievementComplete?: (achievement: Achievement) => void;
  onLevelUp?: (oldLevel: number, newLevel: number, rewards: GameReward[]) => void;
  onSkillUnlock?: (skill: SkillNode) => void;
}

interface UseAchievementsReturn {
  // 等级系统
  level: LevelSystem;
  currentLevel: number;
  currentXP: number;
  xpToNextLevel: number;
  progressToNextLevel: number;
  levelTitle: string;

  // 徽章
  allBadges: Badge[];
  userBadges: UserBadge[];
  unlockedBadges: Badge[];
  lockedBadges: Badge[];
  newBadges: Badge[];

  // 成就
  achievements: Achievement[];
  completedAchievements: Achievement[];
  inProgressAchievements: Achievement[];

  // 技能树
  skillTree: SkillTree | null;
  unlockedSkills: SkillNode[];
  availableSkills: SkillNode[];

  // 排行榜
  leaderboard: Leaderboard | null;
  userRank: number | null;

  // 方法
  loadBadges: () => Promise<void>;
  loadAchievements: () => Promise<void>;
  loadSkillTree: () => Promise<void>;
  loadLeaderboard: (type: Leaderboard['type'], category: Leaderboard['category']) => Promise<void>;
  loadLevelSystem: () => Promise<void>;

  unlockSkill: (skillId: string) => Promise<boolean>;
  upgradeSkill: (skillId: string) => Promise<boolean>;
  addXP: (amount: number) => Promise<void>;
  markBadgeAsSeen: (badgeId: string) => void;

  // 筛选
  getBadgesByCategory: (category: BadgeCategory) => Badge[];
  getBadgesByRarity: (rarity: BadgeRarity) => Badge[];
  getAchievementProgress: (achievementId: string) => number;

  // 状态
  isLoading: boolean;
}

export function useAchievements(options: UseAchievementsOptions = {}): UseAchievementsReturn {
  const store = useGameStore();
  const [prevLevel, setPrevLevel] = useState(store.userGameData.level.currentLevel);

  // 计算进度百分比
  const progressToNextLevel = useMemo(() => {
    const { currentXP, xpToNextLevel } = store.userGameData.level;
    return Math.min(100, Math.round((currentXP / xpToNextLevel) * 100));
  }, [store.userGameData.level]);

  // 已解锁和未解锁徽章
  const { unlockedBadges, lockedBadges, newBadges } = useMemo(() => {
    const userBadgeIds = new Set(store.userGameData.badges.map((b) => b.badgeId));
    
    const unlocked = store.badges.filter((b) => userBadgeIds.has(b.id));
    const locked = store.badges.filter((b) => !userBadgeIds.has(b.id));
    const newB = unlocked.filter(
      (b) => store.userGameData.badges.find((ub) => ub.badgeId === b.id)?.isNew
    );

    return { unlockedBadges: unlocked, lockedBadges: locked, newBadges: newB };
  }, [store.badges, store.userGameData.badges]);

  // 已完成和进行中的成就
  const { completedAchievements, inProgressAchievements } = useMemo(() => {
    const completed = store.userGameData.achievements.filter((a) => a.isCompleted);
    const inProgress = store.userGameData.achievements.filter((a) => !a.isCompleted);
    return { completedAchievements: completed, inProgressAchievements: inProgress };
  }, [store.userGameData.achievements]);

  // 已解锁和可用技能
  const { unlockedSkills, availableSkills } = useMemo(() => {
    if (!store.skillTree) return { unlockedSkills: [], availableSkills: [] };

    const unlocked: SkillNode[] = [];
    const available: SkillNode[] = [];

    for (const branch of store.skillTree.branches) {
      for (const skill of branch.skills) {
        if (skill.isUnlocked) {
          unlocked.push(skill);
        } else if (
          skill.prerequisites.every((p) =>
            store.userGameData.unlockedSkills.includes(p)
          )
        ) {
          available.push(skill);
        }
      }
    }

    return { unlockedSkills: unlocked, availableSkills: available };
  }, [store.skillTree, store.userGameData.unlockedSkills]);

  // 监听等级变化
  useEffect(() => {
    const currentLevel = store.userGameData.level.currentLevel;
    if (currentLevel > prevLevel) {
      options.onLevelUp?.(prevLevel, currentLevel, []);
      setPrevLevel(currentLevel);
    }
  }, [store.userGameData.level.currentLevel, prevLevel, options]);

  // 加载徽章
  const loadBadges = useCallback(async () => {
    await store.loadBadges();
  }, [store]);

  // 加载成就
  const loadAchievements = useCallback(async () => {
    await store.loadAchievements();
  }, [store]);

  // 加载技能树
  const loadSkillTree = useCallback(async () => {
    await store.loadSkillTree();
  }, [store]);

  // 加载排行榜
  const loadLeaderboard = useCallback(
    async (type: Leaderboard['type'], category: Leaderboard['category']) => {
      await store.loadLeaderboard(type, category);
    },
    [store]
  );

  // 加载等级系统
  const loadLevelSystem = useCallback(async () => {
    await store.loadLevelSystem();
  }, [store]);

  // 解锁技能
  const unlockSkill = useCallback(
    async (skillId: string) => {
      const result = await store.unlockSkill(skillId);
      if (result) {
        const skill = store.skillTree?.branches
          .flatMap((b) => b.skills)
          .find((s) => s.id === skillId);
        if (skill) {
          options.onSkillUnlock?.(skill);
        }
      }
      return result;
    },
    [store, options]
  );

  // 升级技能
  const upgradeSkill = useCallback(
    async (skillId: string) => {
      return await store.upgradeSkill(skillId);
    },
    [store]
  );

  // 添加经验
  const addXP = useCallback(
    async (amount: number) => {
      const result = await store.addXP(amount);
      if (result.newLevel && result.levelUp) {
        options.onLevelUp?.(
          result.levelUp.oldLevel,
          result.levelUp.newLevel,
          result.levelUp.rewards
        );
      }
    },
    [store, options]
  );

  // 标记徽章为已查看
  const markBadgeAsSeen = useCallback(
    (badgeId: string) => {
      const badge = store.userGameData.badges.find((b) => b.badgeId === badgeId);
      if (badge) {
        badge.isNew = false;
      }
    },
    [store.userGameData.badges]
  );

  // 按分类筛选徽章
  const getBadgesByCategory = useCallback(
    (category: BadgeCategory) => {
      return store.badges.filter((b) => b.category === category);
    },
    [store.badges]
  );

  // 按稀有度筛选徽章
  const getBadgesByRarity = useCallback(
    (rarity: BadgeRarity) => {
      return store.badges.filter((b) => b.rarity === rarity);
    },
    [store.badges]
  );

  // 获取成就进度
  const getAchievementProgress = useCallback(
    (achievementId: string) => {
      const achievement = store.userGameData.achievements.find(
        (a) => a.id === achievementId
      );
      return achievement ? (achievement.currentValue / achievement.targetValue) * 100 : 0;
    },
    [store.userGameData.achievements]
  );

  // 初始化加载
  useEffect(() => {
    loadBadges();
    loadAchievements();
    loadSkillTree();
    loadLevelSystem();
  }, []);

  return {
    level: store.userGameData.level,
    currentLevel: store.userGameData.level.currentLevel,
    currentXP: store.userGameData.level.currentXP,
    xpToNextLevel: store.userGameData.level.xpToNextLevel,
    progressToNextLevel,
    levelTitle: store.userGameData.level.levelTitle,

    allBadges: store.badges,
    userBadges: store.userGameData.badges,
    unlockedBadges,
    lockedBadges,
    newBadges,

    achievements: store.userGameData.achievements,
    completedAchievements,
    inProgressAchievements,

    skillTree: store.skillTree,
    unlockedSkills,
    availableSkills,

    leaderboard: store.leaderboard,
    userRank: store.leaderboard?.userRank || null,

    loadBadges,
    loadAchievements,
    loadSkillTree,
    loadLeaderboard,
    loadLevelSystem,

    unlockSkill,
    upgradeSkill,
    addXP,
    markBadgeAsSeen,

    getBadgesByCategory,
    getBadgesByRarity,
    getAchievementProgress,

    isLoading: store.isLoading,
  };
}

export default useAchievements;
