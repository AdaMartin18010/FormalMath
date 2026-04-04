/**
 * FormalMath 游戏状态管理
 * 使用 Zustand 管理游戏化系统的全局状态
 */

import { create } from 'zustand';
import { devtools, persist } from 'zustand/middleware';
import type {
  GameState,
  GameSession,
  Puzzle,
  PuzzleLevel,
  BattleSession,
  ExplorationSession,
  Badge,
  UserBadge,
  Achievement,
  GameReward,
  TutorMessage,
  MathWorld,
  HistoryTimeline,
  Leaderboard,
  LevelSystem,
  SkillTree,
  VirtualTutor,
  PersonalizedGuidance,
  LearningRecommendation,
  GameStatistics,
  CollectionItem,
  Quest,
  GameDifficulty,
  PuzzleType,
  BattleType,
  ExplorationMode,
  GuidanceType,
  GameMode,
  GameSettings,
} from '../types/gamification';
import { gameService } from '../services/gameService';

// ==================== 游戏状态接口 ====================

interface GameStoreState extends GameState {
  // 加载状态
  isLoading: boolean;
  error: string | null;

  // 游戏数据缓存
  puzzles: Puzzle[];
  puzzleLevels: PuzzleLevel[];
  badges: Badge[];
  worlds: MathWorld[];
  timeline: HistoryTimeline | null;
  leaderboard: Leaderboard | null;
  skillTree: SkillTree | null;
  tutor: VirtualTutor | null;
  collection: CollectionItem[];

  // 游戏设置
  settings: GameSettings;

  // ========== Actions ==========

  // 初始化
  initialize: () => Promise<void>;

  // 谜题相关
  loadPuzzles: (filters?: { type?: PuzzleType; difficulty?: GameDifficulty; conceptId?: string }) => Promise<void>;
  loadPuzzleLevels: () => Promise<void>;
  startPuzzle: (puzzleId: string) => Promise<void>;
  submitPuzzleAnswer: (answer: unknown, timeSpent: number, hintsUsed: number) => Promise<{
    correct: boolean;
    score: number;
    rewards: GameReward[];
    feedback: string;
  }>;
  useHint: (puzzleId: string, hintId: string) => Promise<boolean>;

  // 对战相关
  createBattle: (type: BattleType, settings: BattleSession['settings']) => Promise<void>;
  joinBattle: (battleId: string) => Promise<void>;
  leaveBattle: () => void;
  submitBattleAnswer: (roundNumber: number, answer: string | number | string[], timeSpent: number) => Promise<void>;
  setBattleReady: (ready: boolean) => void;

  // 探索相关
  loadWorlds: () => Promise<void>;
  loadTimeline: () => Promise<void>;
  startExploration: (mode: ExplorationMode, worldId?: string) => Promise<void>;
  exploreNode: (nodeId: string) => Promise<void>;
  claimTimelineReward: (eventId: string) => Promise<void>;

  // 成就相关
  loadBadges: () => Promise<void>;
  loadAchievements: () => Promise<void>;
  checkBadgeUnlock: (action: string, data: unknown) => Promise<Badge[]>;
  loadLeaderboard: (type: Leaderboard['type'], category: Leaderboard['category']) => Promise<void>;
  loadSkillTree: () => Promise<void>;
  unlockSkill: (skillId: string) => Promise<boolean>;
  upgradeSkill: (skillId: string) => Promise<boolean>;

  // 等级系统
  loadLevelSystem: () => Promise<void>;
  addXP: (amount: number) => Promise<{ newLevel: boolean; levelUp?: { oldLevel: number; newLevel: number; rewards: GameReward[] } }>;
  addCoins: (amount: number) => void;

  // 导师系统
  loadTutor: () => Promise<void>;
  getTutorMessage: (type: GuidanceType, context?: {
    puzzleId?: string;
    conceptId?: string;
    strugglePoints?: string[];
    lastAction?: string;
  }) => Promise<TutorMessage>;
  loadPersonalizedGuidance: () => Promise<void>;
  loadRecommendations: () => Promise<void>;
  setTutorEnabled: (enabled: boolean) => void;
  setTutorPersonality: (personality: VirtualTutor['personality']) => void;

  // 收集系统
  loadCollection: () => Promise<void>;
  collectItem: (itemId: string) => Promise<void>;

  // 统计
  loadStatistics: () => Promise<void>;
  updateStatistics: (updates: Partial<GameStatistics>) => void;

  // 设置
  updateSettings: (settings: Partial<GameSettings>) => void;
  toggleSound: () => void;
  setVolume: (type: 'music' | 'sfx', volume: number) => void;

  // 会话管理
  endSession: () => void;
  clearError: () => void;
}

// ==================== 初始状态 ====================

const initialSettings: GameSettings = {
  soundEnabled: true,
  musicVolume: 0.5,
  sfxVolume: 0.7,
  tutorEnabled: true,
  tutorPersonality: 'friendly',
  hintAutoShow: false,
  notifications: {
    achievement: true,
    friendActivity: true,
    dailyReminder: true,
  },
};

const initialUserGameData = {
  userId: '',
  level: {
    currentLevel: 1,
    currentXP: 0,
    xpToNextLevel: 100,
    totalXP: 0,
    levelTitle: '数学新手',
    levelIcon: '🌱',
    unlockedFeatures: [],
  },
  coins: 100,
  gems: 10,
  badges: [],
  achievements: [],
  skillTree: null as unknown as SkillTree,
  unlockedSkills: [],
  collection: null as unknown as ConceptCollection,
  stats: {
    totalPuzzlesSolved: 0,
    totalBattlesPlayed: 0,
    totalBattlesWon: 0,
    totalExplorationTime: 0,
    puzzleStats: {
      math_riddle: { solved: 0, attempted: 0 },
      proof_construct: { solved: 0, attempted: 0 },
      concept_match: { solved: 0, attempted: 0 },
      equation_solve: { solved: 0, attempted: 0 },
      pattern_recognize: { solved: 0, attempted: 0 },
      logic_deduction: { solved: 0, attempted: 0 },
    },
    difficultyStats: {
      easy: { solved: 0, attempted: 0 },
      medium: { solved: 0, attempted: 0 },
      hard: { solved: 0, attempted: 0 },
      expert: { solved: 0, attempted: 0 },
    },
    averageSolveTime: 0,
    fastestSolveTime: Infinity,
    longestStreak: 0,
    currentStreak: 0,
    battleWinStreak: 0,
    puzzleSolveStreak: 0,
  },
  sessionHistory: [],
};

// ==================== 创建 Store ====================

export const useGameStore = create<GameStoreState>()(
  devtools(
    persist(
      (set, get) => ({
        // 初始状态
        isLoading: false,
        error: null,
        currentSession: undefined,
        userGameData: initialUserGameData,
        settings: initialSettings,
        puzzles: [],
        puzzleLevels: [],
        badges: [],
        worlds: [],
        timeline: null,
        leaderboard: null,
        skillTree: null,
        tutor: null,
        collection: [],
        activePuzzle: undefined,
        activeBattle: undefined,
        activeExploration: undefined,

        // ========== 初始化 ==========
        initialize: async () => {
          set({ isLoading: true, error: null });
          try {
            await Promise.all([
              get().loadPuzzles(),
              get().loadPuzzleLevels(),
              get().loadBadges(),
              get().loadWorlds(),
              get().loadTimeline(),
              get().loadLevelSystem(),
              get().loadTutor(),
              get().loadCollection(),
              get().loadStatistics(),
            ]);
            set({ isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        // ========== 谜题相关 ==========
        loadPuzzles: async (filters) => {
          set({ isLoading: true });
          try {
            const puzzles = await gameService.getPuzzles(filters);
            set({ puzzles, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        loadPuzzleLevels: async () => {
          set({ isLoading: true });
          try {
            const puzzleLevels = await gameService.getPuzzleLevels();
            set({ puzzleLevels, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        startPuzzle: async (puzzleId) => {
          set({ isLoading: true });
          try {
            const puzzle = await gameService.getPuzzleById(puzzleId);
            if (puzzle) {
              const session: GameSession = {
                id: gameService.generateSessionId(),
                userId: get().userGameData.userId,
                mode: 'puzzle',
                difficulty: puzzle.difficulty,
                status: 'playing',
                startedAt: new Date().toISOString(),
                score: 0,
                timeSpent: 0,
                rewards: [],
              };
              set({ 
                activePuzzle: puzzle, 
                currentSession: session,
                isLoading: false 
              });
            }
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        submitPuzzleAnswer: async (answer, timeSpent, hintsUsed) => {
          const { activePuzzle, currentSession, userGameData } = get();
          if (!activePuzzle || !currentSession) {
            throw new Error('No active puzzle');
          }

          set({ isLoading: true });
          try {
            const result = await gameService.submitPuzzleAnswer(
              activePuzzle.id,
              answer,
              timeSpent,
              hintsUsed
            );

            if (result.correct) {
              // 更新会话
              const updatedSession: GameSession = {
                ...currentSession,
                score: currentSession.score + result.score,
                timeSpent: currentSession.timeSpent + timeSpent,
                rewards: [...currentSession.rewards, ...result.rewards],
                status: 'completed',
                endedAt: new Date().toISOString(),
              };

              // 更新统计
              const puzzleType = activePuzzle.type;
              const difficulty = activePuzzle.difficulty;
              
              set({
                currentSession: updatedSession,
                userGameData: {
                  ...userGameData,
                  stats: {
                    ...userGameData.stats,
                    totalPuzzlesSolved: userGameData.stats.totalPuzzlesSolved + 1,
                    puzzleStats: {
                      ...userGameData.stats.puzzleStats,
                      [puzzleType]: {
                        solved: (userGameData.stats.puzzleStats[puzzleType]?.solved || 0) + 1,
                        attempted: (userGameData.stats.puzzleStats[puzzleType]?.attempted || 0) + 1,
                      },
                    },
                    difficultyStats: {
                      ...userGameData.stats.difficultyStats,
                      [difficulty]: {
                        solved: (userGameData.stats.difficultyStats[difficulty]?.solved || 0) + 1,
                        attempted: (userGameData.stats.difficultyStats[difficulty]?.attempted || 0) + 1,
                      },
                    },
                    puzzleSolveStreak: userGameData.stats.puzzleSolveStreak + 1,
                  },
                  sessionHistory: [...userGameData.sessionHistory, updatedSession],
                },
                isLoading: false,
              });

              // 添加奖励
              for (const reward of result.rewards) {
                if (reward.type === 'xp') {
                  await get().addXP(reward.amount || 0);
                } else if (reward.type === 'coin') {
                  get().addCoins(reward.amount || 0);
                }
              }

              // 检查徽章解锁
              await get().checkBadgeUnlock('puzzle_complete', { puzzleId: activePuzzle.id });
            } else {
              // 回答错误，重置连胜
              set({
                userGameData: {
                  ...userGameData,
                  stats: {
                    ...userGameData.stats,
                    puzzleSolveStreak: 0,
                  },
                },
                isLoading: false,
              });
            }

            return result;
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
            throw error;
          }
        },

        useHint: async (puzzleId, hintId) => {
          const { userGameData } = get();
          // 扣除金币
          const hintCost = 5;
          if (userGameData.coins >= hintCost) {
            set({
              userGameData: {
                ...userGameData,
                coins: userGameData.coins - hintCost,
              },
            });
            return true;
          }
          return false;
        },

        // ========== 对战相关 ==========
        createBattle: async (type, settings) => {
          set({ isLoading: true });
          try {
            const battle = await gameService.createBattle(type, settings);
            set({ 
              activeBattle: battle,
              currentSession: {
                id: battle.id,
                userId: get().userGameData.userId,
                mode: 'battle',
                difficulty: settings.difficulty,
                status: 'playing',
                startedAt: battle.createdAt,
                score: 0,
                timeSpent: 0,
                rewards: [],
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        joinBattle: async (battleId) => {
          set({ isLoading: true });
          try {
            const battle = await gameService.joinBattle(battleId);
            set({ 
              activeBattle: battle,
              currentSession: {
                id: battle.id,
                userId: get().userGameData.userId,
                mode: 'battle',
                difficulty: battle.settings.difficulty,
                status: 'playing',
                startedAt: battle.createdAt,
                score: 0,
                timeSpent: 0,
                rewards: [],
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        leaveBattle: () => {
          set({ activeBattle: undefined, currentSession: undefined });
        },

        submitBattleAnswer: async (roundNumber, answer, timeSpent) => {
          const { activeBattle, userGameData } = get();
          if (!activeBattle) return;

          set({ isLoading: true });
          try {
            const playerAnswer = {
              userId: userGameData.userId,
              answer,
              submittedAt: new Date().toISOString(),
              timeSpent,
              isCorrect: true, // 客户端验证
              score: 0,
              hintsUsed: 0,
            };

            const result = await gameService.submitBattleAnswer(
              activeBattle.id,
              roundNumber,
              playerAnswer
            );

            set({ isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        setBattleReady: (ready) => {
          const { activeBattle } = get();
          if (activeBattle) {
            set({
              activeBattle: {
                ...activeBattle,
                opponent: activeBattle.opponent
                  ? { ...activeBattle.opponent, ready }
                  : undefined,
              },
            });
          }
        },

        // ========== 探索相关 ==========
        loadWorlds: async () => {
          set({ isLoading: true });
          try {
            const worlds = await gameService.getMathWorlds();
            set({ worlds, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        loadTimeline: async () => {
          set({ isLoading: true });
          try {
            const timeline = await gameService.getHistoryTimeline();
            set({ timeline, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        startExploration: async (mode, worldId) => {
          set({ isLoading: true });
          try {
            const exploration = await gameService.startExploration(mode, worldId);
            set({ 
              activeExploration: exploration,
              currentSession: {
                id: exploration.id,
                userId: get().userGameData.userId,
                mode: 'exploration',
                difficulty: 'easy',
                status: 'playing',
                startedAt: exploration.startedAt,
                score: 0,
                timeSpent: 0,
                rewards: [],
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        exploreNode: async (nodeId) => {
          const { activeExploration } = get();
          if (!activeExploration) return;

          set({ isLoading: true });
          try {
            const result = await gameService.exploreNode(activeExploration.id, nodeId);
            set({ 
              activeExploration: result.session,
              isLoading: false 
            });

            // 添加奖励
            for (const reward of result.rewards) {
              if (reward.type === 'xp') {
                await get().addXP(reward.amount || 0);
              } else if (reward.type === 'coin') {
                get().addCoins(reward.amount || 0);
              }
            }
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        claimTimelineReward: async (eventId) => {
          // 标记奖励已领取
          set({ isLoading: false });
        },

        // ========== 成就相关 ==========
        loadBadges: async () => {
          set({ isLoading: true });
          try {
            const badges = await gameService.getBadges();
            const userBadges = await gameService.getUserBadges(get().userGameData.userId);
            set({ 
              badges,
              userGameData: {
                ...get().userGameData,
                badges: userBadges,
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        loadAchievements: async () => {
          set({ isLoading: true });
          try {
            const achievements = await gameService.getAchievements(get().userGameData.userId);
            set({ 
              userGameData: {
                ...get().userGameData,
                achievements,
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        checkBadgeUnlock: async (action, data) => {
          try {
            const unlockedBadges = await gameService.checkBadgeUnlock(
              get().userGameData.userId,
              action,
              data
            );
            
            if (unlockedBadges.length > 0) {
              const newUserBadges: UserBadge[] = unlockedBadges.map((badge) => ({
                badgeId: badge.id,
                earnedAt: new Date().toISOString(),
                progress: 100,
                isNew: true,
              }));

              set({
                userGameData: {
                  ...get().userGameData,
                  badges: [...get().userGameData.badges, ...newUserBadges],
                },
              });
            }

            return unlockedBadges;
          } catch (error) {
            console.error('Failed to check badge unlock:', error);
            return [];
          }
        },

        loadLeaderboard: async (type, category) => {
          set({ isLoading: true });
          try {
            const leaderboard = await gameService.getLeaderboard(type, category);
            set({ leaderboard, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        loadSkillTree: async () => {
          set({ isLoading: true });
          try {
            const skillTree = await gameService.getSkillTree();
            set({ 
              skillTree,
              userGameData: {
                ...get().userGameData,
                skillTree,
              },
              isLoading: false 
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        unlockSkill: async (skillId) => {
          const result = await gameService.unlockSkill(skillId);
          if (result) {
            set({
              userGameData: {
                ...get().userGameData,
                unlockedSkills: [...get().userGameData.unlockedSkills, skillId],
              },
            });
          }
          return result;
        },

        upgradeSkill: async (skillId) => {
          return await gameService.upgradeSkill(skillId);
        },

        // ========== 等级系统 ==========
        loadLevelSystem: async () => {
          set({ isLoading: true });
          try {
            const levelSystem = await gameService.getLevelSystem(get().userGameData.userId);
            set({
              userGameData: {
                ...get().userGameData,
                level: levelSystem,
              },
              isLoading: false,
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        addXP: async (amount) => {
          const result = await gameService.addXP(get().userGameData.userId, amount);
          
          if (result.newLevel && result.levelUp) {
            // 升级了
            set({
              userGameData: {
                ...get().userGameData,
                level: {
                  ...get().userGameData.level,
                  currentLevel: result.levelUp.newLevel,
                  currentXP: 0,
                  xpToNextLevel: get().userGameData.level.xpToNextLevel + 50,
                  totalXP: get().userGameData.level.totalXP + amount,
                  levelTitle: gameService.calculateLevelTitle(result.levelUp.newLevel),
                  unlockedFeatures: [
                    ...get().userGameData.level.unlockedFeatures,
                    ...result.levelUp.rewards
                      .filter((r) => r.type === 'unlock')
                      .map((r) => r.unlockedConceptId || ''),
                  ].filter(Boolean),
                },
              },
            });
          } else {
            // 未升级
            set({
              userGameData: {
                ...get().userGameData,
                level: {
                  ...get().userGameData.level,
                  currentXP: get().userGameData.level.currentXP + amount,
                  totalXP: get().userGameData.level.totalXP + amount,
                },
              },
            });
          }

          return result;
        },

        addCoins: (amount) => {
          set({
            userGameData: {
              ...get().userGameData,
              coins: get().userGameData.coins + amount,
            },
          });
        },

        // ========== 导师系统 ==========
        loadTutor: async () => {
          set({ isLoading: true });
          try {
            const tutor = await gameService.getVirtualTutor();
            set({ tutor, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        getTutorMessage: async (type, context = {}) => {
          const message = await gameService.getTutorMessage(type, context);
          return message;
        },

        loadPersonalizedGuidance: async () => {
          // 个性化指导已加载
        },

        loadRecommendations: async () => {
          // 加载推荐
        },

        setTutorEnabled: (enabled) => {
          set({
            settings: {
              ...get().settings,
              tutorEnabled: enabled,
            },
          });
        },

        setTutorPersonality: (personality) => {
          set({
            settings: {
              ...get().settings,
              tutorPersonality: personality,
            },
            tutor: get().tutor
              ? { ...get().tutor!, personality }
              : null,
          });
        },

        // ========== 收集系统 ==========
        loadCollection: async () => {
          set({ isLoading: true });
          try {
            const items = await gameService.getCollectionItems(get().userGameData.userId);
            set({ collection: items, isLoading: false });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        collectItem: async (itemId) => {
          const result = await gameService.collectItem(get().userGameData.userId, itemId);
          if (result.success) {
            await get().loadCollection();
          }
        },

        // ========== 统计 ==========
        loadStatistics: async () => {
          set({ isLoading: true });
          try {
            const stats = await gameService.getGameStatistics(get().userGameData.userId);
            set({
              userGameData: {
                ...get().userGameData,
                stats,
              },
              isLoading: false,
            });
          } catch (error) {
            set({ error: (error as Error).message, isLoading: false });
          }
        },

        updateStatistics: (updates) => {
          set({
            userGameData: {
              ...get().userGameData,
              stats: {
                ...get().userGameData.stats,
                ...updates,
              },
            },
          });
        },

        // ========== 设置 ==========
        updateSettings: (newSettings) => {
          set({
            settings: {
              ...get().settings,
              ...newSettings,
            },
          });
        },

        toggleSound: () => {
          set({
            settings: {
              ...get().settings,
              soundEnabled: !get().settings.soundEnabled,
            },
          });
        },

        setVolume: (type, volume) => {
          set({
            settings: {
              ...get().settings,
              [type === 'music' ? 'musicVolume' : 'sfxVolume']: volume,
            },
          });
        },

        // ========== 会话管理 ==========
        endSession: () => {
          const { currentSession, userGameData } = get();
          if (currentSession) {
            const endedSession: GameSession = {
              ...currentSession,
              status: 'completed',
              endedAt: new Date().toISOString(),
            };
            set({
              currentSession: undefined,
              activePuzzle: undefined,
              activeBattle: undefined,
              activeExploration: undefined,
              userGameData: {
                ...userGameData,
                sessionHistory: [...userGameData.sessionHistory, endedSession],
              },
            });
          }
        },

        clearError: () => {
          set({ error: null });
        },
      }),
      {
        name: 'formalmath-game-store',
        partialize: (state) => ({
          userGameData: state.userGameData,
          settings: state.settings,
        }),
      }
    ),
    { name: 'GameStore' }
  )
);

export default useGameStore;
