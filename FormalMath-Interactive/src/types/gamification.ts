/**
 * FormalMath 游戏化系统类型定义
 * 包含解谜游戏、对战模式、探索模式、成就系统和虚拟导师
 */

// ==================== 通用游戏类型 ====================

export type GameDifficulty = 'easy' | 'medium' | 'hard' | 'expert';
export type GameStatus = 'idle' | 'playing' | 'paused' | 'completed' | 'failed';
export type GameMode = 'puzzle' | 'battle' | 'exploration' | 'tutorial';

export interface GameSession {
  id: string;
  userId: string;
  mode: GameMode;
  difficulty: GameDifficulty;
  status: GameStatus;
  startedAt: string;
  endedAt?: string;
  score: number;
  timeSpent: number;
  rewards: GameReward[];
}

export interface GameReward {
  type: 'xp' | 'coin' | 'badge' | 'item' | 'unlock';
  amount?: number;
  itemId?: string;
  badgeId?: string;
  unlockedConceptId?: string;
}

// ==================== T4.1 解谜游戏 ====================

export type PuzzleType = 
  | 'math_riddle'      // 数学谜题
  | 'proof_construct'  // 证明构造
  | 'concept_match'    // 概念连线
  | 'equation_solve'   // 方程求解
  | 'pattern_recognize'// 模式识别
  | 'logic_deduction'; // 逻辑推导

export interface Puzzle {
  id: string;
  type: PuzzleType;
  title: string;
  description: string;
  difficulty: GameDifficulty;
  conceptIds: string[];
  estimatedTime: number;
  
  // 谜题内容
  content: PuzzleContent;
  
  // 提示系统
  hints: Hint[];
  
  // 奖励
  baseReward: GameReward[];
  timeBonus: boolean;
  
  // 元数据
  author?: string;
  createdAt: string;
  playCount: number;
  passRate: number;
}

export type PuzzleContent = 
  | MathRiddleContent 
  | ProofConstructContent 
  | ConceptMatchContent
  | EquationSolveContent
  | PatternRecognizeContent
  | LogicDeductionContent;

export interface MathRiddleContent {
  problem: string;
  variables: Record<string, number | string>;
  solution: string | number;
  solutionSteps: string[];
  answerType: 'number' | 'text' | 'multiple_choice';
  options?: string[];
}

export interface ProofConstructContent {
  theorem: string;
  given: string[];
  goal: string;
  availableSteps: ProofStepOption[];
  correctSequence: string[];
  partialCredit: boolean;
}

export interface ProofStepOption {
  id: string;
  content: string;
  isCorrect: boolean;
  explanation: string;
}

export interface ConceptMatchContent {
  concepts: MatchItem[];
  definitions: MatchItem[];
  relationships: MatchItem[];
  pairs: { left: string; right: string }[];
}

export interface MatchItem {
  id: string;
  content: string;
  type: 'concept' | 'definition' | 'relationship';
}

export interface EquationSolveContent {
  equation: string;
  variables: string[];
  steps: EquationStep[];
  finalSolution: Record<string, number>;
}

export interface EquationStep {
  id: string;
  description: string;
  operation: string;
  result: string;
}

export interface PatternRecognizeContent {
  sequence: (number | string)[];
  pattern: string;
  nextTerms: (number | string)[];
  generalFormula?: string;
  hintImages?: string[];
}

export interface LogicDeductionContent {
  premises: string[];
  conclusions: LogicConclusion[];
  rules: string[];
}

export interface LogicConclusion {
  id: string;
  statement: string;
  isValid: boolean;
  explanation: string;
}

export interface Hint {
  id: string;
  level: number;
  content: string;
  cost: number;
  used: boolean;
}

export interface PuzzleLevel {
  id: string;
  name: string;
  description: string;
  puzzles: string[];
  requiredScore: number;
  unlockCriteria: UnlockCriteria;
  rewards: GameReward[];
}

export interface UnlockCriteria {
  minLevel?: number;
  requiredBadges?: string[];
  completedPuzzles?: string[];
  minTotalScore?: number;
}

// ==================== T4.2 对战模式 ====================

export type BattleType = 'speed_challenge' | 'proof_race' | 'quiz_duel' | 'team_battle';
export type BattleStatus = 'waiting' | 'starting' | 'in_progress' | 'finished' | 'cancelled';

export interface BattleSession {
  id: string;
  type: BattleType;
  status: BattleStatus;
  createdAt: string;
  startedAt?: string;
  endedAt?: string;
  
  // 参与者
  host: BattlePlayer;
  opponent?: BattlePlayer;
  spectators?: string[];
  
  // 对战设置
  settings: BattleSettings;
  
  // 当前状态
  currentRound: number;
  totalRounds: number;
  rounds: BattleRound[];
  
  // 结果
  winner?: string;
  finalScores: Record<string, number>;
}

export interface BattlePlayer {
  userId: string;
  name: string;
  avatar?: string;
  level: number;
  rating: number;
  ready: boolean;
  connected: boolean;
}

export interface BattleSettings {
  difficulty: GameDifficulty;
  timePerQuestion: number;
  questionCount: number;
  categoryFilter?: string[];
  allowHelpers: boolean;
  isPrivate: boolean;
  password?: string;
}

export interface BattleRound {
  roundNumber: number;
  puzzleId: string;
  puzzleType: PuzzleType;
  
  // 玩家答案
  playerAnswers: Record<string, PlayerAnswer>;
  
  // 本轮结果
  scores: Record<string, number>;
  winner?: string;
  endedAt?: string;
}

export interface PlayerAnswer {
  userId: string;
  answer: string | number | string[];
  submittedAt: string;
  timeSpent: number;
  isCorrect: boolean;
  score: number;
  hintsUsed: number;
}

export interface SpeedChallenge extends BattleSession {
  type: 'speed_challenge';
  consecutiveCorrectBonus: boolean;
  streakMultiplier: number;
}

export interface ProofRace extends BattleSession {
  type: 'proof_race';
  theoremId: string;
  checkpoints: ProofCheckpoint[];
}

export interface ProofCheckpoint {
  id: string;
  description: string;
  completedBy: string[];
  completedAt: Record<string, string>;
}

export interface QuizDuel extends BattleSession {
  type: 'quiz_duel';
  categories: string[];
  lifelines: Record<string, LifelineStatus>;
}

export interface LifelineStatus {
  fiftyFifty: boolean;
  hint: boolean;
  extraTime: boolean;
}

// ==================== T4.3 探索模式 ====================

export type ExplorationMode = 'world' | 'timeline' | 'collection';

export interface ExplorationSession {
  id: string;
  userId: string;
  mode: ExplorationMode;
  startedAt: string;
  currentPosition: ExplorationPosition;
  visitedNodes: string[];
  unlockedNodes: string[];
  collectedItems: string[];
  progress: ExplorationProgress;
}

export interface ExplorationPosition {
  nodeId: string;
  x: number;
  y: number;
}

export interface ExplorationProgress {
  totalNodes: number;
  visitedCount: number;
  unlockedCount: number;
  completionRate: number;
}

// 数学世界探索
export interface MathWorld {
  id: string;
  name: string;
  description: string;
  theme: string;
  backgroundImage?: string;
  
  // 世界结构
  regions: WorldRegion[];
  connections: RegionConnection[];
  
  // 解锁条件
  unlockCriteria: UnlockCriteria;
  
  // 奖励
  completionRewards: GameReward[];
}

export interface WorldRegion {
  id: string;
  name: string;
  description: string;
  type: 'domain' | 'concept_cluster' | 'challenge_area' | 'rest_area';
  position: { x: number; y: number };
  
  // 内容
  conceptIds: string[];
  puzzles: string[];
  npcs?: NPC[];
  
  // 状态
  isLocked: boolean;
  isVisited: boolean;
  isCompleted: boolean;
}

export interface RegionConnection {
  from: string;
  to: string;
  type: 'path' | 'portal' | 'bridge';
  requiredItem?: string;
  requiredLevel?: number;
}

export interface NPC {
  id: string;
  name: string;
  avatar: string;
  role: 'guide' | 'merchant' | 'challenger' | 'historian';
  dialogues: Dialogue[];
  quests?: Quest[];
}

export interface Dialogue {
  id: string;
  trigger: 'greeting' | 'quest_complete' | 'hint_request' | 'story';
  content: string;
  options?: DialogueOption[];
}

export interface DialogueOption {
  text: string;
  nextDialogueId?: string;
  action?: 'give_quest' | 'give_hint' | 'open_shop' | 'start_challenge';
}

export interface Quest {
  id: string;
  title: string;
  description: string;
  type: 'explore' | 'solve' | 'collect' | 'defeat';
  objectives: QuestObjective[];
  rewards: GameReward[];
  isCompleted: boolean;
}

export interface QuestObjective {
  id: string;
  description: string;
  targetId: string;
  targetCount: number;
  currentCount: number;
}

// 历史时间线
export interface HistoryTimeline {
  id: string;
  name: string;
  description: string;
  timeRange: { start: number; end: number };
  
  // 时代
  eras: TimelineEra[];
  
  // 事件
  events: TimelineEvent[];
}

export interface TimelineEra {
  id: string;
  name: string;
  period: { start: number; end: number };
  description: string;
  color: string;
}

export interface TimelineEvent {
  id: string;
  title: string;
  description: string;
  date: number;
  eraId: string;
  
  // 内容
  conceptIds: string[];
  mathematicianIds: string[];
  theoremIds: string[];
  
  // 互动
  puzzleId?: string;
  quizId?: string;
  
  // 状态
  isUnlocked: boolean;
  isVisited: boolean;
  rewardsClaimed: boolean;
}

// 概念收集
export interface ConceptCollection {
  id: string;
  userId: string;
  categories: CollectionCategory[];
  totalCollected: number;
  totalAvailable: number;
}

export interface CollectionCategory {
  id: string;
  name: string;
  icon: string;
  items: CollectionItem[];
}

export interface CollectionItem {
  id: string;
  conceptId: string;
  name: string;
  description: string;
  rarity: 'common' | 'uncommon' | 'rare' | 'epic' | 'legendary';
  image?: string;
  
  // 获取条件
  unlockCondition: string;
  isUnlocked: boolean;
  unlockedAt?: string;
  
  // 展示
  funFact?: string;
  relatedConcepts: string[];
}

// ==================== T4.4 成就系统 ====================

export type BadgeCategory = 
  | 'learning'      // 学习成就
  | 'puzzle'        // 解谜成就
  | 'battle'        // 对战成就
  | 'exploration'   // 探索成就
  | 'social'        // 社交成就
  | 'special';      // 特殊成就

export type BadgeRarity = 'common' | 'uncommon' | 'rare' | 'epic' | 'legendary';

export interface Badge {
  id: string;
  name: string;
  description: string;
  category: BadgeCategory;
  rarity: BadgeRarity;
  icon: string;
  
  // 解锁条件
  unlockCondition: BadgeCondition;
  
  // 元数据
  createdAt: string;
  hidden: boolean; // 是否为隐藏成就
}

export type BadgeCondition = 
  | { type: 'puzzle_count'; count: number; difficulty?: GameDifficulty }
  | { type: 'puzzle_streak'; streak: number }
  | { type: 'battle_win'; count: number }
  | { type: 'battle_streak'; streak: number }
  | { type: 'explore_region'; regionId: string }
  | { type: 'collect_items'; count: number; category?: string }
  | { type: 'complete_quest'; questId: string }
  | { type: 'reach_level'; level: number }
  | { type: 'master_concept'; conceptId: string }
  | { type: 'special_event'; eventId: string };

export interface UserBadge {
  badgeId: string;
  earnedAt: string;
  progress: number;
  isNew: boolean;
}

export interface Achievement {
  id: string;
  userId: string;
  type: string;
  title: string;
  description: string;
  
  // 进度
  targetValue: number;
  currentValue: number;
  isCompleted: boolean;
  completedAt?: string;
  
  // 奖励
  reward: GameReward[];
}

// 技能树
export interface SkillTree {
  id: string;
  name: string;
  description: string;
  branches: SkillBranch[];
}

export interface SkillBranch {
  id: string;
  name: string;
  color: string;
  skills: SkillNode[];
}

export interface SkillNode {
  id: string;
  name: string;
  description: string;
  icon: string;
  level: number;
  maxLevel: number;
  
  // 效果
  effects: SkillEffect[];
  
  // 解锁条件
  prerequisites: string[];
  unlockCost: { type: 'xp' | 'coin'; amount: number };
  
  // 状态
  isUnlocked: boolean;
  currentLevel: number;
}

export interface SkillEffect {
  type: 'xp_boost' | 'time_bonus' | 'hint_discount' | 'extra_lives' | 'unlock_content';
  value: number;
  description: string;
}

// 等级系统
export interface LevelSystem {
  currentLevel: number;
  currentXP: number;
  xpToNextLevel: number;
  totalXP: number;
  
  // 等级信息
  levelTitle: string;
  levelIcon: string;
  
  // 特权
  unlockedFeatures: string[];
}

export interface LevelDefinition {
  level: number;
  title: string;
  icon: string;
  xpRequired: number;
  rewards: GameReward[];
  unlockedFeatures: string[];
}

// 排行榜
export interface Leaderboard {
  id: string;
  name: string;
  type: 'global' | 'weekly' | 'daily' | 'friends';
  category: 'xp' | 'puzzle' | 'battle' | 'collection';
  
  // 条目
  entries: LeaderboardEntry[];
  
  // 时间范围
  startTime?: string;
  endTime?: string;
  
  // 用户排名
  userRank?: number;
  userEntry?: LeaderboardEntry;
}

export interface LeaderboardEntry {
  rank: number;
  userId: string;
  name: string;
  avatar?: string;
  score: number;
  level: number;
  trend: 'up' | 'down' | 'stable';
  isCurrentUser: boolean;
}

// ==================== T4.5 虚拟导师 ====================

export type TutorPersonality = 'encouraging' | 'strict' | 'friendly' | 'scholarly' | 'mysterious';
export type GuidanceType = 'hint' | 'explanation' | 'feedback' | 'motivation' | 'challenge';

export interface VirtualTutor {
  id: string;
  name: string;
  avatar: string;
  personality: TutorPersonality;
  
  // 能力
  capabilities: TutorCapability[];
  
  // 状态
  isActive: boolean;
  currentContext?: GuidanceContext;
}

export interface TutorCapability {
  type: GuidanceType;
  level: number;
  enabled: boolean;
}

export interface GuidanceContext {
  userId: string;
  currentActivity: GameMode;
  currentPuzzleId?: string;
  currentConceptId?: string;
  strugglePoints: string[];
  recentPerformance: PerformanceSnapshot;
}

export interface PerformanceSnapshot {
  accuracy: number;
  averageTime: number;
  streakCount: number;
  lastAttemptResult: 'success' | 'failure' | 'hint_used';
}

export interface TutorMessage {
  id: string;
  type: GuidanceType;
  content: string;
  timestamp: string;
  
  // 上下文
  relatedConceptId?: string;
  relatedPuzzleId?: string;
  
  // 交互
  actions?: TutorAction[];
  followUpQuestions?: string[];
}

export interface TutorAction {
  id: string;
  label: string;
  type: 'show_hint' | 'explain_concept' | 'give_example' | 'simplify' | 'challenge' | 'encourage';
  payload?: unknown;
}

export interface PersonalizedGuidance {
  userId: string;
  learningStyle: 'visual' | 'auditory' | 'kinesthetic' | 'reading';
  difficultyPreference: GameDifficulty;
  interestAreas: string[];
  
  // 指导策略
  hintFrequency: 'high' | 'medium' | 'low';
  encouragementLevel: 'high' | 'medium' | 'low';
  challengePreference: 'conservative' | 'balanced' | 'aggressive';
}

export interface LearningRecommendation {
  id: string;
  type: 'next_puzzle' | 'review_concept' | 'try_battle' | 'explore_world' | 'take_break';
  title: string;
  description: string;
  reason: string;
  targetId: string;
  priority: number;
  estimatedTime: number;
}

// ==================== 游戏状态管理 ====================

export interface GameState {
  // 会话
  currentSession?: GameSession;
  
  // 用户游戏数据
  userGameData: UserGameData;
  
  // 游戏设置
  settings: GameSettings;
  
  // 活跃游戏
  activePuzzle?: Puzzle;
  activeBattle?: BattleSession;
  activeExploration?: ExplorationSession;
}

export interface UserGameData {
  userId: string;
  
  // 等级与经验
  level: LevelSystem;
  
  // 货币
  coins: number;
  gems: number;
  
  // 成就
  badges: UserBadge[];
  achievements: Achievement[];
  
  // 技能树
  skillTree: SkillTree;
  unlockedSkills: string[];
  
  // 收集
  collection: ConceptCollection;
  
  // 统计
  stats: GameStatistics;
  
  // 历史
  sessionHistory: GameSession[];
}

export interface GameSettings {
  soundEnabled: boolean;
  musicVolume: number;
  sfxVolume: number;
  
  // 导师设置
  tutorEnabled: boolean;
  tutorPersonality: TutorPersonality;
  hintAutoShow: boolean;
  
  // 通知
  notifications: {
    achievement: boolean;
    friendActivity: boolean;
    dailyReminder: boolean;
  };
}

export interface GameStatistics {
  totalPuzzlesSolved: number;
  totalBattlesPlayed: number;
  totalBattlesWon: number;
  totalExplorationTime: number;
  
  // 分类统计
  puzzleStats: Record<PuzzleType, { solved: number; attempted: number }>;
  difficultyStats: Record<GameDifficulty, { solved: number; attempted: number }>;
  
  // 时间统计
  averageSolveTime: number;
  fastestSolveTime: number;
  longestStreak: number;
  currentStreak: number;
  
  // 连胜
  battleWinStreak: number;
  puzzleSolveStreak: number;
}
