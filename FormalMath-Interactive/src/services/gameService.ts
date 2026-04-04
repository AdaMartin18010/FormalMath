/**
 * FormalMath 游戏化服务
 * 处理游戏逻辑、状态管理和API交互
 */

import type {
  GameSession,
  Puzzle,
  PuzzleType,
  GameDifficulty,
  BattleSession,
  BattleType,
  ExplorationSession,
  ExplorationMode,
  Badge,
  UserBadge,
  Achievement,
  GameReward,
  TutorMessage,
  GuidanceType,
  PuzzleLevel,
  MathWorld,
  HistoryTimeline,
  Leaderboard,
  LevelSystem,
  SkillTree,
  VirtualTutor,
  PersonalizedGuidance,
  LearningRecommendation,
  PlayerAnswer,
  GameStatistics,
  Quest,
  CollectionItem,
} from '../types/gamification';

// ==================== 模拟数据 ====================

const MOCK_PUZZLES: Puzzle[] = [
  {
    id: 'puzzle_001',
    type: 'math_riddle',
    title: '爱因斯坦的谜题',
    description: '五个不同国籍的人住在五栋不同颜色的房子里，他们抽不同品牌的香烟，喝不同的饮料，养不同的宠物。谁养鱼？',
    difficulty: 'expert',
    conceptIds: ['logic', 'set_theory'],
    estimatedTime: 30,
    content: {
      problem: '使用逻辑推理，根据给定的15个条件，确定谁养鱼。',
      variables: {},
      solution: '德国人',
      solutionSteps: [
        '挪威人住第一间房',
        '蓝房子在第二间',
        '绿房子在白房子左边',
        '...',
      ],
      answerType: 'text',
    },
    hints: [
      { id: 'h1', level: 1, content: '先确定房子的颜色和位置关系', cost: 10, used: false },
      { id: 'h2', level: 2, content: '挪威人住在第一间房子', cost: 20, used: false },
    ],
    baseReward: [
      { type: 'xp', amount: 100 },
      { type: 'coin', amount: 50 },
      { type: 'badge', badgeId: 'logic_master' },
    ],
    timeBonus: true,
    createdAt: '2024-01-01',
    playCount: 1250,
    passRate: 0.15,
  },
  {
    id: 'puzzle_002',
    type: 'proof_construct',
    title: '√2是无理数',
    description: '构造一个证明，证明√2不能表示为两个整数的比。',
    difficulty: 'medium',
    conceptIds: ['number_theory', 'proof_by_contradiction'],
    estimatedTime: 15,
    content: {
      theorem: '√2是无理数',
      given: ['假设√2是有理数'],
      goal: '导出矛盾',
      availableSteps: [
        { id: 's1', content: '设√2 = p/q，其中p,q互质', isCorrect: true, explanation: '有理数的定义' },
        { id: 's2', content: '两边平方得2 = p²/q²', isCorrect: true, explanation: '代数运算' },
        { id: 's3', content: '因此p² = 2q²', isCorrect: true, explanation: '整理方程' },
        { id: 's4', content: '所以p²是偶数', isCorrect: true, explanation: '2q²显然是偶数' },
        { id: 's5', content: '因此p是偶数', isCorrect: true, explanation: '奇数的平方是奇数' },
        { id: 's6', content: '设p = 2k', isCorrect: true, explanation: '偶数的表示' },
        { id: 's7', content: '代入得4k² = 2q²，即2k² = q²', isCorrect: true, explanation: '代入化简' },
        { id: 's8', content: '所以q²是偶数，q也是偶数', isCorrect: true, explanation: '同理' },
        { id: 's9', content: 'p和q都是偶数，与互质矛盾', isCorrect: true, explanation: '矛盾！' },
        { id: 'w1', content: '直接得出结论', isCorrect: false, explanation: '缺少关键步骤' },
      ],
      correctSequence: ['s1', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9'],
      partialCredit: true,
    },
    hints: [
      { id: 'h1', level: 1, content: '使用反证法', cost: 5, used: false },
    ],
    baseReward: [
      { type: 'xp', amount: 50 },
      { type: 'coin', amount: 25 },
    ],
    timeBonus: false,
    createdAt: '2024-01-01',
    playCount: 3000,
    passRate: 0.65,
  },
  {
    id: 'puzzle_003',
    type: 'concept_match',
    title: '几何概念连线',
    description: '将几何概念与其定义正确匹配。',
    difficulty: 'easy',
    conceptIds: ['geometry', 'euclidean_geometry'],
    estimatedTime: 5,
    content: {
      concepts: [
        { id: 'c1', content: '平行线', type: 'concept' },
        { id: 'c2', content: '垂直', type: 'concept' },
        { id: 'c3', content: '全等', type: 'concept' },
      ],
      definitions: [
        { id: 'd1', content: '永不相交的直线', type: 'definition' },
        { id: 'd2', content: '夹角为90度', type: 'definition' },
        { id: 'd3', content: '形状和大小完全相同', type: 'definition' },
      ],
      relationships: [],
      pairs: [
        { left: 'c1', right: 'd1' },
        { left: 'c2', right: 'd2' },
        { left: 'c3', right: 'd3' },
      ],
    },
    hints: [
      { id: 'h1', level: 1, content: '想想日常生活中这些概念的例子', cost: 3, used: false },
    ],
    baseReward: [
      { type: 'xp', amount: 20 },
      { type: 'coin', amount: 10 },
    ],
    timeBonus: true,
    createdAt: '2024-01-01',
    playCount: 5000,
    passRate: 0.90,
  },
  {
    id: 'puzzle_004',
    type: 'equation_solve',
    title: '线性方程组',
    description: '解以下线性方程组',
    difficulty: 'medium',
    conceptIds: ['linear_algebra', 'equation_systems'],
    estimatedTime: 10,
    content: {
      equation: '2x + 3y = 12, x - y = 1',
      variables: ['x', 'y'],
      steps: [
        { id: 'step1', description: '从第二个方程得x = y + 1', operation: '代入', result: 'x = y + 1' },
        { id: 'step2', description: '代入第一个方程', operation: '代入', result: '2(y+1) + 3y = 12' },
        { id: 'step3', description: '展开', operation: '化简', result: '2y + 2 + 3y = 12' },
        { id: 'step4', description: '合并同类项', operation: '化简', result: '5y = 10' },
        { id: 'step5', description: '解出y', operation: '求解', result: 'y = 2' },
        { id: 'step6', description: '代回求x', operation: '回代', result: 'x = 3' },
      ],
      finalSolution: { x: 3, y: 2 },
    },
    hints: [
      { id: 'h1', level: 1, content: '使用代入法', cost: 5, used: false },
    ],
    baseReward: [
      { type: 'xp', amount: 40 },
      { type: 'coin', amount: 20 },
    ],
    timeBonus: true,
    createdAt: '2024-01-01',
    playCount: 2500,
    passRate: 0.75,
  },
  {
    id: 'puzzle_005',
    type: 'pattern_recognize',
    title: '斐波那契模式',
    description: '找出数列的规律并预测接下来的数字',
    difficulty: 'easy',
    conceptIds: ['sequences', 'fibonacci'],
    estimatedTime: 3,
    content: {
      sequence: [1, 1, 2, 3, 5, 8, 13],
      pattern: '每个数是前两个数之和',
      nextTerms: [21, 34, 55],
      generalFormula: 'F(n) = F(n-1) + F(n-2)',
    },
    hints: [
      { id: 'h1', level: 1, content: '观察相邻数字的关系', cost: 2, used: false },
    ],
    baseReward: [
      { type: 'xp', amount: 15 },
      { type: 'coin', amount: 8 },
    ],
    timeBonus: true,
    createdAt: '2024-01-01',
    playCount: 8000,
    passRate: 0.95,
  },
];

const MOCK_BADGES: Badge[] = [
  {
    id: 'first_step',
    name: '第一步',
    description: '完成第一个谜题',
    category: 'learning',
    rarity: 'common',
    icon: '🌱',
    unlockCondition: { type: 'puzzle_count', count: 1 },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'logic_master',
    name: '逻辑大师',
    description: '完成一个专家级逻辑谜题',
    category: 'puzzle',
    rarity: 'rare',
    icon: '🧠',
    unlockCondition: { type: 'puzzle_count', count: 1, difficulty: 'expert' },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'speed_demon',
    name: '速度恶魔',
    description: '在30秒内完成一个谜题',
    category: 'puzzle',
    rarity: 'uncommon',
    icon: '⚡',
    unlockCondition: { type: 'special_event', eventId: 'fast_solve' },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'battle_winner',
    name: '对战王者',
    description: '赢得第一场对战',
    category: 'battle',
    rarity: 'uncommon',
    icon: '🏆',
    unlockCondition: { type: 'battle_win', count: 1 },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'explorer',
    name: '探索者',
    description: '解锁数学世界中的一个区域',
    category: 'exploration',
    rarity: 'common',
    icon: '🗺️',
    unlockCondition: { type: 'explore_region', regionId: 'any' },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'collector',
    name: '收藏家',
    description: '收集10个概念卡片',
    category: 'exploration',
    rarity: 'rare',
    icon: '📚',
    unlockCondition: { type: 'collect_items', count: 10 },
    createdAt: '2024-01-01',
    hidden: false,
  },
  {
    id: 'persistent',
    name: '坚持不懈',
    description: '连续7天登录',
    category: 'special',
    rarity: 'epic',
    icon: '💎',
    unlockCondition: { type: 'special_event', eventId: 'weekly_streak' },
    createdAt: '2024-01-01',
    hidden: true,
  },
];

const MOCK_WORLDS: MathWorld[] = [
  {
    id: 'world_algebra',
    name: '代数王国',
    description: '探索方程、多项式和抽象代数的奥秘',
    theme: 'blue',
    regions: [
      {
        id: 'region_linear',
        name: '线性方程平原',
        description: '一次方程的领地',
        type: 'domain',
        position: { x: 100, y: 100 },
        conceptIds: ['linear_equation', 'slope'],
        puzzles: ['puzzle_004'],
        isLocked: false,
        isVisited: false,
        isCompleted: false,
      },
      {
        id: 'region_quadratic',
        name: '二次方程山脉',
        description: '抛物线的故乡',
        type: 'domain',
        position: { x: 250, y: 150 },
        conceptIds: ['quadratic_equation', 'parabola'],
        puzzles: [],
        isLocked: true,
        isVisited: false,
        isCompleted: false,
      },
    ],
    connections: [
      { from: 'region_linear', to: 'region_quadratic', type: 'path' },
    ],
    unlockCriteria: {},
    completionRewards: [
      { type: 'xp', amount: 500 },
      { type: 'badge', badgeId: 'algebra_master' },
    ],
  },
];

const MOCK_TUTOR: VirtualTutor = {
  id: 'tutor_default',
  name: 'MathGuide',
  avatar: '🤖',
  personality: 'friendly',
  capabilities: [
    { type: 'hint', level: 5, enabled: true },
    { type: 'explanation', level: 5, enabled: true },
    { type: 'feedback', level: 5, enabled: true },
    { type: 'motivation', level: 5, enabled: true },
    { type: 'challenge', level: 3, enabled: true },
  ],
  isActive: true,
};

// ==================== 游戏服务类 ====================

class GameService {
  private static instance: GameService;
  private userId: string = 'user_001';

  private constructor() {}

  static getInstance(): GameService {
    if (!GameService.instance) {
      GameService.instance = new GameService();
    }
    return GameService.instance;
  }

  // ==================== 谜题服务 ====================

  async getPuzzles(
    filters?: {
      type?: PuzzleType;
      difficulty?: GameDifficulty;
      conceptId?: string;
    }
  ): Promise<Puzzle[]> {
    let puzzles = [...MOCK_PUZZLES];

    if (filters?.type) {
      puzzles = puzzles.filter((p) => p.type === filters.type);
    }
    if (filters?.difficulty) {
      puzzles = puzzles.filter((p) => p.difficulty === filters.difficulty);
    }
    if (filters?.conceptId) {
      puzzles = puzzles.filter((p) => p.conceptIds.includes(filters.conceptId!));
    }

    return puzzles;
  }

  async getPuzzleById(id: string): Promise<Puzzle | null> {
    return MOCK_PUZZLES.find((p) => p.id === id) || null;
  }

  async getPuzzleLevels(): Promise<PuzzleLevel[]> {
    return [
      {
        id: 'level_1',
        name: '初学者之路',
        description: '适合数学新手的基础谜题',
        puzzles: ['puzzle_003', 'puzzle_005'],
        requiredScore: 0,
        unlockCriteria: {},
        rewards: [{ type: 'xp', amount: 100 }],
      },
      {
        id: 'level_2',
        name: '进阶挑战',
        description: '需要一定数学基础的谜题',
        puzzles: ['puzzle_002', 'puzzle_004'],
        requiredScore: 50,
        unlockCriteria: { completedPuzzles: ['puzzle_003', 'puzzle_005'] },
        rewards: [{ type: 'xp', amount: 200 }],
      },
      {
        id: 'level_3',
        name: '大师试炼',
        description: '只有真正的数学大师才能解开',
        puzzles: ['puzzle_001'],
        requiredScore: 150,
        unlockCriteria: { completedPuzzles: ['puzzle_002', 'puzzle_004'] },
        rewards: [{ type: 'badge', badgeId: 'logic_master' }],
      },
    ];
  }

  async submitPuzzleAnswer(
    puzzleId: string,
    answer: unknown,
    timeSpent: number,
    hintsUsed: number
  ): Promise<{
    correct: boolean;
    score: number;
    rewards: GameReward[];
    feedback: string;
  }> {
    const puzzle = await this.getPuzzleById(puzzleId);
    if (!puzzle) {
      throw new Error('Puzzle not found');
    }

    // 验证答案
    let correct = false;
    let feedback = '';

    switch (puzzle.type) {
      case 'math_riddle':
        correct = this.validateMathRiddle(puzzle, answer);
        feedback = correct ? '解答正确！逻辑推理完美！' : '答案不正确，再检查一下逻辑链。';
        break;
      case 'proof_construct':
        correct = this.validateProofConstruct(puzzle, answer as string[]);
        feedback = correct ? '证明完整且严谨！' : '证明步骤有误，请检查推导过程。';
        break;
      case 'concept_match':
        correct = this.validateConceptMatch(puzzle, answer as Record<string, string>);
        feedback = correct ? '所有匹配正确！' : '有些匹配不正确，再想想概念之间的关系。';
        break;
      case 'equation_solve':
        correct = this.validateEquationSolve(puzzle, answer as Record<string, number>);
        feedback = correct ? '方程求解正确！' : '解不正确，检查一下计算过程。';
        break;
      case 'pattern_recognize':
        correct = this.validatePatternRecognize(puzzle, answer as (number | string)[]);
        feedback = correct ? '模式识别正确！' : '规律找错了，再观察一下数列。';
        break;
    }

    // 计算分数
    let score = 0;
    if (correct) {
      score = this.calculateScore(puzzle.difficulty, timeSpent, hintsUsed);
    }

    // 计算奖励
    const rewards = correct ? this.calculateRewards(puzzle, score, timeSpent) : [];

    return { correct, score, rewards, feedback };
  }

  private validateMathRiddle(puzzle: Puzzle, answer: unknown): boolean {
    const content = puzzle.content as { solution: string | number };
    return String(answer).toLowerCase().trim() === String(content.solution).toLowerCase().trim();
  }

  private validateProofConstruct(puzzle: Puzzle, answer: string[]): boolean {
    const content = puzzle.content as { correctSequence: string[] };
    return JSON.stringify(answer) === JSON.stringify(content.correctSequence);
  }

  private validateConceptMatch(puzzle: Puzzle, answer: Record<string, string>): boolean {
    const content = puzzle.content as { pairs: { left: string; right: string }[] };
    return content.pairs.every((pair) => answer[pair.left] === pair.right);
  }

  private validateEquationSolve(puzzle: Puzzle, answer: Record<string, number>): boolean {
    const content = puzzle.content as { finalSolution: Record<string, number> };
    return Object.entries(content.finalSolution).every(
      ([key, value]) => Math.abs((answer[key] || 0) - value) < 0.001
    );
  }

  private validatePatternRecognize(puzzle: Puzzle, answer: (number | string)[]): boolean {
    const content = puzzle.content as { nextTerms: (number | string)[] };
    return answer.every((term, index) => term === content.nextTerms[index]);
  }

  private calculateScore(
    difficulty: GameDifficulty,
    timeSpent: number,
    hintsUsed: number
  ): number {
    const baseScores: Record<GameDifficulty, number> = {
      easy: 20,
      medium: 40,
      hard: 80,
      expert: 150,
    };

    let score = baseScores[difficulty];

    // 时间奖励
    if (timeSpent < 60) {
      score += Math.floor((60 - timeSpent) / 10);
    }

    // 提示惩罚
    score -= hintsUsed * 5;

    return Math.max(0, score);
  }

  private calculateRewards(puzzle: Puzzle, score: number, timeSpent: number): GameReward[] {
    const rewards: GameReward[] = [...puzzle.baseReward];

    // 时间奖励
    if (puzzle.timeBonus && timeSpent < puzzle.estimatedTime * 60 * 0.5) {
      rewards.push({ type: 'coin', amount: 10 });
    }

    return rewards;
  }

  // ==================== 对战服务 ====================

  async createBattle(
    type: BattleType,
    settings: BattleSession['settings']
  ): Promise<BattleSession> {
    const battle: BattleSession = {
      id: `battle_${Date.now()}`,
      type,
      status: 'waiting',
      createdAt: new Date().toISOString(),
      host: {
        userId: this.userId,
        name: '玩家',
        level: 5,
        rating: 1000,
        ready: false,
        connected: true,
      },
      settings,
      currentRound: 0,
      totalRounds: settings.questionCount,
      rounds: [],
      finalScores: {},
    };

    return battle;
  }

  async joinBattle(battleId: string): Promise<BattleSession> {
    // 模拟加入对战
    return {
      id: battleId,
      type: 'speed_challenge',
      status: 'starting',
      createdAt: new Date().toISOString(),
      host: {
        userId: 'host_001',
        name: '对手',
        level: 6,
        rating: 1100,
        ready: true,
        connected: true,
      },
      opponent: {
        userId: this.userId,
        name: '玩家',
        level: 5,
        rating: 1000,
        ready: true,
        connected: true,
      },
      settings: {
        difficulty: 'medium',
        timePerQuestion: 30,
        questionCount: 5,
        allowHelpers: false,
        isPrivate: false,
      },
      currentRound: 1,
      totalRounds: 5,
      rounds: [],
      finalScores: {},
    };
  }

  async submitBattleAnswer(
    battleId: string,
    roundNumber: number,
    answer: PlayerAnswer
  ): Promise<{
    correct: boolean;
    roundScore: number;
    opponentAnswer?: PlayerAnswer;
  }> {
    // 模拟对战结果
    return {
      correct: answer.isCorrect,
      roundScore: answer.score,
      opponentAnswer: {
        userId: 'opponent',
        answer: 'test',
        submittedAt: new Date().toISOString(),
        timeSpent: answer.timeSpent + 2,
        isCorrect: Math.random() > 0.3,
        score: Math.floor(Math.random() * 100),
        hintsUsed: 0,
      },
    };
  }

  // ==================== 探索服务 ====================

  async getMathWorlds(): Promise<MathWorld[]> {
    return MOCK_WORLDS;
  }

  async getHistoryTimeline(): Promise<HistoryTimeline> {
    return {
      id: 'timeline_math',
      name: '数学史时间线',
      description: '从古希腊到现代数学的发展历程',
      timeRange: { start: -600, end: 2000 },
      eras: [
        { id: 'era_ancient', name: '古代数学', period: { start: -600, end: 500 }, description: '希腊、埃及、巴比伦数学', color: '#8B4513' },
        { id: 'era_medieval', name: '中世纪数学', period: { start: 500, end: 1500 }, description: '阿拉伯数学、印度数学', color: '#4682B4' },
        { id: 'era_modern', name: '近代数学', period: { start: 1500, end: 1900 }, description: '微积分、分析学', color: '#228B22' },
        { id: 'era_contemporary', name: '现代数学', period: { start: 1900, end: 2000 }, description: '抽象代数、拓扑学', color: '#9370DB' },
      ],
      events: [
        {
          id: 'event_pythagoras',
          title: '毕达哥拉斯定理',
          description: '发现直角三角形三边关系',
          date: -530,
          eraId: 'era_ancient',
          conceptIds: ['pythagorean_theorem'],
          mathematicianIds: ['pythagoras'],
          theoremIds: ['theorem_pythagorean'],
          isUnlocked: true,
          isVisited: false,
          rewardsClaimed: false,
        },
        {
          id: 'event_euclid',
          title: '《几何原本》',
          description: '欧几里得出版几何学巨著',
          date: -300,
          eraId: 'era_ancient',
          conceptIds: ['euclidean_geometry'],
          mathematicianIds: ['euclid'],
          theoremIds: [],
          isUnlocked: true,
          isVisited: false,
          rewardsClaimed: false,
        },
      ],
    };
  }

  async startExploration(mode: ExplorationMode, worldId?: string): Promise<ExplorationSession> {
    return {
      id: `explore_${Date.now()}`,
      userId: this.userId,
      mode,
      startedAt: new Date().toISOString(),
      currentPosition: { nodeId: worldId || 'start', x: 0, y: 0 },
      visitedNodes: [],
      unlockedNodes: [worldId || 'start'],
      collectedItems: [],
      progress: {
        totalNodes: 10,
        visitedCount: 0,
        unlockedCount: 1,
        completionRate: 0,
      },
    };
  }

  async exploreNode(sessionId: string, nodeId: string): Promise<{
    session: ExplorationSession;
    discovered: string[];
    rewards: GameReward[];
    quests: Quest[];
  }> {
    // 模拟探索节点
    return {
      session: {
        id: sessionId,
        userId: this.userId,
        mode: 'world',
        startedAt: new Date().toISOString(),
        currentPosition: { nodeId, x: 100, y: 100 },
        visitedNodes: [nodeId],
        unlockedNodes: ['start', nodeId],
        collectedItems: [],
        progress: {
          totalNodes: 10,
          visitedCount: 1,
          unlockedCount: 2,
          completionRate: 10,
        },
      },
      discovered: ['region_quadratic'],
      rewards: [{ type: 'xp', amount: 30 }],
      quests: [],
    };
  }

  // ==================== 成就服务 ====================

  async getBadges(): Promise<Badge[]> {
    return MOCK_BADGES;
  }

  async getUserBadges(userId: string): Promise<UserBadge[]> {
    // 模拟用户已获得的徽章
    return [
      { badgeId: 'first_step', earnedAt: '2024-01-01', progress: 100, isNew: false },
      { badgeId: 'speed_demon', earnedAt: '2024-01-02', progress: 100, isNew: true },
    ];
  }

  async getAchievements(userId: string): Promise<Achievement[]> {
    return [
      {
        id: 'ach_puzzles',
        userId,
        type: 'puzzle_count',
        title: '谜题猎人',
        description: '完成50个谜题',
        targetValue: 50,
        currentValue: 23,
        isCompleted: false,
        reward: [{ type: 'xp', amount: 500 }],
      },
      {
        id: 'ach_streak',
        userId,
        type: 'daily_streak',
        title: '每日学习者',
        description: '连续学习7天',
        targetValue: 7,
        currentValue: 7,
        isCompleted: true,
        completedAt: '2024-01-07',
        reward: [{ type: 'badge', badgeId: 'persistent' }],
      },
    ];
  }

  async checkBadgeUnlock(userId: string, action: string, data: unknown): Promise<Badge[]> {
    // 模拟检查徽章解锁
    const unlocked: Badge[] = [];
    
    if (action === 'puzzle_complete' && (data as { count: number }).count === 1) {
      const badge = MOCK_BADGES.find((b) => b.id === 'first_step');
      if (badge) unlocked.push(badge);
    }
    
    return unlocked;
  }

  async getLeaderboard(
    type: Leaderboard['type'],
    category: Leaderboard['category']
  ): Promise<Leaderboard> {
    return {
      id: `lb_${type}_${category}`,
      name: `${type} - ${category}`,
      type,
      category,
      entries: [
        { rank: 1, userId: 'u1', name: '数学大师', score: 9999, level: 50, trend: 'stable', isCurrentUser: false },
        { rank: 2, userId: 'u2', name: '逻辑之王', score: 8500, level: 45, trend: 'up', isCurrentUser: false },
        { rank: 3, userId: 'u3', name: '证明专家', score: 7200, level: 40, trend: 'down', isCurrentUser: false },
        { rank: 10, userId: this.userId, name: '玩家', score: 3500, level: 15, trend: 'up', isCurrentUser: true },
      ],
      userRank: 10,
      userEntry: { rank: 10, userId: this.userId, name: '玩家', score: 3500, level: 15, trend: 'up', isCurrentUser: true },
    };
  }

  async getSkillTree(): Promise<SkillTree> {
    return {
      id: 'skill_tree_main',
      name: '数学技能树',
      description: '解锁各种数学能力',
      branches: [
        {
          id: 'branch_logic',
          name: '逻辑推理',
          color: '#3B82F6',
          skills: [
            {
              id: 'skill_logic_1',
              name: '基础逻辑',
              description: '获得5%的谜题经验加成',
              icon: '🧩',
              level: 1,
              maxLevel: 5,
              effects: [{ type: 'xp_boost', value: 0.05, description: '谜题经验+5%' }],
              prerequisites: [],
              unlockCost: { type: 'xp', amount: 100 },
              isUnlocked: true,
              currentLevel: 1,
            },
            {
              id: 'skill_logic_2',
              name: '快速思考',
              description: '解谜时间限制增加10秒',
              icon: '⚡',
              level: 1,
              maxLevel: 3,
              effects: [{ type: 'time_bonus', value: 10, description: '时间+10秒' }],
              prerequisites: ['skill_logic_1'],
              unlockCost: { type: 'xp', amount: 200 },
              isUnlocked: false,
              currentLevel: 0,
            },
          ],
        },
        {
          id: 'branch_collection',
          name: '收集专家',
          color: '#10B981',
          skills: [
            {
              id: 'skill_collect_1',
              name: '鹰眼',
              description: '发现隐藏概念的概率+10%',
              icon: '👁️',
              level: 1,
              maxLevel: 5,
              effects: [{ type: 'unlock_content', value: 0.1, description: '发现率+10%' }],
              prerequisites: [],
              unlockCost: { type: 'xp', amount: 150 },
              isUnlocked: true,
              currentLevel: 1,
            },
          ],
        },
      ],
    };
  }

  async unlockSkill(skillId: string): Promise<boolean> {
    // 模拟解锁技能
    return true;
  }

  async upgradeSkill(skillId: string): Promise<boolean> {
    // 模拟升级技能
    return true;
  }

  // ==================== 等级系统 ====================

  async getLevelSystem(userId: string): Promise<LevelSystem> {
    return {
      currentLevel: 15,
      currentXP: 3500,
      xpToNextLevel: 4500,
      totalXP: 25000,
      levelTitle: '数学学徒',
      levelIcon: '📚',
      unlockedFeatures: ['battle_mode', 'exploration', 'skill_tree'],
    };
  }

  async addXP(userId: string, amount: number): Promise<{
    newLevel: boolean;
    levelUp?: { oldLevel: number; newLevel: number; rewards: GameReward[] };
  }> {
    // 模拟添加经验
    return { newLevel: false };
  }

  // ==================== 导师服务 ====================

  async getVirtualTutor(): Promise<VirtualTutor> {
    return MOCK_TUTOR;
  }

  async getTutorMessage(
    type: GuidanceType,
    context: {
      puzzleId?: string;
      conceptId?: string;
      strugglePoints?: string[];
      lastAction?: string;
    }
  ): Promise<TutorMessage> {
    const messages: Record<GuidanceType, string[]> = {
      hint: [
        '试着从已知条件出发，看看能推导出什么。',
        '这个问题可以用反证法来解决。',
        '注意观察题目中的对称性。',
      ],
      explanation: [
        '这个概念的核心思想是...',
        '让我用一个简单的例子来说明...',
        '这其实是某个更普遍定理的特例。',
      ],
      feedback: [
        '很好的尝试！但还有改进空间。',
        '思路正确，继续加油！',
        '完美！你掌握了这个技巧。',
      ],
      motivation: [
        '相信自己，你能做到的！',
        '每个数学家都曾经历过困难。',
        '进步是一点一滴积累的。',
      ],
      challenge: [
        '试试不用提示解决这个问题？',
        '你能找到更优雅的证明吗？',
        '尝试用不同的方法来解决。',
      ],
    };

    const typeMessages = messages[type];
    const randomMessage = typeMessages[Math.floor(Math.random() * typeMessages.length)];

    return {
      id: `msg_${Date.now()}`,
      type,
      content: randomMessage,
      timestamp: new Date().toISOString(),
      relatedPuzzleId: context.puzzleId,
      relatedConceptId: context.conceptId,
    };
  }

  async getPersonalizedGuidance(userId: string): Promise<PersonalizedGuidance> {
    return {
      userId,
      learningStyle: 'visual',
      difficultyPreference: 'medium',
      interestAreas: ['algebra', 'geometry', 'number_theory'],
      hintFrequency: 'medium',
      encouragementLevel: 'high',
      challengePreference: 'balanced',
    };
  }

  async getLearningRecommendations(userId: string): Promise<LearningRecommendation[]> {
    return [
      {
        id: 'rec_1',
        type: 'next_puzzle',
        title: '继续挑战',
        description: '基于你的进度，推荐尝试下一个难度适中的证明题',
        reason: '你最近完成了3个方程求解题，证明能力有待提升',
        targetId: 'puzzle_002',
        priority: 1,
        estimatedTime: 15,
      },
      {
        id: 'rec_2',
        type: 'review_concept',
        title: '温故知新',
        description: '复习二次函数的概念',
        reason: '距离上次学习这个内容已经一周了',
        targetId: 'concept_quadratic',
        priority: 2,
        estimatedTime: 10,
      },
    ];
  }

  // ==================== 收集系统 ====================

  async getCollectionItems(userId: string): Promise<CollectionItem[]> {
    return [
      {
        id: 'collect_pi',
        conceptId: 'pi',
        name: '圆周率π',
        description: '圆的周长与直径之比',
        rarity: 'common',
        unlockCondition: '完成几何基础课程',
        isUnlocked: true,
        unlockedAt: '2024-01-01',
        funFact: 'π的小数位数已被计算到数万亿位',
        relatedConcepts: ['circle', 'circumference'],
      },
      {
        id: 'collect_golden',
        conceptId: 'golden_ratio',
        name: '黄金分割',
        description: '最美的比例',
        rarity: 'rare',
        unlockCondition: '完成美学与数学专题',
        isUnlocked: false,
        relatedConcepts: ['ratio', 'fibonacci'],
      },
    ];
  }

  async collectItem(userId: string, itemId: string): Promise<{
    success: boolean;
    item?: CollectionItem;
    isNew: boolean;
  }> {
    // 模拟收集物品
    return { success: true, isNew: true };
  }

  // ==================== 统计服务 ====================

  async getGameStatistics(userId: string): Promise<GameStatistics> {
    return {
      totalPuzzlesSolved: 45,
      totalBattlesPlayed: 12,
      totalBattlesWon: 8,
      totalExplorationTime: 3600,
      puzzleStats: {
        math_riddle: { solved: 10, attempted: 15 },
        proof_construct: { solved: 8, attempted: 12 },
        concept_match: { solved: 15, attempted: 15 },
        equation_solve: { solved: 12, attempted: 14 },
        pattern_recognize: { solved: 0, attempted: 0 },
        logic_deduction: { solved: 0, attempted: 0 },
      },
      difficultyStats: {
        easy: { solved: 20, attempted: 22 },
        medium: { solved: 18, attempted: 20 },
        hard: { solved: 7, attempted: 12 },
        expert: { solved: 0, attempted: 2 },
      },
      averageSolveTime: 180,
      fastestSolveTime: 25,
      longestStreak: 15,
      currentStreak: 5,
      battleWinStreak: 3,
      puzzleSolveStreak: 5,
    };
  }

  // ==================== 工具方法 ====================

  generateSessionId(): string {
    return `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }

  formatTime(seconds: number): string {
    const mins = Math.floor(seconds / 60);
    const secs = seconds % 60;
    return `${mins}:${secs.toString().padStart(2, '0')}`;
  }

  calculateLevelTitle(level: number): string {
    const titles = [
      { min: 1, max: 5, title: '数学新手' },
      { min: 6, max: 15, title: '数学学徒' },
      { min: 16, max: 30, title: '数学爱好者' },
      { min: 31, max: 50, title: '数学达人' },
      { min: 51, max: 75, title: '数学专家' },
      { min: 76, max: 100, title: '数学大师' },
    ];
    
    const title = titles.find((t) => level >= t.min && level <= t.max);
    return title?.title || '数学传奇';
  }
}

export const gameService = GameService.getInstance();
export default gameService;
