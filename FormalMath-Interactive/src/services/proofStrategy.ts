/**
 * 证明策略推荐引擎
 * Proof Strategy Recommendation Engine
 */

import type {
  ProofState,
  ProofGoal,
  Tactic,
  TacticSuggestion,
  TacticCategory,
  ProofStrategy,
  ApplicabilityScore,
  Difficulty,
  TacticParameter,
} from '../types/proofAssistant';

// 内置策略库
const BUILTIN_TACTICS: Tactic[] = [
  // ==== 引入规则 ====
  {
    id: 'intro',
    name: 'intro',
    category: 'introduction',
    description: '引入蕴含或全称量词',
    syntax: 'intro [name]',
    examples: ['intro h', 'intro x y z'],
    difficulty: 'easy',
    parameters: [
      { name: 'names', type: 'list', description: '引入的变量名列表', required: false, defaultValue: '' }
    ]
  },
  {
    id: 'intros',
    name: 'intros',
    category: 'introduction',
    description: '引入多个假设',
    syntax: 'intros [names...]',
    examples: ['intros', 'intros h1 h2 h3'],
    difficulty: 'easy',
  },
  {
    id: 'constructor',
    name: 'constructor',
    category: 'introduction',
    description: '分解合取目标',
    syntax: 'constructor',
    examples: ['constructor'],
    difficulty: 'easy',
  },
  {
    id: 'split',
    name: 'split',
    category: 'introduction',
    description: '分解合取目标（constructor 的别名）',
    syntax: 'split',
    examples: ['split'],
    difficulty: 'easy',
  },
  {
    id: 'left',
    name: 'left',
    category: 'introduction',
    description: '选择析取的左分支',
    syntax: 'left',
    examples: ['left'],
    difficulty: 'easy',
  },
  {
    id: 'right',
    name: 'right',
    category: 'introduction',
    description: '选择析取的右分支',
    syntax: 'right',
    examples: ['right'],
    difficulty: 'easy',
  },
  {
    id: 'exists',
    name: 'exists',
    category: 'introduction',
    description: '为存在量词提供证据',
    syntax: 'exists <term>',
    examples: ['exists 0', 'exists (x + y)'],
    difficulty: 'medium',
    parameters: [
      { name: 'witness', type: 'expression', description: '存在量词的见证', required: true }
    ]
  },
  
  // ==== 消去规则 ====
  {
    id: 'apply',
    name: 'apply',
    category: 'elimination',
    description: '应用定理或假设匹配目标',
    syntax: 'apply <theorem>',
    examples: ['apply h', 'apply Nat.add_comm'],
    difficulty: 'medium',
    parameters: [
      { name: 'theorem', type: 'expression', description: '要应用的定理', required: true }
    ]
  },
  {
    id: 'exact',
    name: 'exact',
    category: 'elimination',
    description: '直接提供目标的确切证明',
    syntax: 'exact <term>',
    examples: ['exact h', 'exact rfl'],
    difficulty: 'easy',
    parameters: [
      { name: 'proof', type: 'expression', description: '目标的证明', required: true }
    ]
  },
  {
    id: 'refine',
    name: 'refine',
    category: 'elimination',
    description: '应用定理但留下占位符',
    syntax: 'refine <theorem>',
    examples: ['refine ⟨?_, ?_⟩'],
    difficulty: 'medium',
  },
  {
    id: 'cases',
    name: 'cases',
    category: 'elimination',
    description: '对归纳类型进行案例分析',
    syntax: 'cases <expression>',
    examples: ['cases n', 'cases h with | inl h1 => ... | inr h2 => ...'],
    difficulty: 'medium',
    parameters: [
      { name: 'expression', type: 'expression', description: '要分析的表达式', required: true }
    ]
  },
  {
    id: 'destruct',
    name: 'destruct',
    category: 'elimination',
    description: '解构假设',
    syntax: 'destruct <hypothesis>',
    examples: ['destruct h'],
    difficulty: 'medium',
  },
  
  // ==== 重写规则 ====
  {
    id: 'rw',
    name: 'rw',
    category: 'rewriting',
    description: '使用等式重写',
    syntax: 'rw [<rules...>] [at <location>]',
    examples: ['rw [add_comm]', 'rw [h] at h2', 'rw [← Nat.zero_add]'],
    difficulty: 'medium',
    parameters: [
      { name: 'rules', type: 'list', description: '重写规则列表', required: true },
      { name: 'location', type: 'identifier', description: '重写的位置', required: false }
    ]
  },
  {
    id: 'rewrite',
    name: 'rewrite',
    category: 'rewriting',
    description: 'rw 的别名',
    syntax: 'rewrite [<rules...>]',
    examples: ['rewrite [add_comm]'],
    difficulty: 'medium',
  },
  {
    id: 'simp',
    name: 'simp',
    category: 'rewriting',
    description: '简化表达式',
    syntax: 'simp [<rules...>] [at <location>]',
    examples: ['simp', 'simp [add_zero, mul_one]', 'simp only [h]'],
    difficulty: 'easy',
    parameters: [
      { name: 'rules', type: 'list', description: '简化规则', required: false },
      { name: 'only', type: 'string', description: '仅使用指定规则', required: false }
    ]
  },
  {
    id: 'simp_all',
    name: 'simp_all',
    category: 'rewriting',
    description: '简化所有假设和目标',
    syntax: 'simp_all',
    examples: ['simp_all', 'simp_all [h1, h2]'],
    difficulty: 'easy',
  },
  
  // ==== 归纳法 ====
  {
    id: 'induction',
    name: 'induction',
    category: 'induction',
    description: '对变量进行归纳',
    syntax: 'induction <variable> [with ...]',
    examples: ['induction n', 'induction n with | zero => ... | succ n ih => ...'],
    difficulty: 'medium',
    parameters: [
      { name: 'variable', type: 'identifier', description: '要归纳的变量', required: true }
    ]
  },
  {
    id: 'induction\'',
    name: 'induction\'',
    category: 'induction',
    description: '使用自定义归纳原理',
    syntax: "induction' <variable>",
    examples: ["induction' n"],
    difficulty: 'hard',
  },
  
  // ==== 算术 ====
  {
    id: 'linarith',
    name: 'linarith',
    category: 'arithmetic',
    description: '线性算术求解器',
    syntax: 'linarith',
    examples: ['linarith', 'linarith [h1, h2]'],
    difficulty: 'easy',
    parameters: [
      { name: 'hints', type: 'list', description: '额外的提示', required: false }
    ]
  },
  {
    id: 'nlinarith',
    name: 'nlinarith',
    category: 'arithmetic',
    description: '非线性算术求解器',
    syntax: 'nlinarith',
    examples: ['nlinarith', 'nlinarith [sq_nonneg x]'],
    difficulty: 'medium',
  },
  {
    id: 'omega',
    name: 'omega',
    category: 'arithmetic',
    description: 'Presburger 算术求解器',
    syntax: 'omega',
    examples: ['omega'],
    difficulty: 'easy',
  },
  {
    id: 'ring',
    name: 'ring',
    category: 'arithmetic',
    description: '环论简化',
    syntax: 'ring',
    examples: ['ring', 'ring_nf'],
    difficulty: 'easy',
  },
  {
    id: 'field',
    name: 'field',
    category: 'arithmetic',
    description: '域论简化',
    syntax: 'field',
    examples: ['field', 'field_simp'],
    difficulty: 'easy',
  },
  {
    id: 'norm_num',
    name: 'norm_num',
    category: 'arithmetic',
    description: '数值归一化',
    syntax: 'norm_num',
    examples: ['norm_num', 'norm_num at h'],
    difficulty: 'easy',
  },
  
  // ==== 等式 ====
  {
    id: 'rfl',
    name: 'rfl',
    category: 'equality',
    description: '自反性证明',
    syntax: 'rfl',
    examples: ['rfl', 'exact rfl'],
    difficulty: 'easy',
  },
  {
    id: 'symm',
    name: 'symm',
    category: 'equality',
    description: '应用对称性',
    syntax: 'symm',
    examples: ['symm', 'apply symm'],
    difficulty: 'easy',
  },
  {
    id: 'trans',
    name: 'trans',
    category: 'equality',
    description: '传递性',
    syntax: 'trans <middle>',
    examples: ['trans y'],
    difficulty: 'medium',
  },
  {
    id: 'calc',
    name: 'calc',
    category: 'equality',
    description: '计算式等式链',
    syntax: 'calc <expr> = <expr> := <proof> ...',
    examples: ['calc x = y := h1 _ = z := h2'],
    difficulty: 'medium',
  },
  
  // ==== 自动化 ====
  {
    id: 'tauto',
    name: 'tauto',
    category: 'automation',
    description: '命题逻辑自动求解',
    syntax: 'tauto',
    examples: ['tauto'],
    difficulty: 'easy',
  },
  {
    id: 'itauto',
    name: 'itauto',
    category: 'automation',
    description: '直觉主义命题逻辑求解',
    syntax: 'itauto',
    examples: ['itauto'],
    difficulty: 'easy',
  },
  {
    id: 'aesop',
    name: 'aesop',
    category: 'automation',
    description: '可扩展的自动化证明搜索',
    syntax: 'aesop',
    examples: ['aesop', 'aesop (config := { maxRuleApplications := 100 })'],
    difficulty: 'medium',
  },
  {
    id: 'smt',
    name: 'smt',
    category: 'automation',
    description: 'SMT 求解器接口',
    syntax: 'smt [<lemmas...>]',
    examples: ['smt'],
    difficulty: 'medium',
  },
  
  // ==== 逻辑 ====
  {
    id: 'by_contra',
    name: 'by_contra',
    category: 'logic',
    description: '反证法',
    syntax: 'by_contra [name]',
    examples: ['by_contra', 'by_contra h'],
    difficulty: 'medium',
  },
  {
    id: 'by_cases',
    name: 'by_cases',
    category: 'logic',
    description: '分情况讨论',
    syntax: 'by_cases <condition> [with <name>]',
    examples: ['by_cases x = 0', 'by_cases x ≤ y with h'],
    difficulty: 'medium',
  },
  {
    id: 'contradiction',
    name: 'contradiction',
    category: 'logic',
    description: '寻找矛盾',
    syntax: 'contradiction',
    examples: ['contradiction'],
    difficulty: 'easy',
  },
  {
    id: 'exfalso',
    name: 'exfalso',
    category: 'logic',
    description: '转换为证明假',
    syntax: 'exfalso',
    examples: ['exfalso'],
    difficulty: 'easy',
  },
];

// 预定义策略模板
const PROOF_STRATEGIES: ProofStrategy[] = [
  {
    id: 'direct',
    name: '直接证明',
    description: '直接构造证明，适用于简单的蕴含和全称量词',
    applicableGoals: ['→', '∀', '∧'],
    tactics: ['intro', 'intros', 'exact', 'apply'],
    estimatedSteps: 3,
    difficulty: 'easy'
  },
  {
    id: 'induction_nat',
    name: '自然数归纳',
    description: '对自然数进行归纳证明',
    applicableGoals: ['∀ (n : ℕ)'],
    tactics: ['induction', 'intros', 'simp', 'rw', 'linarith'],
    estimatedSteps: 8,
    difficulty: 'medium'
  },
  {
    id: 'case_analysis',
    name: '案例分析',
    description: '根据构造子进行案例分析',
    applicableGoals: ['∨', '∃', 'inductive'],
    tactics: ['cases', 'left', 'right', 'exists', 'exact'],
    estimatedSteps: 5,
    difficulty: 'medium'
  },
  {
    id: 'algebraic',
    name: '代数简化',
    description: '使用代数规则简化表达式',
    applicableGoals: ['=', '≤', '<'],
    tactics: ['ring', 'field', 'simp', 'rw', 'calc'],
    estimatedSteps: 4,
    difficulty: 'easy'
  },
  {
    id: 'contradiction',
    name: '反证法',
    description: '假设结论不成立导出矛盾',
    applicableGoals: ['¬', '¬∃', '∀'],
    tactics: ['by_contra', 'push_neg', 'simp', 'contradiction'],
    estimatedSteps: 6,
    difficulty: 'medium'
  }
];

export class ProofStrategyEngine {
  private tactics: Map<string, Tactic> = new Map();
  private strategies: Map<string, ProofStrategy> = new Map();
  private usageHistory: Map<string, number> = new Map();
  private successHistory: Map<string, number> = new Map();

  constructor() {
    this.initializeTactics();
    this.initializeStrategies();
  }

  private initializeTactics() {
    BUILTIN_TACTICS.forEach(tactic => {
      this.tactics.set(tactic.id, tactic);
    });
  }

  private initializeStrategies() {
    PROOF_STRATEGIES.forEach(strategy => {
      this.strategies.set(strategy.id, strategy);
    });
  }

  /**
   * 获取所有策略
   */
  getAllTactics(): Tactic[] {
    return Array.from(this.tactics.values());
  }

  /**
   * 按类别获取策略
   */
  getTacticsByCategory(category: TacticCategory): Tactic[] {
    return this.getAllTactics().filter(t => t.category === category);
  }

  /**
   * 搜索策略
   */
  searchTactics(query: string): Tactic[] {
    const lowerQuery = query.toLowerCase();
    return this.getAllTactics().filter(t => 
      t.name.toLowerCase().includes(lowerQuery) ||
      t.description.toLowerCase().includes(lowerQuery) ||
      t.category.toLowerCase().includes(lowerQuery)
    );
  }

  /**
   * 获取策略建议
   */
  getSuggestions(proofState: ProofState): TacticSuggestion[] {
    const suggestions: TacticSuggestion[] = [];
    const currentGoal = proofState.goals.find(g => g.id === proofState.currentGoalId);
    
    if (!currentGoal) return suggestions;

    // 分析目标结构
    const goalPattern = this.analyzeGoalPattern(currentGoal);
    
    // 分析上下文
    const contextPatterns = this.analyzeContext(proofState.context);
    
    // 评估每个策略的适用性
    for (const tactic of this.tactics.values()) {
      const score = this.calculateApplicability(tactic, goalPattern, contextPatterns, proofState);
      
      if (score.overall > 0.3) { // 只返回得分较高的建议
        suggestions.push({
          tactic,
          confidence: score.overall,
          reason: this.generateReason(tactic, goalPattern, score),
          applicability: score,
          preview: this.generatePreview(tactic, currentGoal)
        });
      }
    }

    // 按置信度排序
    suggestions.sort((a, b) => b.confidence - a.confidence);
    
    return suggestions.slice(0, 8); // 返回前8个建议
  }

  /**
   * 分析目标模式
   */
  private analyzeGoalPattern(goal: ProofGoal): GoalPattern {
    const conclusion = goal.conclusion;
    
    return {
      hasImplication: conclusion.includes('→') || conclusion.includes('->'),
      hasForall: conclusion.includes('∀') || conclusion.includes('forall'),
      hasExists: conclusion.includes('∃') || conclusion.includes('exists'),
      hasConjunction: conclusion.includes('∧') || conclusion.includes('/\\'),
      hasDisjunction: conclusion.includes('∨') || conclusion.includes('\\/'),
      hasNegation: conclusion.includes('¬') || conclusion.includes('~') || conclusion.includes('not'),
      hasEquality: conclusion.includes('='),
      isAtomic: !/[∀∃∧∨¬→]/.test(conclusion) && !/forall|exists|->/.test(conclusion),
      hasArithmetic: /[\+\-\*\/]/.test(conclusion) || /add|mul|sub|div/.test(conclusion),
      hasInductive: /Nat|List|Tree|inductive/.test(conclusion),
      conclusion,
      hypothesisCount: goal.hypotheses.length
    };
  }

  /**
   * 分析上下文
   */
  private analyzeContext(context: ProofState['context']): ContextPattern {
    return {
      hasRelevantHypotheses: context.variables.length > 0,
      hasUsefulTheorems: context.theorems.length > 0,
      hasDefinitions: context.definitions.length > 0,
      variableCount: context.variables.length,
      theoremCount: context.theorems.length
    };
  }

  /**
   * 计算策略适用性得分
   */
  private calculateApplicability(
    tactic: Tactic, 
    goal: GoalPattern, 
    context: ContextPattern,
    proofState: ProofState
  ): ApplicabilityScore {
    let goalMatch = 0;
    let contextMatch = 0;

    // 基于目标结构匹配策略
    switch (tactic.id) {
      case 'intro':
      case 'intros':
        if (goal.hasImplication || goal.hasForall) goalMatch = 1.0;
        else if (!goal.isAtomic) goalMatch = 0.3;
        break;
      
      case 'apply':
        if (context.hasUsefulTheorems || context.hasRelevantHypotheses) {
          goalMatch = 0.8;
          contextMatch = context.theoremCount > 0 ? 0.9 : 0.5;
        }
        break;
      
      case 'constructor':
      case 'split':
        if (goal.hasConjunction) goalMatch = 1.0;
        break;
      
      case 'left':
      case 'right':
        if (goal.hasDisjunction) goalMatch = 0.9;
        break;
      
      case 'exists':
        if (goal.hasExists) goalMatch = 1.0;
        break;
      
      case 'rw':
      case 'rewrite':
        if (goal.hasEquality) goalMatch = 0.9;
        else if (context.hasRelevantHypotheses) goalMatch = 0.6;
        break;
      
      case 'simp':
        goalMatch = goal.isAtomic ? 0.8 : 0.4;
        break;
      
      case 'induction':
        if (goal.hasInductive) goalMatch = 0.95;
        break;
      
      case 'cases':
        if (goal.hasDisjunction || goal.hasInductive) goalMatch = 0.85;
        break;
      
      case 'linarith':
      case 'omega':
        if (goal.hasArithmetic) goalMatch = 0.9;
        if (/≤|<|>|≥/.test(goal.conclusion)) goalMatch = 0.95;
        break;
      
      case 'ring':
      case 'field':
        if (goal.hasEquality && goal.hasArithmetic) goalMatch = 0.9;
        break;
      
      case 'tauto':
      case 'itauto':
        if (!goal.hasArithmetic && !goal.hasEquality) {
          goalMatch = 0.8;
        }
        break;
      
      case 'by_contra':
      case 'exfalso':
        if (goal.hasNegation) goalMatch = 0.9;
        else if (goal.isAtomic) goalMatch = 0.5;
        break;
      
      case 'exact':
        if (context.hasRelevantHypotheses && goal.isAtomic) {
          goalMatch = 0.8;
          contextMatch = 0.9;
        }
        break;
      
      case 'rfl':
        if (/=.*\1/.test(goal.conclusion)) goalMatch = 0.95;
        break;
      
      case 'aesop':
        goalMatch = 0.5; // 通用但不确定
        break;
      
      default:
        goalMatch = 0.3;
    }

    // 历史成功率
    const historicalSuccess = this.getHistoricalSuccess(tactic.id);

    // 计算综合得分
    const overall = (goalMatch * 0.5 + contextMatch * 0.3 + historicalSuccess * 0.2);

    return { goalMatch, contextMatch, historicalSuccess, overall };
  }

  /**
   * 获取历史成功率
   */
  private getHistoricalSuccess(tacticId: string): number {
    const successes = this.successHistory.get(tacticId) || 0;
    const usages = this.usageHistory.get(tacticId) || 0;
    return usages > 0 ? successes / usages : 0.5;
  }

  /**
   * 生成建议原因
   */
  private generateReason(tactic: Tactic, goal: GoalPattern, score: ApplicabilityScore): string {
    if (score.goalMatch > 0.8) {
      if (tactic.id === 'intro' || tactic.id === 'intros') {
        return '目标含有蕴含或全称量词，适合引入假设';
      }
      if (tactic.id === 'apply') {
        return '上下文中有可应用的定理或假设';
      }
      if (tactic.category === 'arithmetic') {
        return '目标涉及算术运算，此策略可自动求解';
      }
      if (tactic.category === 'automation') {
        return '当前目标适合自动化求解';
      }
    }
    
    if (tactic.category === 'introduction' && goal.hasForall) {
      return '目标含有全称量词';
    }
    
    if (tactic.difficulty === 'easy') {
      return '简单策略，适合作为开始';
    }
    
    return `基于${tactic.category}类别的推荐`;
  }

  /**
   * 生成策略预览
   */
  private generatePreview(tactic: Tactic, goal: ProofGoal): string {
    if (tactic.examples.length > 0) {
      return tactic.examples[0];
    }
    return tactic.syntax;
  }

  /**
   * 记录策略使用
   */
  recordUsage(tacticId: string, success: boolean) {
    const currentUsage = this.usageHistory.get(tacticId) || 0;
    this.usageHistory.set(tacticId, currentUsage + 1);
    
    if (success) {
      const currentSuccess = this.successHistory.get(tacticId) || 0;
      this.successHistory.set(tacticId, currentSuccess + 1);
    }
  }

  /**
   * 获取推荐策略
   */
  getRecommendedStrategy(proofState: ProofState): ProofStrategy | null {
    const currentGoal = proofState.goals.find(g => g.id === proofState.currentGoalId);
    if (!currentGoal) return null;

    // 根据目标特征选择最佳策略
    for (const strategy of this.strategies.values()) {
      for (const pattern of strategy.applicableGoals) {
        if (currentGoal.conclusion.includes(pattern)) {
          return strategy;
        }
      }
    }

    return null;
  }

  /**
   * 获取分类列表
   */
  getCategories(): { id: TacticCategory; name: string; icon: string }[] {
    return [
      { id: 'introduction', name: '引入规则', icon: '→' },
      { id: 'elimination', name: '消去规则', icon: '×' },
      { id: 'rewriting', name: '重写简化', icon: '⟲' },
      { id: 'automation', name: '自动化', icon: '⚡' },
      { id: 'induction', name: '归纳法', icon: '↻' },
      { id: 'arithmetic', name: '算术', icon: '∑' },
      { id: 'logic', name: '逻辑', icon: '⊤' },
      { id: 'equality', name: '等式', icon: '=' },
    ];
  }
}

// 内部类型
interface GoalPattern {
  hasImplication: boolean;
  hasForall: boolean;
  hasExists: boolean;
  hasConjunction: boolean;
  hasDisjunction: boolean;
  hasNegation: boolean;
  hasEquality: boolean;
  isAtomic: boolean;
  hasArithmetic: boolean;
  hasInductive: boolean;
  conclusion: string;
  hypothesisCount: number;
}

interface ContextPattern {
  hasRelevantHypotheses: boolean;
  hasUsefulTheorems: boolean;
  hasDefinitions: boolean;
  variableCount: number;
  theoremCount: number;
}

// 导出单例
export const proofStrategyEngine = new ProofStrategyEngine();
