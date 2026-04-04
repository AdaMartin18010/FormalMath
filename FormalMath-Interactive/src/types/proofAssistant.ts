/**
 * 定理证明助手类型定义
 * Proof Assistant Type Definitions
 */

// ==================== 证明状态类型 ====================

export type ProofStatus = 
  | 'initial'      // 初始状态
  | 'in_progress'  // 进行中
  | 'complete'     // 已完成
  | 'error'        // 错误
  | 'timeout';     // 超时

export type TacticCategory =
  | 'introduction'    // 引入规则
  | 'elimination'     // 消去规则
  | 'rewriting'       // 重写规则
  | 'automation'      // 自动化
  | 'induction'       // 归纳法
  | 'arithmetic'      // 算术
  | 'logic'           // 逻辑
  | 'equality'        // 等式
  | 'custom';         // 自定义

export type Difficulty = 'easy' | 'medium' | 'hard' | 'expert';

// ==================== 核心证明结构 ====================

export interface ProofGoal {
  id: string;
  conclusion: string;
  hypotheses: Hypothesis[];
  isCompleted: boolean;
}

export interface Hypothesis {
  id: string;
  name: string;
  type: string;
  value?: string;
}

export interface ProofState {
  goals: ProofGoal[];
  currentGoalId: string | null;
  completedGoals: string[];
  proofSteps: ProofStep[];
  context: ProofContext;
}

export interface ProofContext {
  variables: Variable[];
  constants: Constant[];
  definitions: Definition[];
  theorems: TheoremRef[];
}

export interface Variable {
  name: string;
  type: string;
}

export interface Constant {
  name: string;
  type: string;
  value?: string;
}

export interface Definition {
  name: string;
  params: string[];
  body: string;
}

export interface TheoremRef {
  name: string;
  statement: string;
  proven: boolean;
}

// ==================== 证明步骤 ====================

export interface ProofStep {
  id: string;
  stepNumber: number;
  tactic: Tactic;
  goalBefore: ProofGoal;
  goalsAfter: ProofGoal[];
  description: string;
  timestamp: number;
  leanCode: string;
}

export interface Tactic {
  id: string;
  name: string;
  category: TacticCategory;
  description: string;
  syntax: string;
  examples: string[];
  difficulty: Difficulty;
  parameters?: TacticParameter[];
}

export interface TacticParameter {
  name: string;
  type: 'string' | 'number' | 'expression' | 'identifier' | 'list';
  description: string;
  required: boolean;
  defaultValue?: string;
}

// ==================== 策略推荐 ====================

export interface TacticSuggestion {
  tactic: Tactic;
  confidence: number;
  reason: string;
  preview?: string;
  applicability: ApplicabilityScore;
}

export interface ApplicabilityScore {
  goalMatch: number;      // 目标匹配度
  contextMatch: number;   // 上下文匹配度
  historicalSuccess: number; // 历史成功率
  overall: number;        // 综合得分
}

export interface ProofStrategy {
  id: string;
  name: string;
  description: string;
  applicableGoals: string[];
  tactics: Tactic[];
  estimatedSteps: number;
  difficulty: Difficulty;
}

// ==================== Lean4 代码生成 ====================

export interface Lean4Code {
  theorem: string;
  statement: string;
  proof: string;
  complete: string;
  imports: string[];
  namespace?: string;
}

export interface CodeGenerationOptions {
  style: 'verbose' | 'compact' | 'structured';
  includeComments: boolean;
  useMathlib: boolean;
  indentation: number;
}

// ==================== 验证结果 ====================

export interface VerificationResult {
  success: boolean;
  proofState: ProofState;
  errors: ProofError[];
  warnings: ProofWarning[];
  elapsed: number;
  stepsVerified: number;
}

export interface ProofError {
  stepNumber?: number;
  type: 'syntax' | 'type' | 'logic' | 'runtime';
  message: string;
  location?: CodeLocation;
  suggestions?: string[];
}

export interface ProofWarning {
  stepNumber?: number;
  message: string;
  suggestion?: string;
}

export interface CodeLocation {
  line: number;
  column: number;
  endLine?: number;
  endColumn?: number;
}

// ==================== 交互式证明构造 ====================

export interface ProofConstruction {
  id: string;
  theoremName: string;
  theoremStatement: string;
  currentState: ProofState;
  history: ProofState[];
  branches: ProofBranch[];
}

export interface ProofBranch {
  id: string;
  name: string;
  goals: ProofGoal[];
  parentBranchId?: string;
  isActive: boolean;
}

export interface ProofCheckpoint {
  id: string;
  name: string;
  state: ProofState;
  timestamp: number;
  description?: string;
}

// ==================== 证明可视化 ====================

export interface ProofTreeNode {
  id: string;
  goal: ProofGoal;
  tactic?: Tactic;
  children: ProofTreeNode[];
  parent?: string;
  depth: number;
  isCompleted: boolean;
  position: { x: number; y: number };
}

export interface ProofTree {
  root: ProofTreeNode;
  nodes: ProofTreeNode[];
  leaves: ProofTreeNode[];
  maxDepth: number;
}

export interface VisualizationConfig {
  layout: 'tree' | 'graph' | 'linear';
  direction: 'vertical' | 'horizontal';
  showHypotheses: boolean;
  showTactics: boolean;
  colorScheme: 'default' | 'dark' | 'colorful';
  nodeSpacing: number;
  levelSpacing: number;
}

// ==================== 学习相关 ====================

export interface ProofHint {
  level: 'subtle' | 'moderate' | 'explicit';
  message: string;
  relatedTactic?: string;
  example?: string;
}

export interface ProofExplanation {
  stepId: string;
  naturalLanguage: string;
  formalDetails: string;
  intuition: string;
  references?: string[];
}

// ==================== 组件 Props ====================

export interface ProofAssistantProps {
  initialTheorem?: string;
  initialStatement?: string;
  onProofComplete?: (proof: ProofConstruction) => void;
  onStepChange?: (step: ProofStep) => void;
  enableSuggestions?: boolean;
  enableAutoVerify?: boolean;
}

export interface ProofStateViewProps {
  proofState: ProofState;
  onGoalSelect?: (goalId: string) => void;
  onHypothesisClick?: (hypothesis: Hypothesis) => void;
  config?: Partial<VisualizationConfig>;
}

export interface TacticPanelProps {
  suggestions: TacticSuggestion[];
  onTacticSelect: (tactic: Tactic) => void;
  onTacticSearch?: (query: string) => void;
  selectedCategory?: TacticCategory;
  showPreview?: boolean;
}

export interface LeanCodeEditorProps {
  code: Lean4Code;
  onChange?: (code: Lean4Code) => void;
  readOnly?: boolean;
  showLineNumbers?: boolean;
  height?: string;
}

export interface VerificationPanelProps {
  result: VerificationResult | null;
  isVerifying: boolean;
  onReverify?: () => void;
  onErrorClick?: (error: ProofError) => void;
}
