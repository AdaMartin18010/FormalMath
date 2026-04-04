// ==================== 交互式练习系统类型定义 ====================

/** 练习题型 */
export type ExerciseType = 
  | 'single_choice'      // 单选题
  | 'multiple_choice'    // 多选题
  | 'fill_blank'         // 填空题
  | 'calculation'        // 计算题
  | 'proof'              // 证明题
  | 'matching'           // 配对题
  | 'ordering'           // 排序题
  | 'true_false';        // 判断题

/** 难度等级 */
export type DifficultyLevel = 'beginner' | 'intermediate' | 'advanced' | 'expert';

/** 练习状态 */
export type ExerciseStatus = 'not_started' | 'in_progress' | 'completed' | 'reviewing';

/** 答案验证结果 */
export interface ValidationResult {
  isCorrect: boolean;
  score: number;           // 0-100
  feedback: string;        // 反馈信息
  detailedFeedback?: string; // 详细反馈
  correctAnswer?: unknown; // 正确答案
  partialCredit?: number;  // 部分得分
  hints?: string[];        // 相关提示
}

/** 逐步提示 */
export interface StepHint {
  step: number;
  title: string;
  content: string;
  revealed: boolean;
}

/** 练习题目 */
export interface Exercise {
  id: string;
  type: ExerciseType;
  difficulty: DifficultyLevel;
  status: ExerciseStatus;
  
  // 内容
  title: string;
  content: string;         // 题目内容（支持 LaTeX）
  options?: ExerciseOption[]; // 选项（选择题）
  blanks?: BlankItem[];    // 填空项
  correctAnswer: unknown;  // 正确答案
  
  // 提示系统
  hints: StepHint[];
  maxHints: number;        // 最大提示数
  
  // 解析
  solution: string;        // 完整解析
  keyPoints: string[];     // 关键知识点
  commonMistakes: string[]; // 常见错误
  
  // 元数据
  subject: string;         // 学科
  topic: string;           // 主题
  subtopic?: string;       // 子主题
  tags: string[];
  estimatedTime: number;   // 预计用时（分钟）
  points: number;          // 分值
  
  // 关联
  prerequisites: string[]; // 前置知识
  relatedConcepts: string[]; // 相关概念
  relatedTheorems?: string[]; // 相关定理
}

/** 选项 */
export interface ExerciseOption {
  id: string;
  label: string;
  content: string;
  isCorrect?: boolean;     // 仅用于多选题
}

/** 填空项 */
export interface BlankItem {
  id: string;
  position: number;
  answer: string;
  alternatives?: string[]; // 替代答案
  tolerance?: number;      // 数值容差（用于计算题）
}

/** 用户答案 */
export interface UserAnswer {
  exerciseId: string;
  answer: unknown;
  timestamp: string;
  timeSpent: number;       // 用时（秒）
  hintsUsed: number;       // 使用的提示数
  attempts: number;        // 尝试次数
}

/** 练习会话 */
export interface ExerciseSession {
  id: string;
  userId: string;
  title: string;
  description?: string;
  
  // 配置
  exerciseIds: string[];
  shuffleOrder: boolean;
  timeLimit?: number;      // 总时间限制（分钟）
  allowHints: boolean;
  maxAttempts: number;
  
  // 状态
  status: 'not_started' | 'in_progress' | 'completed' | 'paused';
  currentIndex: number;
  answers: Record<string, UserAnswer>;
  
  // 统计
  startTime?: string;
  endTime?: string;
  totalScore: number;
  maxPossibleScore: number;
}

/** 错题记录 */
export interface MistakeRecord {
  id: string;
  exerciseId: string;
  userId: string;
  
  // 错误信息
  wrongAnswer: unknown;
  errorType: ErrorType;
  errorAnalysis?: string;
  
  // 时间记录
  firstWrongAt: string;
  lastWrongAt: string;
  reviewCount: number;
  reviewHistory: ReviewRecord[];
  
  // 掌握状态
  masteryLevel: MasteryLevel;
  nextReviewDate: string;
  isResolved: boolean;
  
  // 关联
  relatedMistakes?: string[]; // 相关错题ID
}

/** 错误类型 */
export type ErrorType =
  | 'concept_misunderstanding'  // 概念理解错误
  | 'calculation_error'         // 计算错误
  | 'formula_misapplication'    // 公式误用
  | 'logic_error'               // 逻辑错误
  | 'careless_mistake'          // 粗心错误
  | 'knowledge_gap'             // 知识漏洞
  | 'other';

/** 掌握等级 */
export type MasteryLevel = 'weak' | 'developing' | 'mastered' | 'forgotten';

/** 复习记录 */
export interface ReviewRecord {
  timestamp: string;
  isCorrect: boolean;
  timeSpent: number;
  hintsUsed: number;
}

/** 学习进度 */
export interface ExerciseProgress {
  userId: string;
  
  // 总体统计
  totalExercises: number;
  completedExercises: number;
  correctExercises: number;
  accuracy: number;
  
  // 分难度统计
  byDifficulty: Record<DifficultyLevel, DifficultyStats>;
  
  // 分主题统计
  byTopic: Record<string, TopicStats>;
  
  // 时间统计
  totalStudyTime: number;  // 总学习时长（分钟）
  streakDays: number;      // 连续学习天数
  lastStudyDate: string;
  
  // 错题统计
  totalMistakes: number;
  resolvedMistakes: number;
  pendingReviews: number;
}

/** 难度统计 */
interface DifficultyStats {
  total: number;
  completed: number;
  correct: number;
  accuracy: number;
}

/** 主题统计 */
interface TopicStats {
  total: number;
  completed: number;
  correct: number;
  accuracy: number;
  mastery: number;         // 掌握度 0-100
}

/** 练习过滤器 */
export interface ExerciseFilter {
  types?: ExerciseType[];
  difficulties?: DifficultyLevel[];
  subjects?: string[];
  topics?: string[];
  tags?: string[];
  status?: ExerciseStatus[];
  prerequisites?: string[];
  excludeCompleted?: boolean;
  searchQuery?: string;
}

/** 练习推荐 */
export interface ExerciseRecommendation {
  exerciseId: string;
  reason: RecommendationReason;
  priority: number;        // 优先级 1-10
  explanation: string;
}

/** 推荐原因 */
export type RecommendationReason =
  | 'knowledge_gap'         // 填补知识漏洞
  | 'mastery_review'        // 掌握度复习
  | 'prerequisite'          // 前置知识
  | 'difficulty_progression' // 难度进阶
  | 'error_pattern'         // 错误模式
  | 'weak_area'             // 薄弱环节
  | 'daily_practice';       // 日常练习

/** 练习设置 */
export interface ExerciseSettings {
  // 界面设置
  showHintButton: boolean;
  showSolutionButton: boolean;
  autoShowSolution: boolean;
  autoAdvance: boolean;
  
  // 行为设置
  allowSkip: boolean;
  requireExplanation: boolean;
  timeLimitPerExercise?: number;
  
  // 反馈设置
  immediateFeedback: boolean;
  showCorrectAnswer: boolean;
  showDetailedFeedback: boolean;
  
  // 学习设置
  adaptiveDifficulty: boolean;
  spacedRepetition: boolean;
  dailyGoal: number;
}

/** 练习组件 Props */
export interface ExerciseComponentProps {
  exercise: Exercise;
  userAnswer?: unknown;
  onAnswer: (answer: unknown) => void;
  onRequestHint?: () => void;
  onShowSolution?: () => void;
  onSkip?: () => void;
  settings?: ExerciseSettings;
  disabled?: boolean;
}

/** 验证器配置 */
export interface ValidatorConfig {
  caseSensitive: boolean;
  ignoreWhitespace: boolean;
  numericalTolerance: number;
  partialCreditEnabled: boolean;
}
