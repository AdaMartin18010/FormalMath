/**
 * FormalMath 智能学习系统类型定义
 * T2.1 认知诊断 / T2.2 评估系统 / T3.1 自适应学习
 */

// ==================== 通用类型 ====================

export interface User {
  id: string;
  name: string;
  avatar?: string;
  level: LearnerLevel;
  joinedAt: string;
}

export type LearnerLevel = 'beginner' | 'intermediate' | 'advanced' | 'expert';

export type MasteryLevel = 0 | 1 | 2 | 3 | 4; // L0-L4

export interface Concept {
  id: string;
  name: string;
  description: string;
  category: string;
  prerequisites: string[];
  difficulty: number; // 1-10
}

// ==================== T2.1 认知诊断系统 ====================

export interface Answer {
  questionId: string;
  selectedOption: string | string[];
  timeSpent: number; // seconds
  confidence?: number; // 0-1
}

export interface DiagnosisReport {
  id: string;
  userId: string;
  createdAt: string;
  overallLevel: MasteryLevel;
  knowledgeLevels: Record<string, MasteryLevel>; // conceptId -> L0-L4
  weakPoints: WeakPoint[];
  strengths: Strength[];
  recommendations: Recommendation[];
  learningStyle?: LearningStyleProfile;
}

export interface WeakPoint {
  conceptId: string;
  conceptName: string;
  currentLevel: MasteryLevel;
  targetLevel: MasteryLevel;
  gap: number;
  priority: 'high' | 'medium' | 'low';
}

export interface Strength {
  conceptId: string;
  conceptName: string;
  level: MasteryLevel;
  canTeachOthers: boolean;
}

export interface Recommendation {
  type: 'concept' | 'exercise' | 'review' | 'challenge';
  targetId: string;
  title: string;
  description: string;
  priority: number;
  estimatedTime: number; // minutes
}

export interface LearningStyleProfile {
  visual: number;
  auditory: number;
  kinesthetic: number;
  reading: number;
  dominant: 'visual' | 'auditory' | 'kinesthetic' | 'reading';
}

export interface DiagnosisSubmitRequest {
  answers: Answer[];
  metadata?: {
    totalTime: number;
    device: string;
    version: string;
  };
}

export interface DiagnosisSubmitResponse {
  diagnosisId: string;
  report: DiagnosisReport;
  nextSteps: string[];
}

// ==================== T2.2 评估系统 ====================

export interface EvaluationReport {
  userId: string;
  generatedAt: string;
  dimensions: AbilityDimensions;
  overallScore: number;
  percentile: number;
  growthCurve: GrowthDataPoint[];
  comparisons: Comparison[];
  badges: Badge[];
  achievements: Achievement[];
}

export interface AbilityDimensions {
  knowledge: number;      // 0-100
  problemSolving: number; // 0-100
  proofAbility: number;   // 0-100
  application: number;    // 0-100
  innovation: number;     // 0-100
}

export interface GrowthDataPoint {
  date: string;
  overall: number;
  knowledge: number;
  problemSolving: number;
  proofAbility: number;
  application: number;
  innovation: number;
}

export interface Comparison {
  type: 'peer' | 'historical' | 'target';
  label: string;
  value: number;
  diff?: number;
}

export interface Badge {
  id: string;
  name: string;
  icon: string;
  earnedAt: string;
  rarity: 'common' | 'rare' | 'epic' | 'legendary';
}

export interface Achievement {
  id: string;
  title: string;
  description: string;
  progress: number; // 0-100
  completed: boolean;
  completedAt?: string;
}

// ==================== T3.1 自适应学习系统 ====================

export interface LearningPath {
  userId: string;
  generatedAt: string;
  path: LearningNode[];
  estimatedTime: number; // minutes
  overallDifficulty: number; // 1-10
  isPersonalized: boolean;
  adaptReason?: string;
}

export interface LearningNode {
  id: string;
  conceptId: string;
  conceptName: string;
  type: 'learn' | 'practice' | 'assess' | 'review' | 'challenge';
  status: LearningNodeStatus;
  estimatedTime: number; // minutes
  difficulty: number; // 1-10
  dependencies: string[]; // node ids
  unlockCriteria?: UnlockCriteria;
  content?: LearningContent;
}

export type LearningNodeStatus = 'locked' | 'available' | 'in_progress' | 'completed' | 'skipped';

export interface UnlockCriteria {
  prerequisiteNodes?: string[];
  minMasteryLevel?: MasteryLevel;
  requiredBadges?: string[];
}

export interface LearningContent {
  theoryUrl?: string;
  videoUrl?: string;
  exercises: Exercise[];
  resources: Resource[];
}

export interface Exercise {
  id: string;
  type: 'multiple_choice' | 'fill_blank' | 'proof' | 'open_ended';
  difficulty: number;
  estimatedTime: number;
}

export interface Resource {
  id: string;
  type: 'article' | 'video' | 'book' | 'tool';
  title: string;
  url: string;
}

export interface ProgressUpdateRequest {
  userId: string;
  conceptId: string;
  mastery: number; // 0-100
  timeSpent?: number;
  completedExercises?: number;
  correctRate?: number;
}

export interface ProgressUpdateResponse {
  success: boolean;
  newMastery: number;
  levelUp: boolean;
  newLevel?: MasteryLevel;
  unlockedConcepts: string[];
  nextRecommendations: string[];
}

// ==================== 个性化知识图谱 ====================

export interface PersonalizedGraphData {
  nodes: PersonalizedNode[];
  edges: GraphEdge[];
  userProgress: UserProgressSummary;
}

export interface PersonalizedNode {
  id: string;
  conceptId: string;
  label: string;
  mastery: MasteryLevel;
  isWeakPoint: boolean;
  isRecommended: boolean;
  isCurrentFocus: boolean;
  x: number;
  y: number;
  size: number;
  color: string;
  opacity: number;
}

export interface GraphEdge {
  source: string;
  target: string;
  type: 'prerequisite' | 'related' | 'extension';
}

export interface UserProgressSummary {
  totalConcepts: number;
  masteredConcepts: number;
  inProgressConcepts: number;
  weakPointsCount: number;
  overallCompletion: number;
}

// ==================== 学习路径可视化 ====================

export interface VisualPath {
  nodes: VisualPathNode[];
  connections: PathConnection[];
  progress: PathProgress;
}

export interface VisualPathNode {
  id: string;
  conceptId: string;
  position: { x: number; y: number };
  status: LearningNodeStatus;
  mastery: MasteryLevel;
  estimatedTime: number;
  isMilestone: boolean;
}

export interface PathConnection {
  from: string;
  to: string;
  type: 'main' | 'alternative' | 'shortcut';
}

export interface PathProgress {
  completed: number;
  total: number;
  estimatedRemaining: number;
  currentNode?: string;
}

// ==================== API 响应类型 ====================

export interface ApiResponse<T> {
  success: boolean;
  data: T;
  message?: string;
  timestamp: string;
}

export interface ApiError {
  code: string;
  message: string;
  details?: Record<string, unknown>;
}

export interface PaginatedResponse<T> {
  items: T[];
  total: number;
  page: number;
  pageSize: number;
  hasMore: boolean;
}
