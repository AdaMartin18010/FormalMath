/**
 * FormalMath 数据分析系统类型定义
 * 学习进度 / 概念掌握 / 学习效率 / 知识网络 / 预测分析
 */

// ==================== 通用类型 ====================

export type TimeRange = 'day' | 'week' | 'month' | 'quarter' | 'year';

export interface DateRange {
  start: string; // ISO date string
  end: string;
}

export interface AnalyticsFilter {
  timeRange?: TimeRange;
  dateRange?: DateRange;
  categories?: string[];
  conceptIds?: string[];
}

// ==================== 学习进度仪表板 ====================

export interface LearningProgressData {
  userId: string;
  generatedAt: string;
  summary: ProgressSummary;
  trends: ProgressTrend[];
  milestones: Milestone[];
  goals: LearningGoal[];
}

export interface ProgressSummary {
  totalConcepts: number;
  masteredConcepts: number;
  inProgressConcepts: number;
  notStartedConcepts: number;
  overallProgress: number; // 0-100
  averageMastery: number; // 0-100
  totalTimeSpent: number; // minutes
  weeklyStudyTime: number; // minutes
  dailyAverage: number; // minutes
}

export interface ProgressTrend {
  date: string;
  conceptsLearned: number;
  conceptsMastered: number;
  timeSpent: number;
  masteryGrowth: number;
}

export interface Milestone {
  id: string;
  title: string;
  description: string;
  targetConcepts: number;
  completedConcepts: number;
  progress: number;
  achievedAt?: string;
  deadline?: string;
  status: 'pending' | 'in_progress' | 'achieved' | 'overdue';
}

export interface LearningGoal {
  id: string;
  title: string;
  description: string;
  targetValue: number;
  currentValue: number;
  unit: string;
  deadline?: string;
  progress: number;
  status: 'active' | 'completed' | 'abandoned';
}

// ==================== 概念掌握热力图 ====================

export interface MasteryHeatmapData {
  userId: string;
  generatedAt: string;
  categories: ConceptCategory[];
  cells: HeatmapCell[];
  overallStats: HeatmapStats;
}

export interface ConceptCategory {
  id: string;
  name: string;
  color: string;
  conceptCount: number;
}

export interface HeatmapCell {
  conceptId: string;
  conceptName: string;
  categoryId: string;
  masteryLevel: number; // 0-100
  masteryLabel: '未开始' | '初学' | '理解' | '熟练' | '精通';
  lastStudiedAt?: string;
  studyCount: number;
  timeSpent: number;
  x: number; // 网格坐标
  y: number;
}

export interface HeatmapStats {
  averageMastery: number;
  masteryDistribution: Record<string, number>;
  weakestCategory: string;
  strongestCategory: string;
  needsReview: string[];
}

// ==================== 学习效率分析 ====================

export interface EfficiencyAnalysisData {
  userId: string;
  generatedAt: string;
  overallEfficiency: number; // 0-100
  timeDistribution: TimeDistribution;
  learningPatterns: LearningPattern[];
  optimalConditions: OptimalCondition[];
  recommendations: EfficiencyRecommendation[];
}

export interface TimeDistribution {
  byHour: HourlyData[];
  byDayOfWeek: DayOfWeekData[];
  bySessionLength: SessionLengthData[];
}

export interface HourlyData {
  hour: number; // 0-23
  avgEfficiency: number;
  avgTimeSpent: number;
  conceptsLearned: number;
}

export interface DayOfWeekData {
  day: number; // 0-6, 0 = Sunday
  dayName: string;
  avgEfficiency: number;
  totalTimeSpent: number;
  conceptsLearned: number;
}

export interface SessionLengthData {
  range: string; // "0-30min", "30-60min", etc.
  avgEfficiency: number;
  sessionCount: number;
  conceptsPerHour: number;
}

export interface LearningPattern {
  id: string;
  name: string;
  description: string;
  frequency: number; // times per week
  avgEfficiency: number;
  trend: 'improving' | 'stable' | 'declining';
}

export interface OptimalCondition {
  factor: string;
  optimalValue: string;
  impact: number; // efficiency improvement percentage
  confidence: number; // 0-1
}

export interface EfficiencyRecommendation {
  id: string;
  type: 'time' | 'method' | 'schedule' | 'break';
  title: string;
  description: string;
  expectedImprovement: number;
  priority: 'high' | 'medium' | 'low';
}

// ==================== 知识网络分析 ====================

export interface KnowledgeNetworkData {
  userId: string;
  generatedAt: string;
  nodes: KnowledgeNode[];
  edges: KnowledgeEdge[];
  networkStats: NetworkStats;
  communities: KnowledgeCommunity[];
  bridges: BridgeConcept[];
}

export interface KnowledgeNode {
  id: string;
  conceptId: string;
  label: string;
  category: string;
  masteryLevel: number;
  importance: number; // centrality measure
  connections: number;
  x: number;
  y: number;
  size: number;
  color: string;
}

export interface KnowledgeEdge {
  source: string;
  target: string;
  type: 'prerequisite' | 'related' | 'extension' | 'application';
  strength: number; // 0-1
  userKnown: boolean; // whether user knows both concepts
}

export interface NetworkStats {
  totalNodes: number;
  totalEdges: number;
  density: number;
  averageDegree: number;
  clusteringCoefficient: number;
  connectedComponents: number;
  knowledgeCoverage: number; // percentage of total domain
}

export interface KnowledgeCommunity {
  id: string;
  name: string;
  conceptIds: string[];
  avgMastery: number;
  cohesion: number;
  color: string;
}

export interface BridgeConcept {
  conceptId: string;
  conceptName: string;
  betweenness: number;
  connectsCommunities: string[];
  importance: 'critical' | 'important' | 'minor';
}

// ==================== 预测分析 ====================

export interface PredictionData {
  userId: string;
  generatedAt: string;
  completionPrediction: CompletionPrediction;
  performanceForecast: PerformanceForecast;
  riskAnalysis: RiskAnalysis;
  adaptiveSuggestions: AdaptiveSuggestion[];
}

export interface CompletionPrediction {
  targetCompletionDate: string;
  confidenceInterval: {
    optimistic: string;
    pessimistic: string;
  };
  probabilityByDate: DateProbability[];
  factors: PredictionFactor[];
}

export interface DateProbability {
  date: string;
  probability: number;
}

export interface PredictionFactor {
  name: string;
  impact: number; // -1 to 1
  trend: 'positive' | 'negative' | 'neutral';
}

export interface PerformanceForecast {
  nextWeek: WeeklyForecast;
  nextMonth: MonthlyForecast;
  trends: PerformanceTrend[];
}

export interface WeeklyForecast {
  expectedConcepts: number;
  expectedMasteryGain: number;
  confidence: number;
}

export interface MonthlyForecast {
  expectedConcepts: number;
  expectedMasteryGain: number;
  milestones: string[];
  confidence: number;
}

export interface PerformanceTrend {
  metric: string;
  current: number;
  predicted: number;
  change: number;
}

export interface RiskAnalysis {
  overallRisk: 'low' | 'medium' | 'high';
  riskFactors: RiskFactor[];
  atRiskConcepts: AtRiskConcept[];
  mitigationStrategies: MitigationStrategy[];
}

export interface RiskFactor {
  type: 'engagement' | 'difficulty' | 'time' | 'prerequisite';
  severity: 'low' | 'medium' | 'high';
  description: string;
  probability: number;
}

export interface AtRiskConcept {
  conceptId: string;
  conceptName: string;
  riskLevel: 'low' | 'medium' | 'high';
  reason: string;
}

export interface MitigationStrategy {
  targetRisk: string;
  action: string;
  expectedEffect: string;
  priority: 'high' | 'medium' | 'low';
}

export interface AdaptiveSuggestion {
  id: string;
  type: 'pace' | 'content' | 'schedule' | 'method';
  current: string;
  suggested: string;
  reason: string;
  expectedBenefit: string;
}

// ==================== API 请求/响应类型 ====================

export interface AnalyticsRequest {
  userId: string;
  filters?: AnalyticsFilter;
}

export interface AnalyticsResponse<T> {
  success: boolean;
  data: T;
  cached?: boolean;
  generatedAt: string;
}

export interface ExportAnalyticsRequest {
  userId: string;
  reportType: 'progress' | 'heatmap' | 'efficiency' | 'network' | 'prediction' | 'all';
  format: 'pdf' | 'csv' | 'json';
  dateRange?: DateRange;
}
