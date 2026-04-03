// Dimension scores
export interface DimensionScores {
  knowledge_mastery: number;
  problem_solving: number;
  proof_ability: number;
  application: number;
  innovation: number;
}

// Assessment request
export interface AssessmentRequest {
  user_id: string;
  scores: DimensionScores;
  evaluation_type?: string;
  period?: string;
  assessor_id?: string;
  notes?: string;
}

// Assessment response
export interface AssessmentResponse {
  record_id: string;
  user_id: string;
  evaluation_type: string;
  scores: {
    total_score: number;
    weighted_score: number;
    grade: string;
    percentile: number;
    dimension_scores: Record<string, DimensionScoreDetail>;
  };
  created_at: string;
}

export interface DimensionScoreDetail {
  name: string;
  score: number;
  weight: number;
  weighted_score: number;
  percentage: number;
}

// Report
export interface EvaluationReport {
  report_metadata: ReportMetadata;
  executive_summary: ExecutiveSummary;
  detailed_scores: DetailedScores;
  dimension_analysis: Record<string, DimensionAnalysis>;
  strengths_and_improvements: StrengthsWeaknesses;
  feedback?: Feedback;
  learning_trajectory?: LearningTrajectory;
}

export interface ReportMetadata {
  report_id: string;
  user_id: string;
  record_id: string;
  generated_at: string;
  report_type: string;
}

export interface ExecutiveSummary {
  evaluation_date: string;
  evaluation_type: string;
  overall_score: number;
  grade: string;
  percentile: number;
  overall_assessment: string;
  key_highlights: string[];
}

export interface DetailedScores {
  total_score: number;
  weighted_score: number;
  dimension_scores: Record<string, DimensionScoreInfo>;
  grade_distribution: Record<string, number>;
}

export interface DimensionScoreInfo {
  score: number;
  weight: number;
  weighted_score: number;
  name: string;
}

export interface DimensionAnalysis {
  name: string;
  score: number;
  level: string;
  description: string;
  recommendations: string[];
}

export interface StrengthsWeaknesses {
  strengths: StrengthWeaknessItem[];
  weaknesses: StrengthWeaknessItem[];
  strongest: StrengthWeaknessItem | null;
  weakest: StrengthWeaknessItem | null;
}

export interface StrengthWeaknessItem {
  dimension: string;
  name: string;
  score: number;
  weight: number;
}

export interface Feedback {
  summary: string;
  strengths: string[];
  weaknesses: string[];
  suggestions: Suggestion[];
  recommended_path: LearningPath;
}

export interface Suggestion {
  dimension: string;
  dimension_name: string;
  priority: string;
  actions: string[];
  target_score: number;
}

export interface LearningPath {
  total_duration: string;
  phases: PathPhase[];
  expected_outcome: string;
}

export interface PathPhase {
  phase: number;
  name: string;
  duration: string;
  focus: string[];
  objectives: string[];
}

// Learning Trajectory
export interface LearningTrajectory {
  data_points: number;
  trajectory: TrajectoryPoint[];
  overall_trend: string;
  overall_growth: number;
}

export interface TrajectoryPoint {
  date: string;
  period?: string;
  scores: DimensionScores;
}

// Progress Response
export interface ProgressResponse {
  user_id: string;
  data_points: number;
  trajectory: TrajectoryPoint[];
  growth_analysis?: GrowthAnalysis;
}

export interface GrowthAnalysis {
  user_id: string;
  periods_analyzed: number;
  period_growth: PeriodGrowth[];
  overall_growth: OverallGrowth;
  trend_direction: string;
}

export interface PeriodGrowth {
  period: string;
  growth: {
    dimension_growth: Record<string, DimensionGrowth>;
    overall_growth: number;
    growth_rate: number;
  };
}

export interface DimensionGrowth {
  current: number;
  previous: number;
  absolute_growth: number;
  relative_growth: number;
  trend: string;
}

export interface OverallGrowth {
  dimension_growth: Record<string, DimensionGrowth>;
  overall_growth: number;
  growth_rate: number;
}

// Feedback
export interface FeedbackResponse {
  feedback_id: string;
  user_id: string;
  record_id: string;
  summary: string;
  strengths: StrengthWeaknessItem[];
  weaknesses: StrengthWeaknessItem[];
  suggestions: Suggestion[];
  dimension_feedback: {
    strengths: string[];
    improvements: string[];
    growth: string[];
  };
  recommended_resources: Resource[];
  recommended_path: LearningPath;
  generated_at: string;
}

export interface Resource {
  type: string;
  title: string;
  difficulty: string;
}

// Dimensions info
export interface DimensionInfo {
  key: string;
  name: string;
  weight: number;
  description: string;
}

export interface DimensionsResponse {
  dimensions: DimensionInfo[];
  total_weight: number;
}

// API Error
export interface ApiError {
  error: string;
  detail?: string;
}
