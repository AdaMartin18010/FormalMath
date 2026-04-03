// 题目类型
export type QuestionType = 'single_choice' | 'multiple_choice' | 'fill_blank' | 'true_false' | 'proof' | 'calculation';

// 知识层次
export type KnowledgeLevel = 0 | 1 | 2 | 3;

// 选项
export interface QuestionOption {
  id: string;
  text: string;
}

// 题目
export interface Question {
  id: string;
  type: QuestionType;
  content: string;
  options?: QuestionOption[];
  knowledge_level: KnowledgeLevel;
  estimated_time: number;
}

// 诊断会话
export interface DiagnosisSession {
  id: string;
  status: 'pending' | 'in_progress' | 'completed' | 'aborted';
  question_count: number;
  time_limit: number;
  current_question_index: number;
}

// 诊断进度
export interface DiagnosisProgress {
  current: number;
  total: number;
  percentage: number;
}

// 提交答案响应
export interface SubmitAnswerResponse {
  success: boolean;
  is_correct: boolean;
  score: number;
  progress: DiagnosisProgress;
  next_question?: Question;
  completed?: boolean;
  report_id?: string;
}

// 能力评估
export interface AbilityAssessment {
  level: number;
  score: number;
  description: string;
  mastered_concepts: string[];
  weak_concepts: string[];
}

// 学习建议
export interface LearningSuggestion {
  type: string;
  title: string;
  content: string;
  priority: number;
  related_concepts: string[];
}

// 可视化数据
export interface VisualizationData {
  radar: {
    labels: string[];
    datasets: any[];
  };
  pie: {
    labels: string[];
    datasets: any[];
  };
  comparison: {
    labels: string[];
    current: number[];
    target: number[];
  };
}

// 诊断报告
export interface DiagnosisReport {
  id: string;
  diagnosis_id: string;
  user_id: string;
  knowledge_state: Record<string, number>;
  ability_level: Record<string, number>;
  ability_assessments: AbilityAssessment[];
  suggestions: LearningSuggestion[];
  total_questions: number;
  correct_count: number;
  accuracy: number;
  avg_time_per_question: number;
  visualization_data: VisualizationData;
  created_at: string;
}

// API响应
export interface ApiResponse<T> {
  success: boolean;
  data: T;
  message: string;
}
