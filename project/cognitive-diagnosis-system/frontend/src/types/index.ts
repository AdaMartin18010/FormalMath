// 题目类型
export type QuestionType = 'SC' | 'MC' | 'FB' | 'SA' | 'PR'

// 知识层次
export type KnowledgeLevel = 0 | 1 | 2 | 3

// 能力等级
export type AbilityLevelName = 'beginner' | 'developing' | 'intermediate' | 'advanced'

// 题目
export interface Question {
  id: string
  content: string
  type: QuestionType
  level: KnowledgeLevel
  difficulty: number
  branch: string
  concepts: string[]
  skills: string[]
  options?: Record<string, string>
  time_estimate: number
  score: number
}

// 能力信息
export interface AbilityInfo {
  score: number
  level: AbilityLevelName
  description: string
  concept_count?: number
  mastered_concepts?: number
}

// 薄弱/优势领域
export interface AreaInfo {
  concept_id: string
  concept_name: string
  current_level: number
  target_level?: number
  improvement_needed?: number
}

// 学习建议
export interface Suggestion {
  type: string
  priority: number
  title: string
  description: string
  action?: string
  estimated_time?: string
  target_concept?: string
  resources?: string[]
  actions?: string[]
}

// 诊断结果
export interface DiagnosisResult {
  test_id: string
  student_id: string
  knowledge_state: Record<string, { level: number; confidence: number }>
  ability_level: Record<string, AbilityInfo>
  weak_areas: AreaInfo[]
  strong_areas: AreaInfo[]
  suggestions: Suggestion[]
  report_summary: string
  overall_confidence: number
  created_at: string
}

// 学习节点
export interface LearningNode {
  id: string
  title: string
  concept: string
  estimatedTime: string
  prerequisites: string[]
  status: 'pending' | 'in_progress' | 'completed'
  resources: string[]
}

// 学习路径
export interface LearningPath {
  currentNode: string
  progress: number
  nodes: LearningNode[]
}

// 用户档案
export interface UserProfile {
  username: string
  email: string
  currentLevel: number
  totalTests: number
  streak: number
  achievements: {
    name: string
    description: string
    date: string
  }[]
}

// API响应
export interface ApiResponse<T> {
  success: boolean
  message: string
  data: T
  error?: string
}
