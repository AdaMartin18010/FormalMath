// 类型定义

export enum CognitiveStyle {
  VISUAL = 'visual',
  AUDITORY = 'auditory',
  READING = 'reading',
  KINESTHETIC = 'kinesthetic',
  MIXED = 'mixed'
}

export enum LearningPreference {
  THEORY_FIRST = 'theory_first',
  EXAMPLE_FIRST = 'example_first',
  PRACTICE_FIRST = 'practice_first',
  BALANCED = 'balanced'
}

export enum DifficultyLevel {
  BEGINNER = 'beginner',
  INTERMEDIATE = 'intermediate',
  ADVANCED = 'advanced',
  EXPERT = 'expert'
}

export enum PathStatus {
  PENDING = 'pending',
  IN_PROGRESS = 'in_progress',
  COMPLETED = 'completed',
  ADJUSTED = 'adjusted',
  ABANDONED = 'abandoned'
}

export enum ResourceType {
  TEXT = 'text',
  VIDEO = 'video',
  INTERACTIVE = 'interactive',
  EXERCISE = 'exercise',
  PROOF = 'proof',
  EXAMPLE = 'example'
}

export interface ConceptNode {
  id: string;
  name: string;
  description: string;
  branch: string;
  difficulty: DifficultyLevel;
  estimated_time: number;
  prerequisites: string[];
  successors: string[];
  related: string[];
}

export interface PathNode {
  node_id: string;
  concept: ConceptNode;
  order: number;
  status: PathStatus;
  recommended_resources: Resource[];
  estimated_time: number;
  difficulty_adjustment: number;
  priority_score: number;
}

export interface Resource {
  id: string;
  title: string;
  type: ResourceType;
  url?: string;
  description: string;
  difficulty: DifficultyLevel;
  estimated_time: number;
  relevance_score: number;
  match_reason: string;
}

export interface LearningPath {
  path_id: string;
  user_id: string;
  name: string;
  description: string;
  target_concepts: string[];
  nodes: PathNode[];
  total_concepts: number;
  total_estimated_time: number;
  completed_nodes: number;
  progress_percentage: number;
  status: PathStatus;
  created_at: string;
  updated_at: string;
}

export interface UserProfile {
  user_id: string;
  cognitive_style: CognitiveStyle;
  learning_preference: LearningPreference;
  current_level: DifficultyLevel;
  mastered_concepts: Record<string, number>;
  interest_areas: string[];
  total_study_time: number;
  completed_concepts: number;
  average_score: number;
}

export interface GeneratePathRequest {
  user_id: string;
  target_concepts: string[];
  algorithm?: string;
  constraints?: Record<string, any>;
  preferences?: Record<string, any>;
}

export interface PathAdjustment {
  adjustment_id: string;
  path_id: string;
  trigger_reason: string;
  old_nodes: PathNode[];
  new_nodes: PathNode[];
  created_at: string;
}

export interface GraphNode {
  id: string;
  name: string;
  branch: string;
  difficulty: string;
  x?: number;
  y?: number;
}

export interface GraphEdge {
  source: string;
  target: string;
  type: string;
}

export interface ConceptGraph {
  nodes: GraphNode[];
  edges: GraphEdge[];
}
