import client from './client';
import type {
  LearningPath,
  GeneratePathRequest,
  PathAdjustment,
  Resource,
  UserProfile,
  ConceptGraph,
  ConceptNode
} from '../types';

export const adaptiveApi = {
  // 生成学习路径
  generatePath: async (request: GeneratePathRequest) => {
    const response = await client.post('/adaptive/path', request);
    return response.data;
  },

  // 获取用户的学习路径
  getUserPaths: async (userId: string, status?: string) => {
    const params = status ? { status } : {};
    const response = await client.get(`/adaptive/path/${userId}`, { params });
    return response.data as LearningPath[];
  },

  // 获取路径详情
  getPathDetail: async (pathId: string) => {
    const response = await client.get(`/adaptive/path/detail/${pathId}`);
    return response.data as LearningPath;
  },

  // 调整学习路径
  adjustPath: async (request: {
    user_id: string;
    path_id: string;
    performance_data: Record<string, any>;
    reason?: string;
  }) => {
    const response = await client.post('/adaptive/adjust', request);
    return response.data as {
      success: boolean;
      adjustment?: PathAdjustment;
      updated_path?: LearningPath;
      message: string;
    };
  },

  // 获取资源推荐
  getRecommendations: async (userId: string, conceptId?: string, num: number = 5) => {
    const params = conceptId ? { concept_id: conceptId, num } : { num };
    const response = await client.get(`/adaptive/recommendations/${userId}`, { params });
    return response.data as {
      user_id: string;
      concept_id?: string;
      recommendations: Resource[];
      message: string;
    };
  },

  // 更新学习进度
  updateProgress: async (request: {
    user_id: string;
    path_id: string;
    node_id: string;
    status: string;
    score?: number;
    time_spent?: number;
    feedback?: string;
  }) => {
    const response = await client.post('/adaptive/progress/update', request);
    return response.data;
  },

  // 更新概念掌握度
  updateMastery: async (request: {
    user_id: string;
    concept_id: string;
    mastery_score: number;
    assessment_method?: string;
  }) => {
    const response = await client.post('/adaptive/mastery/update', request);
    return response.data;
  },

  // 获取下一步建议
  getNextSuggestion: async (userId: string, currentConcept?: string) => {
    const params = currentConcept ? { current_concept: currentConcept } : {};
    const response = await client.get(`/adaptive/suggest/${userId}`, { params });
    return response.data as {
      action: string;
      message: string;
      resources?: Resource[];
      suggestions?: string[];
    };
  },

  // 搜索概念
  searchConcepts: async (query: string, filters?: {
    branch?: string;
    difficulty?: string;
    limit?: number;
  }) => {
    const params = { query, ...filters };
    const response = await client.get('/adaptive/concepts/search', { params });
    return response.data as {
      query: string;
      total: number;
      concepts: ConceptNode[];
    };
  },

  // 获取概念详情
  getConceptDetail: async (conceptId: string) => {
    const response = await client.get(`/adaptive/concepts/${conceptId}`);
    return response.data as ConceptNode & {
      complexity_score: number;
      prerequisites: string[];
      successors: string[];
      related_concepts: string[];
    };
  },

  // 获取用户统计
  getUserStats: async (userId: string) => {
    const response = await client.get(`/adaptive/stats/${userId}`);
    return response.data as {
      user_id: string;
      current_level: string;
      cognitive_style: string;
      learning_preference: string;
      statistics: {
        total_study_time: number;
        completed_concepts: number;
        average_score: number;
        total_paths: number;
        completed_paths: number;
        in_progress_paths: number;
      };
      mastered_concepts: string[];
      interest_areas: string[];
    };
  },

  // 获取概念图谱
  getConceptGraph: async (): Promise<ConceptGraph> => {
    const response = await client.get('/v1/concept-graph');
    return response.data;
  }
};

export default adaptiveApi;
