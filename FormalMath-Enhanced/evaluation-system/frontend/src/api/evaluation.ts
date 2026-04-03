import apiClient from './client';
import {
  AssessmentRequest,
  AssessmentResponse,
  EvaluationReport,
  ProgressResponse,
  FeedbackResponse,
  DimensionsResponse,
} from '../types';

export const evaluationApi = {
  // Create assessment
  assess: async (data: AssessmentRequest): Promise<AssessmentResponse> => {
    const response = await apiClient.post('/evaluation/assess', data);
    return response.data;
  },

  // Get evaluation report
  getReport: async (
    userId: string,
    recordId?: string
  ): Promise<EvaluationReport> => {
    const params = recordId ? { record_id: recordId } : {};
    const response = await apiClient.get(`/evaluation/report/${userId}`, {
      params,
    });
    return response.data;
  },

  // Get learning progress/trajectory
  getProgress: async (
    userId: string,
    periods: number = 6
  ): Promise<ProgressResponse> => {
    const response = await apiClient.get(`/evaluation/progress/${userId}`, {
      params: { periods },
    });
    return response.data;
  },

  // Generate feedback
  generateFeedback: async (data: {
    user_id: string;
    record_id: string;
  }): Promise<FeedbackResponse> => {
    const response = await apiClient.post('/evaluation/feedback', data);
    return response.data;
  },

  // Get dimensions info
  getDimensions: async (): Promise<DimensionsResponse> => {
    const response = await apiClient.get('/evaluation/dimensions');
    return response.data;
  },

  // Get user records
  getUserRecords: async (userId: string): Promise<any> => {
    const response = await apiClient.get(`/evaluation/records/${userId}`);
    return response.data;
  },

  // Get user statistics
  getStatistics: async (userId: string): Promise<any> => {
    const response = await apiClient.get(`/evaluation/statistics/${userId}`);
    return response.data;
  },
};

export default evaluationApi;
