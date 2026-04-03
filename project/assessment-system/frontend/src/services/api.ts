import axios from 'axios';

const API_BASE_URL = 'http://localhost:8000/api/v1';

const api = axios.create({
  baseURL: API_BASE_URL,
  headers: {
    'Content-Type': 'application/json'
  }
});

// 学习者API
export const learnerAPI = {
  create: (data: any) => api.post('/learners', data),
  get: (id: string) => api.get(`/learners/${id}`),
  updateAbility: (id: string, data: any) => api.put(`/learners/${id}/ability`, data),
  updateKnowledge: (id: string, data: any) => api.put(`/learners/${id}/knowledge`, data),
};

// 评估API
export const evaluationAPI = {
  comprehensive: (data: any) => api.post('/evaluations/comprehensive', data),
  process: (learnerId: string, periodDays: number = 7) => 
    api.post('/evaluations/process', null, { params: { learner_id: learnerId, period_days: periodDays } }),
  valueAdded: (learnerId: string, periodDays: number = 30) =>
    api.post('/evaluations/value-added', null, { params: { learner_id: learnerId, period_days: periodDays } }),
  history: (learnerId: string, params?: any) => api.get(`/evaluations/${learnerId}/history`, { params }),
};

// 行为记录API
export const behaviorAPI = {
  record: (data: any) => api.post('/behaviors', data),
  batchRecord: (data: any[]) => api.post('/behaviors/batch', data),
};

// 反馈API
export const feedbackAPI = {
  get: (learnerId: string, params?: any) => api.get(`/feedback/${learnerId}`, { params }),
  markRead: (feedbackId: string) => api.post(`/feedback/${feedbackId}/read`),
  realTime: (data: any) => api.post('/feedback/real-time', data),
  errorAnalysis: (data: any) => api.post('/feedback/error-analysis', data),
};

// 报告API
export const reportAPI = {
  generate: (data: any) => api.post('/reports/generate', data),
  get: (reportId: string) => api.get(`/reports/${reportId}`),
  getLearnerReports: (learnerId: string, params?: any) => 
    api.get(`/learners/${learnerId}/reports`, { params }),
};

// 数据分析API
export const analyticsAPI = {
  trajectory: (learnerId: string, params?: any) => 
    api.get(`/analytics/trajectory/${learnerId}`, { params }),
  errors: (learnerId: string, params?: any) => 
    api.get(`/analytics/errors/${learnerId}`, { params }),
};

// 系统API
export const systemAPI = {
  info: () => api.get('/system/info'),
  health: () => api.get('/system/health'),
};

export const assessmentAPI = {
  learner: learnerAPI,
  evaluation: evaluationAPI,
  behavior: behaviorAPI,
  feedback: feedbackAPI,
  report: reportAPI,
  analytics: analyticsAPI,
  system: systemAPI,
};

export default api;
