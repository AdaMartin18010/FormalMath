import axios from 'axios'
import type { ApiResponse, Question, DiagnosisResult, LearningPath, UserProfile } from '../types'

const API_BASE_URL = import.meta.env.VITE_API_URL || '/api/v1'

const api = axios.create({
  baseURL: API_BASE_URL,
  headers: {
    'Content-Type': 'application/json'
  }
})

// 诊断相关API
export const diagnosisApi = {
  // 开始诊断
  start: (params: { question_count?: number; target_level?: number }) =>
    api.post<ApiResponse<{ test_id: string; questions: Question[]; time_limit: number }>>(
      '/diagnosis/start',
      params
    ),

  // 提交答案
  submit: (data: { test_id: string; responses: { question_id: string; answer: string; time_spent: number }[] }) =>
    api.post<ApiResponse<{ test_id: string; status: string; completed_count: number; total_count: number }>>(
      '/diagnosis/submit',
      data
    ),

  // 分析诊断
  analyze: (testId: string) =>
    api.post<ApiResponse<DiagnosisResult>>(`/diagnosis/analyze/${testId}`),

  // 获取结果
  getResult: (testId: string) =>
    api.get<ApiResponse<DiagnosisResult>>(`/diagnosis/${testId}/result`),

  // 获取题目列表
  getQuestions: (params?: { level?: number; branch?: string; limit?: number }) =>
    api.get<ApiResponse<{ total: number; questions: Question[] }>>('/questions', { params })
}

// 学生相关API
export const studentApi = {
  // 获取档案
  getProfile: (studentId: string) =>
    api.get<ApiResponse<UserProfile>>(`/students/${studentId}/profile`),

  // 获取学习路径
  getLearningPath: (studentId: string) =>
    api.get<ApiResponse<LearningPath>>(`/students/${studentId}/learning-path`),

  // 获取诊断历史
  getHistory: (studentId: string, limit?: number) =>
    api.get<ApiResponse<any[]>>(`/students/${studentId}/history`, { params: { limit } })
}

export default api
