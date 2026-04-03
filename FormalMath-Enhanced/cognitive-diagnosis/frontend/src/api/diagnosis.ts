import apiClient from './client';
import { ApiResponse, DiagnosisSession, Question, SubmitAnswerResponse } from '../types';

export interface StartDiagnosisRequest {
  user_id: string;
  question_count?: number;
  target_levels?: number[];
}

export interface SubmitAnswerRequest {
  session_id: string;
  question_id: string;
  answer: any;
  time_spent: number;
  confidence?: number;
}

// 开始诊断
export const startDiagnosis = async (
  request: StartDiagnosisRequest
): Promise<ApiResponse<{ session_id: string; question_count: number; first_question: Question }>> => {
  const response = await apiClient.post('/api/diagnosis/start', request);
  return response.data;
};

// 提交答案
export const submitAnswer = async (
  request: SubmitAnswerRequest
): Promise<ApiResponse<SubmitAnswerResponse>> => {
  const response = await apiClient.post('/api/diagnosis/submit', request);
  return response.data;
};

// 获取会话状态
export const getSessionStatus = async (
  sessionId: string
): Promise<ApiResponse<DiagnosisSession>> => {
  const response = await apiClient.get(`/api/diagnosis/session/${sessionId}`);
  return response.data;
};

// 完成诊断
export const completeDiagnosis = async (
  sessionId: string
): Promise<ApiResponse<{ report_id: string }>> => {
  const response = await apiClient.post(`/api/diagnosis/complete/${sessionId}`);
  return response.data;
};
