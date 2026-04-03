import apiClient from './client';
import { ApiResponse, DiagnosisReport } from '../types';

// 获取用户的所有报告
export const getUserReports = async (
  userId: string,
  limit: number = 10,
  offset: number = 0
): Promise<ApiResponse<DiagnosisReport[]>> => {
  const response = await apiClient.get(`/api/reports/user/${userId}?limit=${limit}&offset=${offset}`);
  return response.data;
};

// 获取单个报告
export const getReportById = async (
  reportId: string
): Promise<ApiResponse<DiagnosisReport>> => {
  const response = await apiClient.get(`/api/reports/${reportId}`);
  return response.data;
};

// 获取报告摘要
export const getReportSummary = async (
  reportId: string
): Promise<ApiResponse<any>> => {
  const response = await apiClient.get(`/api/reports/${reportId}/summary`);
  return response.data;
};

// 对比报告
export const compareReports = async (
  reportId: string,
  compareWith?: string
): Promise<ApiResponse<any>> => {
  const params = compareWith ? `?compare_with=${compareWith}` : '';
  const response = await apiClient.get(`/api/reports/${reportId}/comparison${params}`);
  return response.data;
};
