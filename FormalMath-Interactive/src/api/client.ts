// ==================== API客户端配置 ====================

import axios, { AxiosInstance, AxiosRequestConfig, AxiosError } from 'axios';
import type { ApiResponse, ApiError } from '@types';

// API基础配置
const API_BASE_URL = import.meta.env.VITE_API_BASE_URL || '/api';
const API_TIMEOUT = 30000;

// 创建axios实例
const apiClient: AxiosInstance = axios.create({
  baseURL: API_BASE_URL,
  timeout: API_TIMEOUT,
  headers: {
    'Content-Type': 'application/json',
  },
});

// 请求拦截器
apiClient.interceptors.request.use(
  (config) => {
    // 添加认证token
    const token = localStorage.getItem('auth_token');
    if (token) {
      config.headers.Authorization = `Bearer ${token}`;
    }
    
    // 添加请求时间戳
    config.headers['X-Request-Time'] = new Date().toISOString();
    
    return config;
  },
  (error) => {
    return Promise.reject(error);
  }
);

// 响应拦截器
apiClient.interceptors.response.use(
  (response) => {
    return response;
  },
  (error: AxiosError<ApiError>) => {
    if (error.response) {
      // 处理特定HTTP错误
      switch (error.response.status) {
        case 401:
          // 未授权，清除token并重定向到登录页
          localStorage.removeItem('auth_token');
          window.location.href = '/login';
          break;
        case 403:
          console.error('访问被拒绝');
          break;
        case 404:
          console.error('资源不存在');
          break;
        case 500:
          console.error('服务器内部错误');
          break;
      }
    } else if (error.request) {
      console.error('网络请求失败，请检查网络连接');
    } else {
      console.error('请求配置错误:', error.message);
    }
    
    return Promise.reject(error);
  }
);

/**
 * 通用GET请求
 */
export async function get<T>(
  url: string,
  config?: AxiosRequestConfig
): Promise<ApiResponse<T>> {
  try {
    const response = await apiClient.get<ApiResponse<T>>(url, config);
    return response.data;
  } catch (error) {
    return handleApiError(error);
  }
}

/**
 * 通用POST请求
 */
export async function post<T>(
  url: string,
  data?: unknown,
  config?: AxiosRequestConfig
): Promise<ApiResponse<T>> {
  try {
    const response = await apiClient.post<ApiResponse<T>>(url, data, config);
    return response.data;
  } catch (error) {
    return handleApiError(error);
  }
}

/**
 * 通用PUT请求
 */
export async function put<T>(
  url: string,
  data?: unknown,
  config?: AxiosRequestConfig
): Promise<ApiResponse<T>> {
  try {
    const response = await apiClient.put<ApiResponse<T>>(url, data, config);
    return response.data;
  } catch (error) {
    return handleApiError(error);
  }
}

/**
 * 通用DELETE请求
 */
export async function del<T>(
  url: string,
  config?: AxiosRequestConfig
): Promise<ApiResponse<T>> {
  try {
    const response = await apiClient.delete<ApiResponse<T>>(url, config);
    return response.data;
  } catch (error) {
    return handleApiError(error);
  }
}

/**
 * 处理API错误
 */
function handleApiError(error: unknown): ApiResponse<never> {
  if (axios.isAxiosError(error)) {
    const axiosError = error as AxiosError<ApiError>;
    return {
      success: false,
      error: axiosError.response?.data || {
        code: 'NETWORK_ERROR',
        message: axiosError.message || '网络请求失败',
      },
      meta: { timestamp: new Date().toISOString() },
    };
  }
  
  return {
    success: false,
    error: {
      code: 'UNKNOWN_ERROR',
      message: error instanceof Error ? error.message : '未知错误',
    },
    meta: { timestamp: new Date().toISOString() },
  };
}

/**
 * 上传文件
 */
export async function uploadFile<T>(
  url: string,
  file: File,
  onProgress?: (progress: number) => void
): Promise<ApiResponse<T>> {
  const formData = new FormData();
  formData.append('file', file);
  
  try {
    const response = await apiClient.post<ApiResponse<T>>(url, formData, {
      headers: { 'Content-Type': 'multipart/form-data' },
      onUploadProgress: (progressEvent) => {
        if (onProgress && progressEvent.total) {
          const progress = Math.round((progressEvent.loaded * 100) / progressEvent.total);
          onProgress(progress);
        }
      },
    });
    return response.data;
  } catch (error) {
    return handleApiError(error);
  }
}

/**
 * 下载文件
 */
export async function downloadFile(
  url: string,
  filename?: string
): Promise<void> {
  try {
    const response = await apiClient.get(url, { responseType: 'blob' });
    const blob = new Blob([response.data]);
    const downloadUrl = window.URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = downloadUrl;
    link.download = filename || 'download';
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    window.URL.revokeObjectURL(downloadUrl);
  } catch (error) {
    console.error('下载失败:', error);
    throw error;
  }
}

export default apiClient;
