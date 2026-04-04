// ==================== 笔记系统服务层 ====================
import axios from 'axios';
import type {
  Note,
  NoteFolder,
  NoteTag,
  NoteVersion,
  NoteSearchFilter,
  NoteSortOption,
  NoteSearchResult,
  NoteStatistics,
  NoteTemplate,
  NoteExportOptions,
  NoteImportResult,
  NoteAIRequest,
  NoteAIResponse,
  NoteShareSettings,
  NoteComment,
  ApiResponse,
  NoteAttachment,
} from '../types/notes';

const API_BASE_URL = import.meta.env.VITE_API_URL || 'http://localhost:3000/api';

const api = axios.create({
  baseURL: `${API_BASE_URL}/notes`,
  headers: {
    'Content-Type': 'application/json',
  },
  timeout: 30000,
});

// 请求拦截器
api.interceptors.request.use(
  (config) => {
    const token = localStorage.getItem('auth_token');
    if (token) {
      config.headers.Authorization = `Bearer ${token}`;
    }
    return config;
  },
  (error) => Promise.reject(error)
);

// ==================== 笔记CRUD操作 ====================

export const fetchNotes = async (
  folderId?: string,
  filters?: NoteSearchFilter,
  sort?: NoteSortOption
): Promise<ApiResponse<Note[]>> => {
  try {
    const response = await api.get('/', {
      params: {
        folderId,
        ...filters,
        sort,
      },
    });
    return response.data;
  } catch (error) {
    console.error('Failed to fetch notes:', error);
    throw error;
  }
};

export const fetchNoteById = async (id: string): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.get(`/${id}`);
    return response.data;
  } catch (error) {
    console.error(`Failed to fetch note ${id}:`, error);
    throw error;
  }
};

export const createNote = async (
  noteData: Partial<Note>
): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.post('/', {
      ...noteData,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
      version: 1,
    });
    return response.data;
  } catch (error) {
    console.error('Failed to create note:', error);
    throw error;
  }
};

export const updateNote = async (
  id: string,
  updates: Partial<Note>
): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.patch(`/${id}`, {
      ...updates,
      updatedAt: new Date().toISOString(),
    });
    return response.data;
  } catch (error) {
    console.error(`Failed to update note ${id}:`, error);
    throw error;
  }
};

export const deleteNote = async (id: string): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/${id}`);
    return response.data;
  } catch (error) {
    console.error(`Failed to delete note ${id}:`, error);
    throw error;
  }
};

export const batchDeleteNotes = async (ids: string[]): Promise<ApiResponse<void>> => {
  try {
    const response = await api.post('/batch-delete', { ids });
    return response.data;
  } catch (error) {
    console.error('Failed to batch delete notes:', error);
    throw error;
  }
};

// ==================== 笔记版本历史 ====================

export const fetchNoteVersions = async (noteId: string): Promise<ApiResponse<NoteVersion[]>> => {
  try {
    const response = await api.get(`/${noteId}/versions`);
    return response.data;
  } catch (error) {
    console.error(`Failed to fetch versions for note ${noteId}:`, error);
    throw error;
  }
};

export const restoreNoteVersion = async (
  noteId: string,
  versionId: string
): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.post(`/${noteId}/restore`, { versionId });
    return response.data;
  } catch (error) {
    console.error(`Failed to restore version ${versionId}:`, error);
    throw error;
  }
};

export const compareVersions = async (
  noteId: string,
  versionId1: string,
  versionId2: string
): Promise<ApiResponse<{ diff: string; additions: number; deletions: number }>> => {
  try {
    const response = await api.get(`/${noteId}/compare`, {
      params: { v1: versionId1, v2: versionId2 },
    });
    return response.data;
  } catch (error) {
    console.error('Failed to compare versions:', error);
    throw error;
  }
};

// ==================== 笔记搜索 ====================

export const searchNotes = async (
  query: string,
  filters?: NoteSearchFilter,
  options?: {
    fuzzy?: boolean;
    highlight?: boolean;
    limit?: number;
  }
): Promise<ApiResponse<NoteSearchResult[]>> => {
  try {
    const response = await api.get('/search', {
      params: {
        q: query,
        ...filters,
        ...options,
      },
    });
    return response.data;
  } catch (error) {
    console.error('Failed to search notes:', error);
    throw error;
  }
};

export const advancedSearch = async (
  filters: NoteSearchFilter,
  sort: NoteSortOption = 'updatedAt_desc',
  page: number = 1,
  pageSize: number = 20
): Promise<ApiResponse<{ results: NoteSearchResult[]; total: number }>> => {
  try {
    const response = await api.post('/search/advanced', {
      filters,
      sort,
      page,
      pageSize,
    });
    return response.data;
  } catch (error) {
    console.error('Failed to perform advanced search:', error);
    throw error;
  }
};

// ==================== 笔记标签管理 ====================

export const fetchTags = async (): Promise<ApiResponse<NoteTag[]>> => {
  try {
    const response = await api.get('/tags');
    return response.data;
  } catch (error) {
    console.error('Failed to fetch tags:', error);
    throw error;
  }
};

export const createTag = async (
  name: string,
  color: string
): Promise<ApiResponse<NoteTag>> => {
  try {
    const response = await api.post('/tags', { name, color });
    return response.data;
  } catch (error) {
    console.error('Failed to create tag:', error);
    throw error;
  }
};

export const updateTag = async (
  id: string,
  updates: Partial<NoteTag>
): Promise<ApiResponse<NoteTag>> => {
  try {
    const response = await api.patch(`/tags/${id}`, updates);
    return response.data;
  } catch (error) {
    console.error(`Failed to update tag ${id}:`, error);
    throw error;
  }
};

export const deleteTag = async (id: string): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/tags/${id}`);
    return response.data;
  } catch (error) {
    console.error(`Failed to delete tag ${id}:`, error);
    throw error;
  }
};

export const batchTagNotes = async (
  noteIds: string[],
  tagIds: string[],
  action: 'add' | 'remove'
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.post('/tags/batch', { noteIds, tagIds, action });
    return response.data;
  } catch (error) {
    console.error('Failed to batch tag notes:', error);
    throw error;
  }
};

// ==================== 文件夹管理 ====================

export const fetchFolders = async (): Promise<ApiResponse<NoteFolder[]>> => {
  try {
    const response = await api.get('/folders');
    return response.data;
  } catch (error) {
    console.error('Failed to fetch folders:', error);
    throw error;
  }
};

export const createFolder = async (
  name: string,
  parentId?: string,
  description?: string
): Promise<ApiResponse<NoteFolder>> => {
  try {
    const response = await api.post('/folders', { name, parentId, description });
    return response.data;
  } catch (error) {
    console.error('Failed to create folder:', error);
    throw error;
  }
};

export const updateFolder = async (
  id: string,
  updates: Partial<NoteFolder>
): Promise<ApiResponse<NoteFolder>> => {
  try {
    const response = await api.patch(`/folders/${id}`, updates);
    return response.data;
  } catch (error) {
    console.error(`Failed to update folder ${id}:`, error);
    throw error;
  }
};

export const deleteFolder = async (
  id: string,
  deleteNotes: boolean = false
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/folders/${id}`, {
      params: { deleteNotes },
    });
    return response.data;
  } catch (error) {
    console.error(`Failed to delete folder ${id}:`, error);
    throw error;
  }
};

export const moveNotesToFolder = async (
  noteIds: string[],
  folderId: string | null
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.post('/folders/move', { noteIds, folderId });
    return response.data;
  } catch (error) {
    console.error('Failed to move notes:', error);
    throw error;
  }
};

// ==================== AI助手服务 ====================

export const analyzeNote = async (noteId: string): Promise<ApiResponse<Note['aiAnalysis']>> => {
  try {
    const response = await api.post(`/${noteId}/analyze`);
    return response.data;
  } catch (error) {
    console.error('Failed to analyze note:', error);
    throw error;
  }
};

export const aiAssistant = async (request: NoteAIRequest): Promise<ApiResponse<NoteAIResponse>> => {
  try {
    const response = await api.post('/ai/assist', request);
    return response.data;
  } catch (error) {
    console.error('AI assistant request failed:', error);
    throw error;
  }
};

export const suggestConceptLinks = async (
  noteId: string
): Promise<ApiResponse<Note['aiAnalysis']['conceptLinks']>> => {
  try {
    const response = await api.get(`/${noteId}/suggest-links`);
    return response.data;
  } catch (error) {
    console.error('Failed to suggest concept links:', error);
    throw error;
  }
};

export const generateNoteSummary = async (
  noteId: string,
  maxLength?: number
): Promise<ApiResponse<string>> => {
  try {
    const response = await api.post(`/${noteId}/summarize`, { maxLength });
    return response.data;
  } catch (error) {
    console.error('Failed to generate summary:', error);
    throw error;
  }
};

export const autoTagNote = async (noteId: string): Promise<ApiResponse<string[]>> => {
  try {
    const response = await api.post(`/${noteId}/auto-tag`);
    return response.data;
  } catch (error) {
    console.error('Failed to auto-tag note:', error);
    throw error;
  }
};

// ==================== 笔记分享 ====================

export const shareNote = async (
  noteId: string,
  settings: Partial<NoteShareSettings>
): Promise<ApiResponse<NoteShareSettings>> => {
  try {
    const response = await api.post(`/${noteId}/share`, settings);
    return response.data;
  } catch (error) {
    console.error('Failed to share note:', error);
    throw error;
  }
};

export const unshareNote = async (noteId: string): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/${noteId}/share`);
    return response.data;
  } catch (error) {
    console.error('Failed to unshare note:', error);
    throw error;
  }
};

export const fetchSharedNote = async (shareLink: string): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.get(`/shared/${shareLink}`);
    return response.data;
  } catch (error) {
    console.error('Failed to fetch shared note:', error);
    throw error;
  }
};

// ==================== 笔记评论 ====================

export const fetchNoteComments = async (noteId: string): Promise<ApiResponse<NoteComment[]>> => {
  try {
    const response = await api.get(`/${noteId}/comments`);
    return response.data;
  } catch (error) {
    console.error('Failed to fetch comments:', error);
    throw error;
  }
};

export const addComment = async (
  noteId: string,
  content: string,
  parentId?: string
): Promise<ApiResponse<NoteComment>> => {
  try {
    const response = await api.post(`/${noteId}/comments`, { content, parentId });
    return response.data;
  } catch (error) {
    console.error('Failed to add comment:', error);
    throw error;
  }
};

export const deleteComment = async (
  noteId: string,
  commentId: string
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/${noteId}/comments/${commentId}`);
    return response.data;
  } catch (error) {
    console.error('Failed to delete comment:', error);
    throw error;
  }
};

// ==================== 笔记导入导出 ====================

export const exportNotes = async (
  noteIds: string[],
  options: NoteExportOptions
): Promise<Blob> => {
  try {
    const response = await api.post('/export', { noteIds, options }, {
      responseType: 'blob',
    });
    return response.data;
  } catch (error) {
    console.error('Failed to export notes:', error);
    throw error;
  }
};

export const importNotes = async (
  file: File,
  folderId?: string
): Promise<ApiResponse<NoteImportResult>> => {
  try {
    const formData = new FormData();
    formData.append('file', file);
    if (folderId) formData.append('folderId', folderId);
    
    const response = await api.post('/import', formData, {
      headers: { 'Content-Type': 'multipart/form-data' },
    });
    return response.data;
  } catch (error) {
    console.error('Failed to import notes:', error);
    throw error;
  }
};

// ==================== 笔记模板 ====================

export const fetchTemplates = async (): Promise<ApiResponse<NoteTemplate[]>> => {
  try {
    const response = await api.get('/templates');
    return response.data;
  } catch (error) {
    console.error('Failed to fetch templates:', error);
    throw error;
  }
};

export const createNoteFromTemplate = async (
  templateId: string,
  folderId?: string
): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.post(`/templates/${templateId}/create`, { folderId });
    return response.data;
  } catch (error) {
    console.error('Failed to create note from template:', error);
    throw error;
  }
};

// ==================== 笔记统计 ====================

export const fetchNoteStatistics = async (): Promise<ApiResponse<NoteStatistics>> => {
  try {
    const response = await api.get('/statistics');
    return response.data;
  } catch (error) {
    console.error('Failed to fetch statistics:', error);
    throw error;
  }
};

// ==================== 附件上传 ====================

export const uploadAttachment = async (
  noteId: string,
  file: File
): Promise<ApiResponse<NoteAttachment>> => {
  try {
    const formData = new FormData();
    formData.append('file', file);
    
    const response = await api.post(`/${noteId}/attachments`, formData, {
      headers: { 'Content-Type': 'multipart/form-data' },
    });
    return response.data;
  } catch (error) {
    console.error('Failed to upload attachment:', error);
    throw error;
  }
};

export const deleteAttachment = async (
  noteId: string,
  attachmentId: string
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/${noteId}/attachments/${attachmentId}`);
    return response.data;
  } catch (error) {
    console.error('Failed to delete attachment:', error);
    throw error;
  }
};

// ==================== 知识图谱关联 ====================

export const linkNoteToConcept = async (
  noteId: string,
  conceptId: string,
  relationType: Note['aiAnalysis']['conceptLinks'][0]['relationType']
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.post(`/${noteId}/concepts`, { conceptId, relationType });
    return response.data;
  } catch (error) {
    console.error('Failed to link note to concept:', error);
    throw error;
  }
};

export const unlinkNoteFromConcept = async (
  noteId: string,
  conceptId: string
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.delete(`/${noteId}/concepts/${conceptId}`);
    return response.data;
  } catch (error) {
    console.error('Failed to unlink note from concept:', error);
    throw error;
  }
};

export const fetchRelatedNotes = async (noteId: string): Promise<ApiResponse<Note[]>> => {
  try {
    const response = await api.get(`/${noteId}/related`);
    return response.data;
  } catch (error) {
    console.error('Failed to fetch related notes:', error);
    throw error;
  }
};

// ==================== 自动保存 ====================

export const autoSaveNote = async (
  id: string,
  content: string,
  title: string
): Promise<ApiResponse<Note>> => {
  try {
    const response = await api.post(`/${id}/autosave`, {
      content,
      title,
      timestamp: new Date().toISOString(),
    });
    return response.data;
  } catch (error) {
    console.error('Auto-save failed:', error);
    throw error;
  }
};

// ==================== 笔记收藏和置顶 ====================

export const toggleNoteFavorite = async (
  noteId: string,
  isFavorite: boolean
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.patch(`/${noteId}/favorite`, { isFavorite });
    return response.data;
  } catch (error) {
    console.error('Failed to toggle favorite:', error);
    throw error;
  }
};

export const toggleNotePinned = async (
  noteId: string,
  isPinned: boolean
): Promise<ApiResponse<void>> => {
  try {
    const response = await api.patch(`/${noteId}/pinned`, { isPinned });
    return response.data;
  } catch (error) {
    console.error('Failed to toggle pinned:', error);
    throw error;
  }
};
