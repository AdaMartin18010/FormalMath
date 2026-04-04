// ==================== 智能笔记系统类型定义 ====================

// 笔记类型
export type NoteType = 'concept' | 'theorem' | 'proof' | 'example' | 'exercise' | 'general';

// 笔记状态
export type NoteStatus = 'draft' | 'published' | 'archived' | 'shared';

// 笔记标签
export interface NoteTag {
  id: string;
  name: string;
  color: string;
  count?: number;
}

// 笔记版本历史
export interface NoteVersion {
  id: string;
  noteId: string;
  version: number;
  content: string;
  title: string;
  createdAt: string;
  createdBy: string;
  changeSummary?: string;
}

// 笔记附件
export interface NoteAttachment {
  id: string;
  name: string;
  type: string;
  size: number;
  url: string;
  uploadedAt: string;
}

// 知识图谱关联
export interface NoteConceptLink {
  conceptId: string;
  conceptName: string;
  relationType: 'defines' | 'explains' | 'applies' | 'references' | 'extends';
  relevanceScore: number;
}

// AI分析结果
export interface NoteAIAnalysis {
  summary?: string;
  keyConcepts: string[];
  suggestedTags: string[];
  relatedNotes: string[];
  difficulty?: 'beginner' | 'intermediate' | 'advanced';
  estimatedReadTime?: number;
  conceptLinks: NoteConceptLink[];
  generatedAt: string;
}

// AI助手会话
export interface NoteAIChatMessage {
  id: string;
  role: 'user' | 'assistant' | 'system';
  content: string;
  timestamp: string;
  context?: {
    selectedText?: string;
    noteContext?: string;
  };
}

// 笔记分享设置
export interface NoteShareSettings {
  isPublic: boolean;
  shareLink?: string;
  password?: string;
  expiresAt?: string;
  allowComments: boolean;
  allowEdit: boolean;
  viewCount: number;
}

// 笔记评论
export interface NoteComment {
  id: string;
  noteId: string;
  content: string;
  author: {
    id: string;
    name: string;
    avatar?: string;
  };
  createdAt: string;
  updatedAt?: string;
  parentId?: string;
  replies?: NoteComment[];
}

// 笔记搜索过滤器
export interface NoteSearchFilter {
  query?: string;
  tags?: string[];
  type?: NoteType;
  status?: NoteStatus;
  dateRange?: {
    start: string;
    end: string;
  };
  conceptIds?: string[];
  author?: string;
}

// 笔记排序选项
export type NoteSortOption = 
  | 'updatedAt_desc'
  | 'updatedAt_asc'
  | 'createdAt_desc'
  | 'createdAt_asc'
  | 'title_asc'
  | 'title_desc';

// 核心笔记接口
export interface Note {
  id: string;
  title: string;
  content: string;
  type: NoteType;
  status: NoteStatus;
  tags: NoteTag[];
  author: {
    id: string;
    name: string;
    avatar?: string;
  };
  createdAt: string;
  updatedAt: string;
  version: number;
  wordCount: number;
  attachments?: NoteAttachment[];
  aiAnalysis?: NoteAIAnalysis;
  shareSettings?: NoteShareSettings;
  parentId?: string; // 用于笔记嵌套
  children?: Note[];
  isPinned?: boolean;
  isFavorite?: boolean;
}

// 笔记文件夹
export interface NoteFolder {
  id: string;
  name: string;
  description?: string;
  parentId?: string;
  children?: NoteFolder[];
  noteCount: number;
  createdAt: string;
  updatedAt: string;
}

// 笔记编辑器状态
export interface NoteEditorState {
  currentNote: Note | null;
  isDirty: boolean;
  isSaving: boolean;
  autoSaveEnabled: boolean;
  lastSavedAt?: string;
  selectedText?: string;
  cursorPosition?: {
    line: number;
    ch: number;
  };
  viewMode: 'edit' | 'preview' | 'split';
}

// 笔记搜索结果
export interface NoteSearchResult {
  note: Note;
  highlights: {
    title?: string;
    content?: string;
  };
  relevanceScore: number;
}

// 笔记统计
export interface NoteStatistics {
  totalNotes: number;
  totalWords: number;
  notesByType: Record<NoteType, number>;
  notesByTag: Record<string, number>;
  recentActivity: {
    date: string;
    notesCreated: number;
    notesUpdated: number;
  }[];
  mostUsedTags: NoteTag[];
  favoriteNotes: Note[];
}

// 笔记导出选项
export interface NoteExportOptions {
  format: 'markdown' | 'pdf' | 'html' | 'latex';
  includeMetadata?: boolean;
  includeComments?: boolean;
  includeHistory?: boolean;
  template?: string;
}

// 笔记导入结果
export interface NoteImportResult {
  success: boolean;
  importedCount: number;
  failedCount: number;
  errors: string[];
  importedNotes: Note[];
}

// AI助手请求类型
export interface NoteAIRequest {
  type: 'summarize' | 'explain' | 'expand' | 'relate' | 'suggest' | 'quiz' | 'translate';
  content: string;
  context?: {
    noteId?: string;
    selectedText?: string;
    conceptId?: string;
  };
  options?: Record<string, unknown>;
}

// AI助手响应
export interface NoteAIResponse {
  success: boolean;
  result: string;
  suggestedEdits?: {
    range: { start: number; end: number };
    replacement: string;
    explanation: string;
  }[];
  followUpQuestions?: string[];
  relatedConcepts?: NoteConceptLink[];
  error?: string;
}

// 笔记模板
export interface NoteTemplate {
  id: string;
  name: string;
  description: string;
  type: NoteType;
  content: string;
  defaultTags: string[];
  icon?: string;
}
