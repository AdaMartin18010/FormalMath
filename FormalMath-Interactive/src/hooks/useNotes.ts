// ==================== 笔记系统自定义Hook ====================
import { useCallback, useEffect, useState } from 'react';
import { useNoteStore } from '../stores/noteStore';
import {
  fetchNotes,
  createNote,
  updateNote,
  deleteNote,
  searchNotes,
  fetchTags,
  fetchFolders,
  fetchTemplates,
  createNoteFromTemplate,
  analyzeNote,
  generateNoteSummary,
  autoTagNote,
  suggestConceptLinks,
  shareNote,
  unshareNote,
  exportNotes,
  importNotes,
} from '../services/noteService';
import type {
  Note,
  NoteType,
  NoteSearchFilter,
  NoteSortOption,
  NoteTemplate,
  NoteExportOptions,
  NoteShareSettings,
} from '../types/notes';

// ==================== 笔记列表Hook ====================
export const useNotesList = (folderId?: string) => {
  const { notes, setNotes, isSearching } = useNoteStore();
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  const loadNotes = useCallback(async () => {
    setIsLoading(true);
    setError(null);
    try {
      const response = await fetchNotes(folderId);
      if (response.success && response.data) {
        setNotes(response.data);
      }
    } catch (err) {
      setError(err as Error);
    } finally {
      setIsLoading(false);
    }
  }, [folderId, setNotes]);

  useEffect(() => {
    loadNotes();
  }, [loadNotes]);

  return { notes, isLoading, error, refetch: loadNotes };
};

// ==================== 笔记CRUD Hook ====================
export const useNoteCRUD = () => {
  const { addNote: addToStore, updateNote: updateInStore, deleteNote: deleteFromStore } = useNoteStore();
  const [isLoading, setIsLoading] = useState(false);

  const createNewNote = useCallback(async (data: Partial<Note>) => {
    setIsLoading(true);
    try {
      const response = await createNote(data);
      if (response.success && response.data) {
        addToStore(response.data);
        return response.data;
      }
      return null;
    } finally {
      setIsLoading(false);
    }
  }, [addToStore]);

  const updateExistingNote = useCallback(async (id: string, updates: Partial<Note>) => {
    setIsLoading(true);
    try {
      const response = await updateNote(id, updates);
      if (response.success && response.data) {
        updateInStore(id, updates);
        return response.data;
      }
      return null;
    } finally {
      setIsLoading(false);
    }
  }, [updateInStore]);

  const deleteExistingNote = useCallback(async (id: string) => {
    setIsLoading(true);
    try {
      await deleteNote(id);
      deleteFromStore(id);
      return true;
    } catch {
      return false;
    } finally {
      setIsLoading(false);
    }
  }, [deleteFromStore]);

  return {
    createNewNote,
    updateExistingNote,
    deleteExistingNote,
    isLoading,
  };
};

// ==================== 笔记搜索Hook ====================
export const useNoteSearch = () => {
  const { setSearchResults, setIsSearching } = useNoteStore();
  const [isLoading, setIsLoading] = useState(false);

  const search = useCallback(async (
    query: string,
    filters?: NoteSearchFilter,
    options?: { fuzzy?: boolean; highlight?: boolean; limit?: number }
  ) => {
    if (!query.trim() && !filters) {
      setSearchResults([]);
      return [];
    }

    setIsLoading(true);
    setIsSearching(true);
    try {
      const response = await searchNotes(query, filters, options);
      if (response.success && response.data) {
        setSearchResults(response.data);
        return response.data;
      }
      return [];
    } catch (error) {
      console.error('Search error:', error);
      return [];
    } finally {
      setIsLoading(false);
      setIsSearching(false);
    }
  }, [setSearchResults, setIsSearching]);

  return { search, isLoading };
};

// ==================== 笔记模板Hook ====================
export const useNoteTemplates = () => {
  const [templates, setTemplates] = useState<NoteTemplate[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  const loadTemplates = useCallback(async () => {
    setIsLoading(true);
    try {
      const response = await fetchTemplates();
      if (response.success && response.data) {
        setTemplates(response.data);
      }
    } catch (error) {
      console.error('Failed to load templates:', error);
    } finally {
      setIsLoading(false);
    }
  }, []);

  const createFromTemplate = useCallback(async (templateId: string, folderId?: string) => {
    setIsLoading(true);
    try {
      const response = await createNoteFromTemplate(templateId, folderId);
      return response.success ? response.data : null;
    } catch (error) {
      console.error('Failed to create from template:', error);
      return null;
    } finally {
      setIsLoading(false);
    }
  }, []);

  useEffect(() => {
    loadTemplates();
  }, [loadTemplates]);

  return { templates, isLoading, loadTemplates, createFromTemplate };
};

// ==================== AI助手Hook ====================
export const useNoteAI = () => {
  const [isProcessing, setIsProcessing] = useState(false);

  const summarize = useCallback(async (noteId: string, maxLength?: number) => {
    setIsProcessing(true);
    try {
      const response = await generateNoteSummary(noteId, maxLength);
      return response.success ? response.data : null;
    } finally {
      setIsProcessing(false);
    }
  }, []);

  const analyze = useCallback(async (noteId: string) => {
    setIsProcessing(true);
    try {
      const response = await analyzeNote(noteId);
      return response.success ? response.data : null;
    } finally {
      setIsProcessing(false);
    }
  }, []);

  const suggestTags = useCallback(async (noteId: string) => {
    setIsProcessing(true);
    try {
      const response = await autoTagNote(noteId);
      return response.success ? response.data : null;
    } finally {
      setIsProcessing(false);
    }
  }, []);

  const suggestLinks = useCallback(async (noteId: string) => {
    setIsProcessing(true);
    try {
      const response = await suggestConceptLinks(noteId);
      return response.success ? response.data : null;
    } finally {
      setIsProcessing(false);
    }
  }, []);

  return {
    summarize,
    analyze,
    suggestTags,
    suggestLinks,
    isProcessing,
  };
};

// ==================== 笔记分享Hook ====================
export const useNoteShare = () => {
  const [isLoading, setIsLoading] = useState(false);

  const share = useCallback(async (noteId: string, settings: Partial<NoteShareSettings>) => {
    setIsLoading(true);
    try {
      const response = await shareNote(noteId, settings);
      return response.success ? response.data : null;
    } finally {
      setIsLoading(false);
    }
  }, []);

  const unshare = useCallback(async (noteId: string) => {
    setIsLoading(true);
    try {
      await unshareNote(noteId);
      return true;
    } catch {
      return false;
    } finally {
      setIsLoading(false);
    }
  }, []);

  return { share, unshare, isLoading };
};

// ==================== 笔记导入导出Hook ====================
export const useNoteImportExport = () => {
  const [isLoading, setIsLoading] = useState(false);
  const [progress, setProgress] = useState(0);

  const exportNote = useCallback(async (noteIds: string[], options: NoteExportOptions) => {
    setIsLoading(true);
    try {
      const blob = await exportNotes(noteIds, options);
      const url = window.URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `notes-export-${new Date().toISOString().split('T')[0]}.${options.format}`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      window.URL.revokeObjectURL(url);
      return true;
    } catch (error) {
      console.error('Export failed:', error);
      return false;
    } finally {
      setIsLoading(false);
    }
  }, []);

  const importNote = useCallback(async (file: File, folderId?: string) => {
    setIsLoading(true);
    try {
      const response = await importNotes(file, folderId);
      return response.success ? response.data : null;
    } catch (error) {
      console.error('Import failed:', error);
      return null;
    } finally {
      setIsLoading(false);
    }
  }, []);

  return { exportNote, importNote, isLoading, progress };
};

// ==================== 自动保存Hook ====================
export const useNoteAutoSave = (
  noteId: string,
  content: string,
  title: string,
  enabled: boolean = true,
  interval: number = 3000
) => {
  const [lastSaved, setLastSaved] = useState<Date | null>(null);
  const [isSaving, setIsSaving] = useState(false);

  useEffect(() => {
    if (!enabled || !noteId) return;

    const timer = setTimeout(async () => {
      setIsSaving(true);
      try {
        // 这里应该调用自动保存API
        // await autoSaveNote(noteId, content, title);
        setLastSaved(new Date());
      } catch (error) {
        console.error('Auto-save failed:', error);
      } finally {
        setIsSaving(false);
      }
    }, interval);

    return () => clearTimeout(timer);
  }, [noteId, content, title, enabled, interval]);

  return { lastSaved, isSaving };
};

// ==================== 综合笔记Hook ====================
export const useNotes = () => {
  const noteStore = useNoteStore();
  const notesList = useNotesList();
  const noteCRUD = useNoteCRUD();
  const noteSearch = useNoteSearch();
  const templates = useNoteTemplates();
  const ai = useNoteAI();
  const share = useNoteShare();
  const importExport = useNoteImportExport();

  return {
    // Store
    ...noteStore,
    
    // 列表
    ...notesList,
    
    // CRUD
    ...noteCRUD,
    
    // 搜索
    ...noteSearch,
    
    // 模板
    ...templates,
    
    // AI
    ...ai,
    
    // 分享
    ...share,
    
    // 导入导出
    ...importExport,
  };
};

export default useNotes;
