// ==================== 笔记系统状态管理 ====================
import { create } from 'zustand';
import { persist, subscribeWithSelector } from 'zustand/middleware';
import type {
  Note,
  NoteFolder,
  NoteTag,
  NoteVersion,
  NoteSearchFilter,
  NoteSortOption,
  NoteSearchResult,
  NoteEditorState,
  NoteStatistics,
  NoteTemplate,
  NoteAIChatMessage,
} from '../types/notes';

// 笔记状态接口
interface NoteState {
  // ===== 笔记数据 =====
  notes: Note[];
  folders: NoteFolder[];
  tags: NoteTag[];
  templates: NoteTemplate[];
  currentFolder: NoteFolder | null;
  selectedNoteIds: string[];
  
  // ===== 编辑器状态 =====
  editor: NoteEditorState;
  
  // ===== 搜索状态 =====
  searchFilter: NoteSearchFilter;
  searchResults: NoteSearchResult[];
  sortOption: NoteSortOption;
  isSearching: boolean;
  
  // ===== AI助手状态 =====
  aiChatHistory: NoteAIChatMessage[];
  isAIProcessing: boolean;
  
  // ===== UI状态 =====
  sidebarOpen: boolean;
  folderTreeExpanded: string[];
  
  // ===== 统计数据 =====
  statistics: NoteStatistics | null;
}

// 笔记操作接口
interface NoteActions {
  // ===== 笔记CRUD =====
  setNotes: (notes: Note[]) => void;
  addNote: (note: Note) => void;
  updateNote: (id: string, updates: Partial<Note>) => void;
  deleteNote: (id: string) => void;
  selectNote: (note: Note | null) => void;
  toggleNoteSelection: (id: string) => void;
  clearSelection: () => void;
  
  // ===== 编辑器操作 =====
  updateEditorContent: (content: string) => void;
  updateEditorTitle: (title: string) => void;
  setEditorDirty: (isDirty: boolean) => void;
  setEditorSaving: (isSaving: boolean) => void;
  setEditorViewMode: (mode: 'edit' | 'preview' | 'split') => void;
  setSelectedText: (text: string | undefined) => void;
  toggleAutoSave: () => void;
  
  // ===== 文件夹操作 =====
  setFolders: (folders: NoteFolder[]) => void;
  addFolder: (folder: NoteFolder) => void;
  updateFolder: (id: string, updates: Partial<NoteFolder>) => void;
  deleteFolder: (id: string) => void;
  setCurrentFolder: (folder: NoteFolder | null) => void;
  toggleFolderExpanded: (folderId: string) => void;
  
  // ===== 标签操作 =====
  setTags: (tags: NoteTag[]) => void;
  addTag: (tag: NoteTag) => void;
  updateTag: (id: string, updates: Partial<NoteTag>) => void;
  deleteTag: (id: string) => void;
  
  // ===== 搜索操作 =====
  setSearchFilter: (filter: NoteSearchFilter) => void;
  setSearchResults: (results: NoteSearchResult[]) => void;
  setSortOption: (option: NoteSortOption) => void;
  setIsSearching: (isSearching: boolean) => void;
  clearSearch: () => void;
  
  // ===== AI助手操作 =====
  addAIChatMessage: (message: NoteAIChatMessage) => void;
  clearAIChatHistory: () => void;
  setAIProcessing: (isProcessing: boolean) => void;
  
  // ===== UI操作 =====
  toggleSidebar: () => void;
  setSidebarOpen: (open: boolean) => void;
  
  // ===== 统计操作 =====
  setStatistics: (stats: NoteStatistics) => void;
}

// 初始编辑器状态
const initialEditorState: NoteEditorState = {
  currentNote: null,
  isDirty: false,
  isSaving: false,
  autoSaveEnabled: true,
  viewMode: 'split',
};

// 创建笔记Store
export const useNoteStore = create<NoteState & NoteActions>()(
  subscribeWithSelector(
    persist(
      (set, get) => ({
        // ===== 初始状态 =====
        notes: [],
        folders: [],
        tags: [],
        templates: [],
        currentFolder: null,
        selectedNoteIds: [],
        editor: initialEditorState,
        searchFilter: {},
        searchResults: [],
        sortOption: 'updatedAt_desc',
        isSearching: false,
        aiChatHistory: [],
        isAIProcessing: false,
        sidebarOpen: true,
        folderTreeExpanded: [],
        statistics: null,
        
        // ===== 笔记CRUD =====
        setNotes: (notes) => set({ notes }),
        
        addNote: (note) => set((state) => ({
          notes: [note, ...state.notes],
          editor: {
            ...state.editor,
            currentNote: note,
            isDirty: false,
          },
        })),
        
        updateNote: (id, updates) => set((state) => ({
          notes: state.notes.map((n) =>
            n.id === id ? { ...n, ...updates, updatedAt: new Date().toISOString() } : n
          ),
          editor: state.editor.currentNote?.id === id
            ? { ...state.editor, currentNote: { ...state.editor.currentNote, ...updates } }
            : state.editor,
        })),
        
        deleteNote: (id) => set((state) => ({
          notes: state.notes.filter((n) => n.id !== id),
          selectedNoteIds: state.selectedNoteIds.filter((sid) => sid !== id),
          editor: state.editor.currentNote?.id === id
            ? { ...state.editor, currentNote: null }
            : state.editor,
        })),
        
        selectNote: (note) => set((state) => ({
          editor: {
            ...state.editor,
            currentNote: note,
            isDirty: false,
          },
        })),
        
        toggleNoteSelection: (id) => set((state) => ({
          selectedNoteIds: state.selectedNoteIds.includes(id)
            ? state.selectedNoteIds.filter((sid) => sid !== id)
            : [...state.selectedNoteIds, id],
        })),
        
        clearSelection: () => set({ selectedNoteIds: [] }),
        
        // ===== 编辑器操作 =====
        updateEditorContent: (content) => set((state) => ({
          editor: {
            ...state.editor,
            currentNote: state.editor.currentNote
              ? { ...state.editor.currentNote, content }
              : null,
            isDirty: true,
          },
        })),
        
        updateEditorTitle: (title) => set((state) => ({
          editor: {
            ...state.editor,
            currentNote: state.editor.currentNote
              ? { ...state.editor.currentNote, title }
              : null,
            isDirty: true,
          },
        })),
        
        setEditorDirty: (isDirty) => set((state) => ({
          editor: { ...state.editor, isDirty },
        })),
        
        setEditorSaving: (isSaving) => set((state) => ({
          editor: { ...state.editor, isSaving },
        })),
        
        setEditorViewMode: (viewMode) => set((state) => ({
          editor: { ...state.editor, viewMode },
        })),
        
        setSelectedText: (selectedText) => set((state) => ({
          editor: { ...state.editor, selectedText },
        })),
        
        toggleAutoSave: () => set((state) => ({
          editor: { ...state.editor, autoSaveEnabled: !state.editor.autoSaveEnabled },
        })),
        
        // ===== 文件夹操作 =====
        setFolders: (folders) => set({ folders }),
        
        addFolder: (folder) => set((state) => ({
          folders: [...state.folders, folder],
        })),
        
        updateFolder: (id, updates) => set((state) => ({
          folders: state.folders.map((f) =>
            f.id === id ? { ...f, ...updates, updatedAt: new Date().toISOString() } : f
          ),
        })),
        
        deleteFolder: (id) => set((state) => ({
          folders: state.folders.filter((f) => f.id !== id),
        })),
        
        setCurrentFolder: (currentFolder) => set({ currentFolder }),
        
        toggleFolderExpanded: (folderId) => set((state) => ({
          folderTreeExpanded: state.folderTreeExpanded.includes(folderId)
            ? state.folderTreeExpanded.filter((id) => id !== folderId)
            : [...state.folderTreeExpanded, folderId],
        })),
        
        // ===== 标签操作 =====
        setTags: (tags) => set({ tags }),
        
        addTag: (tag) => set((state) => ({
          tags: [...state.tags, tag],
        })),
        
        updateTag: (id, updates) => set((state) => ({
          tags: state.tags.map((t) => (t.id === id ? { ...t, ...updates } : t)),
        })),
        
        deleteTag: (id) => set((state) => ({
          tags: state.tags.filter((t) => t.id !== id),
        })),
        
        // ===== 搜索操作 =====
        setSearchFilter: (searchFilter) => set({ searchFilter }),
        
        setSearchResults: (searchResults) => set({ searchResults }),
        
        setSortOption: (sortOption) => set({ sortOption }),
        
        setIsSearching: (isSearching) => set({ isSearching }),
        
        clearSearch: () => set({
          searchFilter: {},
          searchResults: [],
          isSearching: false,
        }),
        
        // ===== AI助手操作 =====
        addAIChatMessage: (message) => set((state) => ({
          aiChatHistory: [...state.aiChatHistory, message],
        })),
        
        clearAIChatHistory: () => set({ aiChatHistory: [] }),
        
        setAIProcessing: (isAIProcessing) => set({ isAIProcessing }),
        
        // ===== UI操作 =====
        toggleSidebar: () => set((state) => ({ sidebarOpen: !state.sidebarOpen })),
        
        setSidebarOpen: (sidebarOpen) => set({ sidebarOpen }),
        
        // ===== 统计操作 =====
        setStatistics: (statistics) => set({ statistics }),
      }),
      {
        name: 'formalmath-notes-storage',
        partialize: (state) => ({
          editor: {
            autoSaveEnabled: state.editor.autoSaveEnabled,
            viewMode: state.editor.viewMode,
          },
          sidebarOpen: state.sidebarOpen,
          folderTreeExpanded: state.folderTreeExpanded,
          sortOption: state.sortOption,
        }),
      }
    )
  )
);

// 派生状态选择器
export const selectFilteredNotes = (state: NoteState & NoteActions): Note[] => {
  let filtered = [...state.notes];
  
  // 应用搜索过滤
  if (state.searchResults.length > 0) {
    const resultIds = new Set(state.searchResults.map((r) => r.note.id));
    filtered = filtered.filter((n) => resultIds.has(n.id));
  }
  
  // 应用类型过滤
  if (state.searchFilter.type) {
    filtered = filtered.filter((n) => n.type === state.searchFilter.type);
  }
  
  // 应用标签过滤
  if (state.searchFilter.tags && state.searchFilter.tags.length > 0) {
    filtered = filtered.filter((n) =>
      n.tags.some((t) => state.searchFilter.tags?.includes(t.id))
    );
  }
  
  // 应用状态过滤
  if (state.searchFilter.status) {
    filtered = filtered.filter((n) => n.status === state.searchFilter.status);
  }
  
  // 应用文件夹过滤
  if (state.currentFolder) {
    filtered = filtered.filter((n) => n.parentId === state.currentFolder?.id);
  }
  
  // 应用排序
  filtered.sort((a, b) => {
    switch (state.sortOption) {
      case 'updatedAt_desc':
        return new Date(b.updatedAt).getTime() - new Date(a.updatedAt).getTime();
      case 'updatedAt_asc':
        return new Date(a.updatedAt).getTime() - new Date(b.updatedAt).getTime();
      case 'createdAt_desc':
        return new Date(b.createdAt).getTime() - new Date(a.createdAt).getTime();
      case 'createdAt_asc':
        return new Date(a.createdAt).getTime() - new Date(b.createdAt).getTime();
      case 'title_asc':
        return a.title.localeCompare(b.title);
      case 'title_desc':
        return b.title.localeCompare(a.title);
      default:
        return 0;
    }
  });
  
  return filtered;
};

export const selectNotesByTag = (state: NoteState & NoteActions): Record<string, Note[]> => {
  const byTag: Record<string, Note[]> = {};
  state.tags.forEach((tag) => {
    byTag[tag.id] = state.notes.filter((n) => n.tags.some((t) => t.id === tag.id));
  });
  return byTag;
};

export const selectPinnedNotes = (state: NoteState & NoteActions): Note[] => {
  return state.notes.filter((n) => n.isPinned);
};

export const selectFavoriteNotes = (state: NoteState & NoteActions): Note[] => {
  return state.notes.filter((n) => n.isFavorite);
};
