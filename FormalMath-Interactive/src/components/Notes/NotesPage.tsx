// ==================== 笔记系统主页面 ====================
import React, { useEffect, useState, useCallback } from 'react';
import { useNoteStore } from '../../stores/noteStore';
import { fetchNotes, createNote, fetchTags, fetchFolders, fetchNoteStatistics } from '../../services/noteService';
import { NoteEditor } from './NoteEditor';
import { NoteList } from './NoteList';
import { NoteSearch } from './NoteSearch';
import { NoteAIAssistant } from './NoteAIAssistant';
import { NoteShare } from './NoteShare';
import { NoteConceptGraph } from './NoteConceptGraph';
import type { Note, NoteType } from '../../types/notes';
import {
  Plus,
  FileText,
  Search,
  Sparkles,
  Share2,
  Network,
  LayoutGrid,
  List,
  MoreVertical,
  Folder,
  Tag,
  Star,
  Clock,
  Trash2,
  Archive,
  Settings,
  ChevronLeft,
  ChevronRight,
} from 'lucide-react';

// 视图模式
 type ViewMode = 'list' | 'grid' | 'split';

// 侧边栏标签
 type SidebarTab = 'all' | 'favorites' | 'recent' | 'trash' | 'archive';

export const NotesPage: React.FC = () => {
  const [viewMode, setViewMode] = useState<ViewMode>('split');
  const [activeTab, setActiveTab] = useState<SidebarTab>('all');
  const [showSidebar, setShowSidebar] = useState(true);
  const [showAIAssistant, setShowAIAssistant] = useState(true);
  const [showSharePanel, setShowSharePanel] = useState(false);
  const [showConceptGraph, setShowConceptGraph] = useState(false);
  const [isLoading, setIsLoading] = useState(true);
  const [selectedNoteId, setSelectedNoteId] = useState<string | undefined>();

  const {
    notes,
    setNotes,
    tags,
    setTags,
    folders,
    setFolders,
    statistics,
    setStatistics,
    addNote,
    selectNote,
    editor,
  } = useNoteStore();

  const { currentNote } = editor;

  // 初始化加载数据
  useEffect(() => {
    const loadData = async () => {
      setIsLoading(true);
      try {
        const [notesRes, tagsRes, foldersRes, statsRes] = await Promise.all([
          fetchNotes(),
          fetchTags(),
          fetchFolders(),
          fetchNoteStatistics(),
        ]);

        if (notesRes.success) setNotes(notesRes.data || []);
        if (tagsRes.success) setTags(tagsRes.data || []);
        if (foldersRes.success) setFolders(foldersRes.data || []);
        if (statsRes.success && statsRes.data) setStatistics(statsRes.data);
      } catch (error) {
        console.error('Failed to load notes data:', error);
      } finally {
        setIsLoading(false);
      }
    };

    loadData();
  }, [setNotes, setTags, setFolders, setStatistics]);

  // 创建新笔记
  const handleCreateNote = useCallback(async (type: NoteType = 'general') => {
    try {
      const newNote: Partial<Note> = {
        title: '未命名笔记',
        content: '',
        type,
        status: 'draft',
        tags: [],
        author: {
          id: 'current-user',
          name: '当前用户',
        },
        wordCount: 0,
        isPinned: false,
        isFavorite: false,
      };

      const response = await createNote(newNote);
      if (response.success && response.data) {
        addNote(response.data);
        setSelectedNoteId(response.data.id);
      }
    } catch (error) {
      console.error('Failed to create note:', error);
    }
  }, [addNote]);

  // 处理笔记选择
  const handleNoteSelect = useCallback((note: Note) => {
    setSelectedNoteId(note.id);
  }, []);

  // 过滤笔记
  const getFilteredNotes = () => {
    switch (activeTab) {
      case 'favorites':
        return notes.filter((n) => n.isFavorite);
      case 'recent':
        return notes
          .slice()
          .sort((a, b) => new Date(b.updatedAt).getTime() - new Date(a.updatedAt).getTime())
          .slice(0, 10);
      case 'trash':
        return notes.filter((n) => n.status === 'archived');
      case 'archive':
        return notes.filter((n) => n.status === 'archived');
      default:
        return notes;
    }
  };

  if (isLoading) {
    return (
      <div className="flex items-center justify-center h-screen bg-gray-50">
        <div className="text-center">
          <div className="w-12 h-12 border-4 border-blue-200 border-t-blue-500 rounded-full animate-spin mx-auto mb-4" />
          <p className="text-gray-500">加载笔记中...</p>
        </div>
      </div>
    );
  }

  return (
    <div className="h-screen bg-gray-50 flex overflow-hidden">
      {/* 侧边栏 */}
      {showSidebar && (
        <aside className="w-64 bg-white border-r border-gray-200 flex flex-col">
          {/* Logo区域 */}
          <div className="px-4 py-4 border-b border-gray-200">
            <div className="flex items-center">
              <div className="w-8 h-8 bg-gradient-to-br from-blue-500 to-purple-500 rounded-lg flex items-center justify-center mr-3">
                <FileText className="w-5 h-5 text-white" />
              </div>
              <div>
                <h1 className="font-bold text-gray-800">智能笔记</h1>
                <p className="text-xs text-gray-400">AI辅助学习</p>
              </div>
            </div>
          </div>

          {/* 新建笔记按钮 */}
          <div className="p-4">
            <button
              onClick={() => handleCreateNote()}
              className="
                w-full flex items-center justify-center px-4 py-3
                bg-blue-500 text-white rounded-xl
                hover:bg-blue-600 transition-colors
                shadow-sm hover:shadow-md
              "
            >
              <Plus className="w-5 h-5 mr-2" />
              新建笔记
            </button>
          </div>

          {/* 导航菜单 */}
          <nav className="flex-1 overflow-y-auto px-3 space-y-1">
            <button
              onClick={() => setActiveTab('all')}
              className={`
                w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors
                ${activeTab === 'all'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
                }
              `}
            >
              <FileText className="w-4 h-4 mr-3" />
              全部笔记
              <span className="ml-auto text-xs text-gray-400">{notes.length}</span>
            </button>
            <button
              onClick={() => setActiveTab('favorites')}
              className={`
                w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors
                ${activeTab === 'favorites'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
                }
              `}
            >
              <Star className="w-4 h-4 mr-3" />
              收藏笔记
              <span className="ml-auto text-xs text-gray-400">
                {notes.filter((n) => n.isFavorite).length}
              </span>
            </button>
            <button
              onClick={() => setActiveTab('recent')}
              className={`
                w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors
                ${activeTab === 'recent'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
                }
              `}
            >
              <Clock className="w-4 h-4 mr-3" />
              最近编辑
            </button>
            <button
              onClick={() => setActiveTab('archive')}
              className={`
                w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors
                ${activeTab === 'archive'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
                }
              `}
            >
              <Archive className="w-4 h-4 mr-3" />
              归档笔记
            </button>

            <div className="pt-4 pb-2">
              <h3 className="px-3 text-xs font-medium text-gray-400 uppercase tracking-wider">
                标签
              </h3>
            </div>
            {tags.slice(0, 8).map((tag) => (
              <button
                key={tag.id}
                className="w-full flex items-center px-3 py-2 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
              >
                <span
                  className="w-2 h-2 rounded-full mr-3"
                  style={{ backgroundColor: tag.color }}
                />
                {tag.name}
                <span className="ml-auto text-xs text-gray-400">{tag.count || 0}</span>
              </button>
            ))}

            <div className="pt-4 pb-2">
              <h3 className="px-3 text-xs font-medium text-gray-400 uppercase tracking-wider">
                文件夹
              </h3>
            </div>
            {folders.slice(0, 5).map((folder) => (
              <button
                key={folder.id}
                className="w-full flex items-center px-3 py-2 text-sm text-gray-600 hover:bg-gray-100 rounded-lg transition-colors"
              >
                <Folder className="w-4 h-4 mr-3" />
                {folder.name}
                <span className="ml-auto text-xs text-gray-400">{folder.noteCount}</span>
              </button>
            ))}
          </nav>

          {/* 底部统计 */}
          {statistics && (
            <div className="p-4 border-t border-gray-200">
              <div className="grid grid-cols-2 gap-3 text-center">
                <div>
                  <div className="text-lg font-semibold text-gray-800">
                    {statistics.totalNotes}
                  </div>
                  <div className="text-xs text-gray-400">笔记</div>
                </div>
                <div>
                  <div className="text-lg font-semibold text-gray-800">
                    {Math.round(statistics.totalWords / 1000)}k
                  </div>
                  <div className="text-xs text-gray-400">字数</div>
                </div>
              </div>
            </div>
          )}
        </aside>
      )}

      {/* 主内容区 */}
      <main className="flex-1 flex flex-col min-w-0">
        {/* 顶部工具栏 */}
        <header className="h-14 bg-white border-b border-gray-200 flex items-center justify-between px-4">
          <div className="flex items-center space-x-2">
            <button
              onClick={() => setShowSidebar(!showSidebar)}
              className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded-lg"
            >
              {showSidebar ? <ChevronLeft className="w-5 h-5" /> : <ChevronRight className="w-5 h-5" />}
            </button>
            <NoteSearch className="w-80" />
          </div>

          <div className="flex items-center space-x-2">
            {/* 视图切换 */}
            <div className="flex items-center bg-gray-100 rounded-lg p-1">
              <button
                onClick={() => setViewMode('list')}
                className={`
                  p-1.5 rounded transition-colors
                  ${viewMode === 'list' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-500'}
                `}
              >
                <List className="w-4 h-4" />
              </button>
              <button
                onClick={() => setViewMode('grid')}
                className={`
                  p-1.5 rounded transition-colors
                  ${viewMode === 'grid' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-500'}
                `}
              >
                <LayoutGrid className="w-4 h-4" />
              </button>
              <button
                onClick={() => setViewMode('split')}
                className={`
                  p-1.5 rounded transition-colors
                  ${viewMode === 'split' ? 'bg-white shadow-sm text-gray-800' : 'text-gray-500'}
                `}
              >
                <span className="text-xs font-medium">分屏</span>
              </button>
            </div>

            <div className="w-px h-6 bg-gray-200 mx-2" />

            {/* 功能按钮 */}
            {currentNote && (
              <>
                <button
                  onClick={() => setShowAIAssistant(!showAIAssistant)}
                  className={`
                    flex items-center px-3 py-1.5 rounded-lg text-sm
                    ${showAIAssistant
                      ? 'bg-purple-100 text-purple-700'
                      : 'text-gray-600 hover:bg-gray-100'
                    }
                  `}
                >
                  <Sparkles className="w-4 h-4 mr-1.5" />
                  AI助手
                </button>
                <button
                  onClick={() => setShowSharePanel(!showSharePanel)}
                  className="flex items-center px-3 py-1.5 text-gray-600 hover:bg-gray-100 rounded-lg text-sm"
                >
                  <Share2 className="w-4 h-4 mr-1.5" />
                  分享
                </button>
                <button
                  onClick={() => setShowConceptGraph(!showConceptGraph)}
                  className="flex items-center px-3 py-1.5 text-gray-600 hover:bg-gray-100 rounded-lg text-sm"
                >
                  <Network className="w-4 h-4 mr-1.5" />
                  知识图谱
                </button>
              </>
            )}

            <button className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded-lg">
              <Settings className="w-5 h-5" />
            </button>
          </div>
        </header>

        {/* 内容区域 */}
        <div className="flex-1 flex overflow-hidden">
          {/* 笔记列表 */}
          {(viewMode === 'list' || viewMode === 'split') && (
            <div className={`
              ${viewMode === 'split' ? 'w-80 border-r border-gray-200' : 'w-full'}
              bg-white flex flex-col
            `}>
              <NoteList
                onNoteSelect={handleNoteSelect}
                selectedNoteId={selectedNoteId}
              />
            </div>
          )}

          {/* 编辑器区域 */}
          {(viewMode === 'split' || viewMode === 'grid') && (
            <div className="flex-1 flex">
              {/* 主编辑器 */}
              <div className={`
                flex-1 p-4 overflow-auto
                ${showAIAssistant || showSharePanel || showConceptGraph ? 'mr-80' : ''}
              `}>
                <NoteEditor noteId={selectedNoteId} className="h-full" />
              </div>

              {/* 右侧面板 */}
              <div className="w-80 border-l border-gray-200 bg-white flex flex-col">
                {showAIAssistant && (
                  <div className="flex-1 border-b border-gray-200">
                    <NoteAIAssistant note={currentNote || undefined} />
                  </div>
                )}
                {showConceptGraph && currentNote && (
                  <div className="flex-1 border-b border-gray-200 overflow-auto p-4">
                    <NoteConceptGraph note={currentNote} />
                  </div>
                )}
                {showSharePanel && currentNote && (
                  <div className="p-4">
                    <NoteShare note={currentNote} />
                  </div>
                )}
              </div>
            </div>
          )}
        </div>
      </main>
    </div>
  );
};

export default NotesPage;
