// ==================== 智能笔记系统基础示例 ====================
import React, { useState } from 'react';
import { 
  NoteEditor, 
  NoteList, 
  NoteSearch, 
  NoteAIAssistant,
  NoteTemplates,
  LaTeXToolbar,
} from '../';
import { useNoteStore } from '../../../stores/noteStore';
import { createNote } from '../../../services/noteService';
import type { Note, NoteType } from '../../../types/notes';
import {
  Plus,
  Layout,
  Search,
  Sparkles,
  FileText,
  Folder,
  Tag,
  Settings,
  ChevronLeft,
  ChevronRight,
} from 'lucide-react';

// 基础示例组件
export const BasicExample: React.FC = () => {
  const [selectedNoteId, setSelectedNoteId] = useState<string | undefined>();
  const [showTemplates, setShowTemplates] = useState(false);
  const [showSidebar, setShowSidebar] = useState(true);
  const [activeTab, setActiveTab] = useState<'all' | 'favorites' | 'recent'>('all');

  const { notes, addNote, selectNote, editor } = useNoteStore();
  const { currentNote } = editor;

  // 创建新笔记
  const handleCreateNote = async (type: NoteType = 'general') => {
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
  };

  // 处理笔记选择
  const handleNoteSelect = (note: Note) => {
    selectNote(note);
    setSelectedNoteId(note.id);
  };

  return (
    <div className="h-screen bg-gray-50 flex overflow-hidden">
      {/* 侧边栏 */}
      {showSidebar && (
        <aside className="w-64 bg-white border-r border-gray-200 flex flex-col">
          {/* Logo */}
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

          {/* 新建按钮 */}
          <div className="p-4">
            <button
              onClick={() => handleCreateNote()}
              className="w-full flex items-center justify-center px-4 py-3 bg-blue-500 text-white rounded-xl hover:bg-blue-600 transition-colors shadow-sm"
            >
              <Plus className="w-5 h-5 mr-2" />
              新建笔记
            </button>
          </div>

          {/* 导航菜单 */}
          <nav className="flex-1 overflow-y-auto px-3 space-y-1">
            <button
              onClick={() => setActiveTab('all')}
              className={`w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors ${
                activeTab === 'all'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
              }`}
            >
              <FileText className="w-4 h-4 mr-3" />
              全部笔记
              <span className="ml-auto text-xs text-gray-400">{notes.length}</span>
            </button>
            <button
              onClick={() => setActiveTab('favorites')}
              className={`w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors ${
                activeTab === 'favorites'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
              }`}
            >
              <Layout className="w-4 h-4 mr-3" />
              收藏笔记
            </button>
            <button
              onClick={() => setActiveTab('recent')}
              className={`w-full flex items-center px-3 py-2.5 rounded-lg text-sm transition-colors ${
                activeTab === 'recent'
                  ? 'bg-blue-50 text-blue-700 font-medium'
                  : 'text-gray-600 hover:bg-gray-100'
              }`}
            >
              <Folder className="w-4 h-4 mr-3" />
              最近编辑
            </button>

            <div className="pt-4 pb-2">
              <h3 className="px-3 text-xs font-medium text-gray-400 uppercase tracking-wider">
                标签
              </h3>
            </div>
            <div className="px-3 py-2 text-sm text-gray-400">
              暂无标签
            </div>
          </nav>
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
            <button
              onClick={() => setShowTemplates(true)}
              className="flex items-center px-3 py-1.5 text-gray-600 hover:bg-gray-100 rounded-lg text-sm"
            >
              <Layout className="w-4 h-4 mr-1.5" />
              模板
            </button>
            <button className="p-2 text-gray-400 hover:text-gray-600 hover:bg-gray-100 rounded-lg">
              <Settings className="w-5 h-5" />
            </button>
          </div>
        </header>

        {/* 内容区域 */}
        <div className="flex-1 flex overflow-hidden">
          {/* 笔记列表 */}
          <div className="w-80 border-r border-gray-200 bg-white flex flex-col">
            <NoteList
              onNoteSelect={handleNoteSelect}
              selectedNoteId={selectedNoteId}
            />
          </div>

          {/* 编辑器区域 */}
          <div className="flex-1 flex">
            <div className="flex-1 p-4 overflow-auto">
              <NoteEditor noteId={selectedNoteId} className="h-full" />
            </div>

            {/* AI助手侧边栏 */}
            {currentNote && (
              <div className="w-80 border-l border-gray-200 bg-white">
                <NoteAIAssistant note={currentNote} />
              </div>
            )}
          </div>
        </div>
      </main>

      {/* 模板选择弹窗 */}
      {showTemplates && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <NoteTemplates
            onSelectTemplate={(template) => {
              console.log('Selected template:', template);
              setShowTemplates(false);
            }}
            onClose={() => setShowTemplates(false)}
            className="w-[800px] max-h-[80vh]"
          />
        </div>
      )}
    </div>
  );
};

// 独立编辑器示例
export const EditorOnlyExample: React.FC = () => {
  return (
    <div className="h-screen bg-gray-50 p-8">
      <div className="h-full max-w-4xl mx-auto bg-white rounded-xl shadow-lg overflow-hidden">
        <NoteEditor className="h-full" />
      </div>
    </div>
  );
};

// LaTeX工具栏示例
export const LaTeXExample: React.FC = () => {
  const [latex, setLatex] = useState('');

  const handleInsert = (latexCode: string) => {
    setLatex((prev) => prev + latexCode);
  };

  return (
    <div className="p-8 max-w-2xl mx-auto">
      <h2 className="text-2xl font-bold mb-4">LaTeX公式编辑器示例</h2>
      
      <div className="mb-4">
        <LaTeXToolbar onInsert={handleInsert} />
      </div>

      <div className="p-4 bg-gray-100 rounded-lg font-mono text-sm min-h-[200px]">
        {latex || '点击上方按钮插入LaTeX公式...'}
      </div>

      <div className="mt-4 p-4 bg-blue-50 rounded-lg">
        <h3 className="font-medium text-blue-800 mb-2">使用说明</h3>
        <ul className="text-sm text-blue-600 list-disc list-inside space-y-1">
          <li>点击公式按钮插入对应的LaTeX代码</li>
          <li>使用{}表示需要填写的内容</li>
          <li>支持行内公式$...$和块级公式$$...$$</li>
        </ul>
      </div>
    </div>
  );
};

// AI助手示例
export const AIAssistantExample: React.FC = () => {
  const [content, setContent] = useState('');

  return (
    <div className="h-screen bg-gray-50 flex">
      <div className="flex-1 p-8">
        <h2 className="text-2xl font-bold mb-4">AI笔记助手示例</h2>
        <textarea
          value={content}
          onChange={(e) => setContent(e.target.value)}
          className="w-full h-64 p-4 border border-gray-200 rounded-lg font-mono text-sm"
          placeholder="输入笔记内容..."
        />
      </div>
      <div className="w-96 border-l border-gray-200 bg-white">
        <NoteAIAssistant />
      </div>
    </div>
  );
};

// 完整功能示例
export const FullFeatureExample: React.FC = () => {
  const [view, setView] = useState<'editor' | 'list' | 'search' | 'ai'>('editor');

  return (
    <div className="h-screen bg-gray-50">
      {/* 导航 */}
      <nav className="bg-white border-b border-gray-200 px-4 py-3">
        <div className="flex items-center space-x-4">
          <button
            onClick={() => setView('editor')}
            className={`px-4 py-2 rounded-lg ${view === 'editor' ? 'bg-blue-100 text-blue-700' : 'text-gray-600'}`}
          >
            编辑器
          </button>
          <button
            onClick={() => setView('list')}
            className={`px-4 py-2 rounded-lg ${view === 'list' ? 'bg-blue-100 text-blue-700' : 'text-gray-600'}`}
          >
            笔记列表
          </button>
          <button
            onClick={() => setView('search')}
            className={`px-4 py-2 rounded-lg ${view === 'search' ? 'bg-blue-100 text-blue-700' : 'text-gray-600'}`}
          >
            搜索
          </button>
          <button
            onClick={() => setView('ai')}
            className={`px-4 py-2 rounded-lg ${view === 'ai' ? 'bg-blue-100 text-blue-700' : 'text-gray-600'}`}
          >
            AI助手
          </button>
        </div>
      </nav>

      {/* 内容 */}
      <div className="h-[calc(100vh-60px)]">
        {view === 'editor' && <EditorOnlyExample />}
        {view === 'list' && (
          <div className="h-full p-8">
            <NoteList />
          </div>
        )}
        {view === 'search' && (
          <div className="h-full p-8 max-w-2xl mx-auto">
            <h2 className="text-2xl font-bold mb-4">笔记搜索</h2>
            <NoteSearch />
          </div>
        )}
        {view === 'ai' && <AIAssistantExample />}
      </div>
    </div>
  );
};

export default BasicExample;
