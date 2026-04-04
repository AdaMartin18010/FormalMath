// ==================== 笔记列表组件 ====================
import React, { useState, useCallback } from 'react';
import { useNoteStore, selectFilteredNotes } from '../../stores/noteStore';
import {
  FileText,
  MoreVertical,
  Pin,
  Star,
  Clock,
  Tag,
  Folder,
  Trash2,
  Edit3,
  Share2,
  Copy,
  Archive,
  Check,
  ChevronDown,
  ChevronRight,
} from 'lucide-react';
import type { Note, NoteType, NoteStatus } from '../../types/notes';

interface NoteListProps {
  onNoteSelect?: (note: Note) => void;
  selectedNoteId?: string;
  className?: string;
}

// 笔记类型图标
const NoteTypeIcon: React.FC<{ type: NoteType }> = ({ type }) => {
  const iconClass = "w-4 h-4";
  switch (type) {
    case 'concept':
      return <span className={iconClass} title="概念">💡</span>;
    case 'theorem':
      return <span className={iconClass} title="定理">📐</span>;
    case 'proof':
      return <span className={iconClass} title="证明">✓</span>;
    case 'example':
      return <span className={iconClass} title="示例">📝</span>;
    case 'exercise':
      return <span className={iconClass} title="练习">🎯</span>;
    default:
      return <FileText className={iconClass} />;
  }
};

// 笔记类型颜色
const getNoteTypeColor = (type: NoteType): string => {
  switch (type) {
    case 'concept': return 'bg-blue-100 text-blue-700';
    case 'theorem': return 'bg-purple-100 text-purple-700';
    case 'proof': return 'bg-green-100 text-green-700';
    case 'example': return 'bg-yellow-100 text-yellow-700';
    case 'exercise': return 'bg-orange-100 text-orange-700';
    default: return 'bg-gray-100 text-gray-700';
  }
};

// 格式化相对时间
const formatRelativeTime = (date: string): string => {
  const now = new Date();
  const past = new Date(date);
  const diffMs = now.getTime() - past.getTime();
  const diffMins = Math.floor(diffMs / 60000);
  const diffHours = Math.floor(diffMs / 3600000);
  const diffDays = Math.floor(diffMs / 86400000);

  if (diffMins < 1) return '刚刚';
  if (diffMins < 60) return `${diffMins}分钟前`;
  if (diffHours < 24) return `${diffHours}小时前`;
  if (diffDays < 7) return `${diffDays}天前`;
  return past.toLocaleDateString('zh-CN');
};

// 笔记列表项
interface NoteListItemProps {
  note: Note;
  isSelected: boolean;
  onSelect: (note: Note) => void;
  onToggleFavorite: (noteId: string) => void;
  onTogglePin: (noteId: string) => void;
  onDelete: (noteId: string) => void;
}

const NoteListItem: React.FC<NoteListItemProps> = ({
  note,
  isSelected,
  onSelect,
  onToggleFavorite,
  onTogglePin,
  onDelete,
}) => {
  const [showMenu, setShowMenu] = useState(false);

  // 截断内容预览
  const contentPreview = note.content
    ?.replace(/[#*`\[\]()]/g, ' ')
    ?.replace(/\s+/g, ' ')
    ?.slice(0, 100) + (note.content?.length > 100 ? '...' : '') || '无内容';

  return (
    <div
      onClick={() => onSelect(note)}
      className={`
        group relative p-4 cursor-pointer border-b border-gray-100
        transition-all duration-200
        ${isSelected
          ? 'bg-blue-50 border-l-4 border-l-blue-500'
          : 'bg-white border-l-4 border-l-transparent hover:bg-gray-50'
        }
      `}
    >
      <div className="flex items-start justify-between">
        <div className="flex-1 min-w-0">
          {/* 标题行 */}
          <div className="flex items-center space-x-2 mb-1">
            <NoteTypeIcon type={note.type} />
            <h3 className={`
              font-medium truncate
              ${isSelected ? 'text-blue-700' : 'text-gray-800'}
            `}>
              {note.title || '无标题'}
            </h3>
            {note.isPinned && (
              <Pin className="w-3 h-3 text-blue-500 fill-current flex-shrink-0" />
            )}
            {note.status === 'archived' && (
              <span className="text-xs px-1.5 py-0.5 bg-gray-100 text-gray-500 rounded">
                归档
              </span>
            )}
          </div>

          {/* 内容预览 */}
          <p className="text-sm text-gray-500 truncate mb-2">
            {contentPreview}
          </p>

          {/* 元信息 */}
          <div className="flex items-center space-x-3 text-xs text-gray-400">
            <span className="flex items-center">
              <Clock className="w-3 h-3 mr-1" />
              {formatRelativeTime(note.updatedAt)}
            </span>
            {note.wordCount > 0 && (
              <span>{note.wordCount} 字</span>
            )}
            {note.tags.length > 0 && (
              <div className="flex items-center space-x-1">
                <Tag className="w-3 h-3" />
                {note.tags.slice(0, 3).map((tag) => (
                  <span
                    key={tag.id}
                    className="px-1.5 py-0.5 rounded-full text-xs"
                    style={{ backgroundColor: tag.color + '20', color: tag.color }}
                  >
                    {tag.name}
                  </span>
                ))}
                {note.tags.length > 3 && (
                  <span className="text-gray-400">+{note.tags.length - 3}</span>
                )}
              </div>
            )}
          </div>
        </div>

        {/* 操作按钮 */}
        <div className="flex items-center space-x-1 ml-2 opacity-0 group-hover:opacity-100 transition-opacity">
          <button
            onClick={(e) => {
              e.stopPropagation();
              onToggleFavorite(note.id);
            }}
            className={`
              p-1.5 rounded-lg transition-colors
              ${note.isFavorite
                ? 'text-yellow-500 bg-yellow-50'
                : 'text-gray-400 hover:text-yellow-500 hover:bg-yellow-50'
              }
            `}
            title={note.isFavorite ? '取消收藏' : '收藏'}
          >
            <Star className={`w-4 h-4 ${note.isFavorite ? 'fill-current' : ''}`} />
          </button>
          <button
            onClick={(e) => {
              e.stopPropagation();
              onTogglePin(note.id);
            }}
            className={`
              p-1.5 rounded-lg transition-colors
              ${note.isPinned
                ? 'text-blue-500 bg-blue-50'
                : 'text-gray-400 hover:text-blue-500 hover:bg-blue-50'
              }
            `}
            title={note.isPinned ? '取消置顶' : '置顶'}
          >
            <Pin className={`w-4 h-4 ${note.isPinned ? 'fill-current' : ''}`} />
          </button>
          <div className="relative">
            <button
              onClick={(e) => {
                e.stopPropagation();
                setShowMenu(!showMenu);
              }}
              className="p-1.5 rounded-lg text-gray-400 hover:text-gray-600 hover:bg-gray-100"
            >
              <MoreVertical className="w-4 h-4" />
            </button>
            {showMenu && (
              <>
                <div
                  className="fixed inset-0 z-10"
                  onClick={() => setShowMenu(false)}
                />
                <div className="absolute right-0 top-full mt-1 w-40 bg-white rounded-lg shadow-lg border border-gray-200 z-20 py-1">
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      // 编辑操作
                      setShowMenu(false);
                    }}
                    className="w-full px-4 py-2 text-left text-sm text-gray-700 hover:bg-gray-50 flex items-center"
                  >
                    <Edit3 className="w-4 h-4 mr-2" />
                    编辑
                  </button>
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      // 分享操作
                      setShowMenu(false);
                    }}
                    className="w-full px-4 py-2 text-left text-sm text-gray-700 hover:bg-gray-50 flex items-center"
                  >
                    <Share2 className="w-4 h-4 mr-2" />
                    分享
                  </button>
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      // 复制操作
                      setShowMenu(false);
                    }}
                    className="w-full px-4 py-2 text-left text-sm text-gray-700 hover:bg-gray-50 flex items-center"
                  >
                    <Copy className="w-4 h-4 mr-2" />
                    复制
                  </button>
                  <hr className="my-1" />
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      onDelete(note.id);
                      setShowMenu(false);
                    }}
                    className="w-full px-4 py-2 text-left text-sm text-red-600 hover:bg-red-50 flex items-center"
                  >
                    <Trash2 className="w-4 h-4 mr-2" />
                    删除
                  </button>
                </div>
              </>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

// 主组件
export const NoteList: React.FC<NoteListProps> = ({
  onNoteSelect,
  selectedNoteId,
  className = '',
}) => {
  const {
    notes,
    folders,
    currentFolder,
    selectNote,
    toggleNoteSelection,
    updateNote,
    deleteNote,
    setCurrentFolder,
    toggleFolderExpanded,
    folderTreeExpanded,
  } = useNoteStore();

  const filteredNotes = useNoteStore(selectFilteredNotes);

  // 分组笔记
  const pinnedNotes = filteredNotes.filter((n) => n.isPinned);
  const unpinnedNotes = filteredNotes.filter((n) => !n.isPinned);

  // 处理笔记选择
  const handleNoteSelect = useCallback((note: Note) => {
    selectNote(note);
    onNoteSelect?.(note);
  }, [selectNote, onNoteSelect]);

  // 处理收藏
  const handleToggleFavorite = useCallback((noteId: string) => {
    const note = notes.find((n) => n.id === noteId);
    if (note) {
      updateNote(noteId, { isFavorite: !note.isFavorite });
    }
  }, [notes, updateNote]);

  // 处理置顶
  const handleTogglePin = useCallback((noteId: string) => {
    const note = notes.find((n) => n.id === noteId);
    if (note) {
      updateNote(noteId, { isPinned: !note.isPinned });
    }
  }, [notes, updateNote]);

  // 处理删除
  const handleDelete = useCallback((noteId: string) => {
    if (confirm('确定要删除这篇笔记吗？')) {
      deleteNote(noteId);
    }
  }, [deleteNote]);

  // 渲染文件夹树
  const renderFolderTree = (folderList: typeof folders, parentId?: string, level = 0) => {
    const children = folderList.filter((f) => f.parentId === parentId);
    if (children.length === 0) return null;

    return children.map((folder) => {
      const isExpanded = folderTreeExpanded.includes(folder.id);
      const hasChildren = folderList.some((f) => f.parentId === folder.id);
      const isSelected = currentFolder?.id === folder.id;

      return (
        <div key={folder.id}>
          <button
            onClick={() => setCurrentFolder(isSelected ? null : folder)}
            className={`
              w-full flex items-center px-3 py-2 text-sm rounded-lg
              transition-colors
              ${isSelected
                ? 'bg-blue-100 text-blue-700'
                : 'text-gray-600 hover:bg-gray-100'
              }
            `}
            style={{ paddingLeft: `${12 + level * 16}px` }}
          >
            {hasChildren && (
              <button
                onClick={(e) => {
                  e.stopPropagation();
                  toggleFolderExpanded(folder.id);
                }}
                className="mr-1 p-0.5 rounded hover:bg-gray-200"
              >
                {isExpanded ? (
                  <ChevronDown className="w-3 h-3" />
                ) : (
                  <ChevronRight className="w-3 h-3" />
                )}
              </button>
            )}
            {!hasChildren && <span className="w-4" />}
            <Folder className="w-4 h-4 mr-2 flex-shrink-0" />
            <span className="truncate">{folder.name}</span>
            <span className="ml-auto text-xs text-gray-400">
              {folder.noteCount}
            </span>
          </button>
          {isExpanded && renderFolderTree(folderList, folder.id, level + 1)}
        </div>
      );
    });
  };

  return (
    <div className={`flex h-full ${className}`}>
      {/* 文件夹侧边栏 */}
      <div className="w-56 border-r border-gray-200 bg-gray-50 flex flex-col">
        <div className="p-3 border-b border-gray-200">
          <h3 className="text-xs font-medium text-gray-500 uppercase tracking-wider">
            文件夹
          </h3>
        </div>
        <div className="flex-1 overflow-y-auto p-2 space-y-1">
          <button
            onClick={() => setCurrentFolder(null)}
            className={`
              w-full flex items-center px-3 py-2 text-sm rounded-lg
              transition-colors
              ${!currentFolder
                ? 'bg-blue-100 text-blue-700'
                : 'text-gray-600 hover:bg-gray-100'
              }
            `}
          >
            <Folder className="w-4 h-4 mr-2" />
            全部笔记
            <span className="ml-auto text-xs text-gray-400">{notes.length}</span>
          </button>
          {renderFolderTree(folders)}
        </div>
      </div>

      {/* 笔记列表 */}
      <div className="flex-1 flex flex-col bg-white">
        {/* 列表头部 */}
        <div className="px-4 py-3 border-b border-gray-200 flex items-center justify-between">
          <h2 className="font-medium text-gray-800">
            {currentFolder ? currentFolder.name : '全部笔记'}
            <span className="ml-2 text-sm text-gray-400">({filteredNotes.length})</span>
          </h2>
        </div>

        {/* 笔记列表内容 */}
        <div className="flex-1 overflow-y-auto">
          {filteredNotes.length === 0 ? (
            <div className="flex flex-col items-center justify-center h-full text-gray-400">
              <FileText className="w-12 h-12 mb-4 opacity-50" />
              <p>暂无笔记</p>
              <p className="text-sm mt-1">创建第一篇笔记开始记录</p>
            </div>
          ) : (
            <>
              {/* 置顶笔记 */}
              {pinnedNotes.length > 0 && (
                <>
                  <div className="px-4 py-2 bg-gray-50 text-xs font-medium text-gray-500">
                    置顶笔记
                  </div>
                  {pinnedNotes.map((note) => (
                    <NoteListItem
                      key={note.id}
                      note={note}
                      isSelected={selectedNoteId === note.id}
                      onSelect={handleNoteSelect}
                      onToggleFavorite={handleToggleFavorite}
                      onTogglePin={handleTogglePin}
                      onDelete={handleDelete}
                    />
                  ))}
                </>
              )}

              {/* 普通笔记 */}
              {unpinnedNotes.length > 0 && (
                <>
                  {pinnedNotes.length > 0 && (
                    <div className="px-4 py-2 bg-gray-50 text-xs font-medium text-gray-500">
                      其他笔记
                    </div>
                  )}
                  {unpinnedNotes.map((note) => (
                    <NoteListItem
                      key={note.id}
                      note={note}
                      isSelected={selectedNoteId === note.id}
                      onSelect={handleNoteSelect}
                      onToggleFavorite={handleToggleFavorite}
                      onTogglePin={handleTogglePin}
                      onDelete={handleDelete}
                    />
                  ))}
                </>
              )}
            </>
          )}
        </div>
      </div>
    </div>
  );
};

export default NoteList;
