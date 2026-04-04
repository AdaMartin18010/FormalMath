/**
 * 视频笔记组件
 */

import React, { useState, useRef, useCallback } from 'react';
import { 
  Plus, 
  Edit2, 
  Trash2, 
  Clock, 
  MessageCircle, 
  Heart,
  Share2,
  Type,
  Image as ImageIcon,
  FunctionSquare,
  X,
  Check
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoNotesProps } from './types';
import type { VideoNote } from '../../types/video';
import { useVideoNotes } from '../../hooks/useVideo';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const VideoNotes: React.FC<VideoNotesProps> = ({
  videoId,
  currentTime,
  isPlaying,
  onTimestampClick,
  className,
}) => {
  const { notes, addNote, updateNote, deleteNote, isLoading } = useVideoNotes(videoId);
  const [isAdding, setIsAdding] = useState(false);
  const [editingNote, setEditingNote] = useState<string | null>(null);
  const [newNoteContent, setNewNoteContent] = useState('');
  const [newNoteType, setNewNoteType] = useState<VideoNote['type']>('text');

  // 格式化时间
  const formatTime = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    const hours = Math.floor(mins / 60);
    
    if (hours > 0) {
      return `${hours}:${String(mins % 60).padStart(2, '0')}:${String(secs).padStart(2, '0')}`;
    }
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  // 添加新笔记
  const handleAddNote = useCallback(() => {
    if (!newNoteContent.trim()) return;

    addNote({
      videoId,
      userId: 'current-user',
      timestamp: currentTime,
      content: newNoteContent.trim(),
      type: newNoteType,
      isPublic: false,
    });

    setNewNoteContent('');
    setIsAdding(false);
  }, [addNote, currentTime, newNoteContent, newNoteType, videoId]);

  // 取消添加
  const handleCancel = useCallback(() => {
    setIsAdding(false);
    setNewNoteContent('');
    setEditingNote(null);
  }, []);

  // 开始添加笔记
  const startAddingNote = useCallback(() => {
    setIsAdding(true);
    setNewNoteType('text');
  }, []);

  return (
    <div className={cn('bg-gray-900 rounded-lg overflow-hidden', className)}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-white/10">
        <h3 className="text-white font-medium flex items-center gap-2">
          <MessageCircle className="w-4 h-4" />
          视频笔记
          <span className="text-white/50 text-sm">({notes.length})</span>
        </h3>
        
        {!isAdding && (
          <button
            onClick={startAddingNote}
            className="flex items-center gap-1 px-3 py-1.5 bg-blue-500 hover:bg-blue-600 text-white text-sm rounded-lg transition-colors"
          >
            <Plus className="w-4 h-4" />
            添加笔记
          </button>
        )}
      </div>

      {/* 添加笔记区域 */}
      {isAdding && (
        <div className="p-4 border-b border-white/10 bg-white/5">
          {/* 笔记类型选择 */}
          <div className="flex gap-2 mb-3">
            {(['text', 'formula', 'screenshot'] as const).map((type) => (
              <button
                key={type}
                onClick={() => setNewNoteType(type)}
                className={cn(
                  'px-3 py-1.5 rounded-lg text-sm flex items-center gap-1.5 transition-colors',
                  newNoteType === type
                    ? 'bg-blue-500 text-white'
                    : 'bg-white/10 text-white/70 hover:bg-white/20'
                )}
              >
                {type === 'text' && <Type className="w-3.5 h-3.5" />}
                {type === 'formula' && <FunctionSquare className="w-3.5 h-3.5" />}
                {type === 'screenshot' && <ImageIcon className="w-3.5 h-3.5" />}
                {type === 'text' && '文本'}
                {type === 'formula' && '公式'}
                {type === 'screenshot' && '截图'}
              </button>
            ))}
          </div>

          {/* 笔记内容输入 */}
          <textarea
            value={newNoteContent}
            onChange={(e) => setNewNoteContent(e.target.value)}
            placeholder="输入笔记内容..."
            className="w-full h-24 bg-gray-800 text-white px-3 py-2 rounded-lg resize-none focus:outline-none focus:ring-2 focus:ring-blue-500 placeholder-white/40"
          />

          {/* 当前时间 */}
          <div className="flex items-center gap-2 mt-2 text-white/50 text-sm">
            <Clock className="w-3.5 h-3.5" />
            <span>标记时间点: {formatTime(currentTime)}</span>
          </div>

          {/* 操作按钮 */}
          <div className="flex justify-end gap-2 mt-3">
            <button
              onClick={handleCancel}
              className="px-4 py-1.5 text-white/70 hover:text-white transition-colors"
            >
              取消
            </button>
            <button
              onClick={handleAddNote}
              disabled={!newNoteContent.trim()}
              className="px-4 py-1.5 bg-blue-500 hover:bg-blue-600 disabled:bg-white/20 disabled:cursor-not-allowed text-white rounded-lg transition-colors flex items-center gap-1.5"
            >
              <Check className="w-4 h-4" />
              保存
            </button>
          </div>
        </div>
      )}

      {/* 笔记列表 */}
      <div className="max-h-96 overflow-y-auto">
        {isLoading ? (
          <div className="p-8 text-center text-white/40">
            <div className="w-8 h-8 border-2 border-white/20 border-t-blue-500 rounded-full animate-spin mx-auto mb-2" />
            加载中...
          </div>
        ) : notes.length === 0 ? (
          <div className="p-8 text-center text-white/40">
            <MessageCircle className="w-12 h-12 mx-auto mb-3 opacity-30" />
            <p>还没有笔记</p>
            <p className="text-sm mt-1">点击上方按钮添加第一条笔记</p>
          </div>
        ) : (
          notes
            .sort((a, b) => a.timestamp - b.timestamp)
            .map((note) => (
              <NoteItem
                key={note.id}
                note={note}
                isEditing={editingNote === note.id}
                onTimestampClick={onTimestampClick}
                onEdit={() => setEditingNote(note.id)}
                onDelete={() => deleteNote(note.id)}
                onSaveEdit={(content) => {
                  updateNote(note.id, { content });
                  setEditingNote(null);
                }}
                onCancelEdit={() => setEditingNote(null)}
              />
            ))
        )}
      </div>
    </div>
  );
};

// 单个笔记项组件
interface NoteItemProps {
  note: VideoNote;
  isEditing: boolean;
  onTimestampClick?: (time: number) => void;
  onEdit: () => void;
  onDelete: () => void;
  onSaveEdit: (content: string) => void;
  onCancelEdit: () => void;
}

const NoteItem: React.FC<NoteItemProps> = ({
  note,
  isEditing,
  onTimestampClick,
  onEdit,
  onDelete,
  onSaveEdit,
  onCancelEdit,
}) => {
  const [editContent, setEditContent] = useState(note.content);

  const formatTime = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  const formatDate = (dateString: string): string => {
    const date = new Date(dateString);
    return date.toLocaleDateString('zh-CN', {
      month: 'short',
      day: 'numeric',
      hour: '2-digit',
      minute: '2-digit',
    });
  };

  const getTypeIcon = (type: VideoNote['type']) => {
    switch (type) {
      case 'formula':
        return <FunctionSquare className="w-3.5 h-3.5" />;
      case 'screenshot':
        return <ImageIcon className="w-3.5 h-3.5" />;
      default:
        return <Type className="w-3.5 h-3.5" />;
    }
  };

  if (isEditing) {
    return (
      <div className="p-4 border-b border-white/10 bg-blue-500/10">
        <textarea
          value={editContent}
          onChange={(e) => setEditContent(e.target.value)}
          className="w-full h-20 bg-gray-800 text-white px-3 py-2 rounded-lg resize-none focus:outline-none focus:ring-2 focus:ring-blue-500"
          autoFocus
        />
        <div className="flex justify-end gap-2 mt-2">
          <button
            onClick={onCancelEdit}
            className="px-3 py-1 text-sm text-white/70 hover:text-white"
          >
            取消
          </button>
          <button
            onClick={() => onSaveEdit(editContent)}
            className="px-3 py-1 text-sm bg-blue-500 hover:bg-blue-600 text-white rounded"
          >
            保存
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className="p-4 border-b border-white/10 hover:bg-white/5 transition-colors group">
      {/* 头部 */}
      <div className="flex items-start justify-between mb-2">
        <div className="flex items-center gap-2">
          <span className={cn(
            'px-2 py-0.5 rounded text-xs flex items-center gap-1',
            note.type === 'formula' && 'bg-purple-500/20 text-purple-400',
            note.type === 'screenshot' && 'bg-green-500/20 text-green-400',
            note.type === 'text' && 'bg-blue-500/20 text-blue-400'
          )}>
            {getTypeIcon(note.type)}
          </span>
          <button
            onClick={() => onTimestampClick?.(note.timestamp)}
            className="text-blue-400 text-sm hover:underline flex items-center gap-1"
          >
            <Clock className="w-3 h-3" />
            {formatTime(note.timestamp)}
          </button>
        </div>
        
        {/* 操作按钮 */}
        <div className="flex items-center gap-1 opacity-0 group-hover:opacity-100 transition-opacity">
          <button
            onClick={onEdit}
            className="p-1 text-white/40 hover:text-white/70 transition-colors"
          >
            <Edit2 className="w-3.5 h-3.5" />
          </button>
          <button
            onClick={onDelete}
            className="p-1 text-white/40 hover:text-red-400 transition-colors"
          >
            <Trash2 className="w-3.5 h-3.5" />
          </button>
        </div>
      </div>

      {/* 内容 */}
      <div className="text-white/90 text-sm leading-relaxed whitespace-pre-wrap">
        {note.content}
      </div>

      {/* 底部信息 */}
      <div className="flex items-center justify-between mt-3 text-xs text-white/40">
        <span>{formatDate(note.createdAt)}</span>
        <div className="flex items-center gap-3">
          <button className="flex items-center gap-1 hover:text-white/70 transition-colors">
            <Heart className="w-3.5 h-3.5" />
            {note.likes || 0}
          </button>
          <button className="flex items-center gap-1 hover:text-white/70 transition-colors">
            <Share2 className="w-3.5 h-3.5" />
          </button>
        </div>
      </div>
    </div>
  );
};
