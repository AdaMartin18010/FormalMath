/**
 * 视频管理界面组件
 * 用于管理员上传、编辑、管理视频内容
 */

import React, { useState, useCallback } from 'react';
import {
  Upload,
  Edit2,
  Trash2,
  Search,
  Filter,
  Grid,
  List,
  MoreVertical,
  Play,
  Clock,
  Eye,
  CheckCircle,
  AlertCircle,
  X,
  ChevronLeft,
  ChevronRight,
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { Video, VideoCategory, VideoSearchParams } from '../../types/video';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

// 视频管理界面 Props
export interface VideoManagementProps {
  videos: Video[];
  categories: VideoCategory[];
  onUpload: () => void;
  onEdit: (video: Video) => void;
  onDelete: (video: Video) => void;
  onSearch: (params: VideoSearchParams) => void;
  className?: string;
}

// 视图模式
 type ViewMode = 'grid' | 'list';

export const VideoManagement: React.FC<VideoManagementProps> = ({
  videos,
  categories,
  onUpload,
  onEdit,
  onDelete,
  onSearch,
  className,
}) => {
  const [viewMode, setViewMode] = useState<ViewMode>('grid');
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedCategory, setSelectedCategory] = useState<string>('all');
  const [selectedVideos, setSelectedVideos] = useState<Set<string>>(new Set());
  const [currentPage, setCurrentPage] = useState(1);
  const pageSize = 12;

  // 处理搜索
  const handleSearch = useCallback(() => {
    onSearch({
      keyword: searchQuery,
      category: selectedCategory === 'all' ? undefined : selectedCategory,
      page: currentPage,
      pageSize,
    });
  }, [searchQuery, selectedCategory, currentPage, onSearch]);

  // 处理选择
  const toggleSelect = useCallback((videoId: string) => {
    setSelectedVideos(prev => {
      const newSet = new Set(prev);
      if (newSet.has(videoId)) {
        newSet.delete(videoId);
      } else {
        newSet.add(videoId);
      }
      return newSet;
    });
  }, []);

  // 全选
  const toggleSelectAll = useCallback(() => {
    if (selectedVideos.size === videos.length) {
      setSelectedVideos(new Set());
    } else {
      setSelectedVideos(new Set(videos.map(v => v.id)));
    }
  }, [videos, selectedVideos.size]);

  // 格式化时长
  const formatDuration = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    const hours = Math.floor(mins / 60);
    
    if (hours > 0) {
      return `${hours}:${String(mins % 60).padStart(2, '0')}:${String(secs).padStart(2, '0')}`;
    }
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  // 格式化日期
  const formatDate = (dateString: string): string => {
    const date = new Date(dateString);
    return date.toLocaleDateString('zh-CN', {
      year: 'numeric',
      month: 'short',
      day: 'numeric',
    });
  };

  // 格式化数字
  const formatNumber = (num: number): string => {
    if (num >= 10000) {
      return `${(num / 10000).toFixed(1)}万`;
    }
    if (num >= 1000) {
      return `${(num / 1000).toFixed(1)}k`;
    }
    return num.toString();
  };

  return (
    <div className={cn('bg-gray-900 rounded-lg overflow-hidden', className)}>
      {/* 工具栏 */}
      <div className="flex flex-wrap items-center gap-3 p-4 border-b border-white/10">
        {/* 搜索 */}
        <div className="flex-1 min-w-[200px] max-w-md">
          <div className="relative">
            <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-white/40" />
            <input
              type="text"
              value={searchQuery}
              onChange={(e) => setSearchQuery(e.target.value)}
              placeholder="搜索视频..."
              className="w-full bg-gray-800 text-white pl-10 pr-4 py-2 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500 placeholder-white/40"
              onKeyDown={(e) => e.key === 'Enter' && handleSearch()}
            />
          </div>
        </div>

        {/* 分类筛选 */}
        <select
          value={selectedCategory}
          onChange={(e) => setSelectedCategory(e.target.value)}
          className="bg-gray-800 text-white px-3 py-2 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
        >
          <option value="all">全部分类</option>
          {categories.map((cat) => (
            <option key={cat.id} value={cat.id}>{cat.name}</option>
          ))}
        </select>

        {/* 视图切换 */}
        <div className="flex items-center bg-gray-800 rounded-lg p-1">
          <button
            onClick={() => setViewMode('grid')}
            className={cn(
              'p-1.5 rounded transition-colors',
              viewMode === 'grid' ? 'bg-blue-500 text-white' : 'text-white/60 hover:text-white'
            )}
          >
            <Grid className="w-4 h-4" />
          </button>
          <button
            onClick={() => setViewMode('list')}
            className={cn(
              'p-1.5 rounded transition-colors',
              viewMode === 'list' ? 'bg-blue-500 text-white' : 'text-white/60 hover:text-white'
            )}
          >
            <List className="w-4 h-4" />
          </button>
        </div>

        {/* 上传按钮 */}
        <button
          onClick={onUpload}
          className="flex items-center gap-2 px-4 py-2 bg-blue-500 hover:bg-blue-600 text-white rounded-lg transition-colors"
        >
          <Upload className="w-4 h-4" />
          上传视频
        </button>
      </div>

      {/* 批量操作栏 */}
      {selectedVideos.size > 0 && (
        <div className="flex items-center justify-between px-4 py-2 bg-blue-500/20 border-b border-blue-500/30">
          <span className="text-blue-400 text-sm">
            已选择 {selectedVideos.size} 个视频
          </span>
          <div className="flex items-center gap-2">
            <button
              onClick={() => setSelectedVideos(new Set())}
              className="text-white/70 hover:text-white text-sm"
            >
              取消选择
            </button>
            <button className="px-3 py-1 bg-red-500 hover:bg-red-600 text-white text-sm rounded transition-colors">
              批量删除
            </button>
          </div>
        </div>
      )}

      {/* 视频列表 */}
      <div className={cn(
        'p-4',
        viewMode === 'grid' ? 'grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-4' : 'space-y-2'
      )}>
        {videos.map((video) => (
          viewMode === 'grid' ? (
            <VideoGridCard
              key={video.id}
              video={video}
              isSelected={selectedVideos.has(video.id)}
              onSelect={() => toggleSelect(video.id)}
              onEdit={() => onEdit(video)}
              onDelete={() => onDelete(video)}
              formatDuration={formatDuration}
              formatDate={formatDate}
              formatNumber={formatNumber}
            />
          ) : (
            <VideoListItem
              key={video.id}
              video={video}
              isSelected={selectedVideos.has(video.id)}
              onSelect={() => toggleSelect(video.id)}
              onEdit={() => onEdit(video)}
              onDelete={() => onDelete(video)}
              formatDuration={formatDuration}
              formatDate={formatDate}
              formatNumber={formatNumber}
            />
          )
        ))}
      </div>

      {/* 分页 */}
      <div className="flex items-center justify-between px-4 py-4 border-t border-white/10">
        <span className="text-white/50 text-sm">
          共 {videos.length} 个视频
        </span>
        <div className="flex items-center gap-2">
          <button
            onClick={() => setCurrentPage(prev => Math.max(1, prev - 1))}
            disabled={currentPage === 1}
            className="p-2 rounded-lg bg-gray-800 text-white disabled:opacity-50 disabled:cursor-not-allowed hover:bg-gray-700 transition-colors"
          >
            <ChevronLeft className="w-4 h-4" />
          </button>
          <span className="text-white px-3">
            第 {currentPage} 页
          </span>
          <button
            onClick={() => setCurrentPage(prev => prev + 1)}
            disabled={videos.length < pageSize}
            className="p-2 rounded-lg bg-gray-800 text-white disabled:opacity-50 disabled:cursor-not-allowed hover:bg-gray-700 transition-colors"
          >
            <ChevronRight className="w-4 h-4" />
          </button>
        </div>
      </div>
    </div>
  );
};

// 网格卡片
interface VideoCardProps {
  video: Video;
  isSelected: boolean;
  onSelect: () => void;
  onEdit: () => void;
  onDelete: () => void;
  formatDuration: (seconds: number) => string;
  formatDate: (date: string) => string;
  formatNumber: (num: number) => string;
}

const VideoGridCard: React.FC<VideoCardProps> = ({
  video,
  isSelected,
  onSelect,
  onEdit,
  onDelete,
  formatDuration,
  formatDate,
  formatNumber,
}) => {
  const [showActions, setShowActions] = useState(false);

  return (
    <div
      className={cn(
        'group bg-gray-800 rounded-lg overflow-hidden transition-all',
        isSelected && 'ring-2 ring-blue-500'
      )}
      onMouseEnter={() => setShowActions(true)}
      onMouseLeave={() => setShowActions(false)}
    >
      {/* 缩略图 */}
      <div className="relative aspect-video bg-gray-700">
        <img
          src={video.thumbnail}
          alt={video.title}
          className="w-full h-full object-cover"
        />
        
        {/* 时长 */}
        <div className="absolute bottom-2 right-2 px-1.5 py-0.5 bg-black/80 text-white text-xs rounded">
          {formatDuration(video.duration)}
        </div>

        {/* 选择框 */}
        <div className="absolute top-2 left-2">
          <input
            type="checkbox"
            checked={isSelected}
            onChange={onSelect}
            className="w-5 h-5 rounded border-2 border-white/50 bg-black/50 checked:bg-blue-500 checked:border-blue-500"
          />
        </div>

        {/* 操作按钮 */}
        {showActions && (
          <div className="absolute top-2 right-2 flex gap-1">
            <button
              onClick={onEdit}
              className="p-1.5 bg-black/50 text-white rounded hover:bg-black/70 transition-colors"
            >
              <Edit2 className="w-4 h-4" />
            </button>
            <button
              onClick={onDelete}
              className="p-1.5 bg-black/50 text-white rounded hover:bg-red-500 transition-colors"
            >
              <Trash2 className="w-4 h-4" />
            </button>
          </div>
        )}

        {/* 播放按钮 */}
        <div className="absolute inset-0 bg-black/50 opacity-0 group-hover:opacity-100 transition-opacity flex items-center justify-center">
          <Play className="w-12 h-12 text-white" />
        </div>
      </div>

      {/* 信息 */}
      <div className="p-3">
        <h3 className="text-white font-medium line-clamp-2 mb-2">{video.title}</h3>
        
        <div className="flex items-center gap-2 text-sm text-white/50">
          <Eye className="w-4 h-4" />
          <span>{formatNumber(video.viewCount)}</span>
          <span className="mx-1">·</span>
          <span>{formatDate(video.createdAt)}</span>
        </div>

        <div className="flex items-center gap-2 mt-2">
          <span className={cn(
            'px-2 py-0.5 text-xs rounded-full',
            video.difficulty === 'beginner' && 'bg-green-500/20 text-green-400',
            video.difficulty === 'intermediate' && 'bg-yellow-500/20 text-yellow-400',
            video.difficulty === 'advanced' && 'bg-red-500/20 text-red-400'
          )}>
            {video.difficulty === 'beginner' && '入门'}
            {video.difficulty === 'intermediate' && '进阶'}
            {video.difficulty === 'advanced' && '高级'}
          </span>
        </div>
      </div>
    </div>
  );
};

// 列表项
const VideoListItem: React.FC<VideoCardProps> = ({
  video,
  isSelected,
  onSelect,
  onEdit,
  onDelete,
  formatDuration,
  formatDate,
  formatNumber,
}) => {
  return (
    <div className={cn(
      'flex items-center gap-4 p-3 bg-gray-800 rounded-lg transition-all',
      isSelected && 'ring-2 ring-blue-500'
    )}>
      {/* 选择框 */}
      <input
        type="checkbox"
        checked={isSelected}
        onChange={onSelect}
        className="w-5 h-5 rounded border-2 border-white/50 bg-transparent checked:bg-blue-500 checked:border-blue-500"
      />

      {/* 缩略图 */}
      <div className="relative w-32 aspect-video bg-gray-700 rounded overflow-hidden flex-shrink-0">
        <img
          src={video.thumbnail}
          alt={video.title}
          className="w-full h-full object-cover"
        />
        <div className="absolute bottom-1 right-1 px-1 py-0.5 bg-black/80 text-white text-xs rounded">
          {formatDuration(video.duration)}
        </div>
      </div>

      {/* 信息 */}
      <div className="flex-1 min-w-0">
        <h3 className="text-white font-medium truncate">{video.title}</h3>
        <div className="flex items-center gap-4 mt-1 text-sm text-white/50">
          <span className="flex items-center gap-1">
            <Eye className="w-3.5 h-3.5" />
            {formatNumber(video.viewCount)}
          </span>
          <span className="flex items-center gap-1">
            <Clock className="w-3.5 h-3.5" />
            {formatDate(video.createdAt)}
          </span>
          <span className={cn(
            'px-2 py-0.5 text-xs rounded-full',
            video.difficulty === 'beginner' && 'bg-green-500/20 text-green-400',
            video.difficulty === 'intermediate' && 'bg-yellow-500/20 text-yellow-400',
            video.difficulty === 'advanced' && 'bg-red-500/20 text-red-400'
          )}>
            {video.difficulty === 'beginner' && '入门'}
            {video.difficulty === 'intermediate' && '进阶'}
            {video.difficulty === 'advanced' && '高级'}
          </span>
        </div>
      </div>

      {/* 操作 */}
      <div className="flex items-center gap-2">
        <button
          onClick={onEdit}
          className="p-2 text-white/50 hover:text-white hover:bg-white/10 rounded-lg transition-colors"
        >
          <Edit2 className="w-4 h-4" />
        </button>
        <button
          onClick={onDelete}
          className="p-2 text-white/50 hover:text-red-400 hover:bg-red-500/10 rounded-lg transition-colors"
        >
          <Trash2 className="w-4 h-4" />
        </button>
      </div>
    </div>
  );
};
