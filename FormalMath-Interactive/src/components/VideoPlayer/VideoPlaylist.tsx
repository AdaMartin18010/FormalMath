/**
 * 视频播放列表组件
 */

import React, { useState, useMemo } from 'react';
import { 
  Play, 
  Pause, 
  ChevronUp, 
  ChevronDown,
  ListVideo,
  Shuffle,
  Repeat,
  GripVertical,
  Trash2
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoPlaylistProps } from './types';
import type { Video, VideoPlaylist as VideoPlaylistType } from '../../types/video';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const VideoPlaylist: React.FC<VideoPlaylistProps> = ({
  playlist,
  currentVideoId,
  onVideoClick,
  className,
}) => {
  const [isExpanded, setIsExpanded] = useState(true);
  const [isShuffled, setIsShuffled] = useState(false);
  const [repeatMode, setRepeatMode] = useState<'none' | 'all' | 'one'>('none');

  // 获取当前播放索引
  const currentIndex = useMemo(() => {
    return playlist.videos.findIndex(v => v.id === currentVideoId);
  }, [playlist.videos, currentVideoId]);

  // 计算总时长
  const totalDuration = useMemo(() => {
    return playlist.videos.reduce((acc, video) => acc + video.duration, 0);
  }, [playlist.videos]);

  // 格式化时长
  const formatDuration = (seconds: number): string => {
    const hours = Math.floor(seconds / 3600);
    const mins = Math.floor((seconds % 3600) / 60);
    
    if (hours > 0) {
      return `${hours}小时${mins}分钟`;
    }
    return `${mins}分钟`;
  };

  // 格式化单个视频时长
  const formatVideoDuration = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  return (
    <div className={cn('bg-gray-900 rounded-lg overflow-hidden', className)}>
      {/* 头部 */}
      <div className="flex items-center justify-between px-4 py-3 border-b border-white/10">
        <div className="flex items-center gap-3">
          <button
            onClick={() => setIsExpanded(!isExpanded)}
            className="p-1 text-white/60 hover:text-white transition-colors"
          >
            {isExpanded ? (
              <ChevronUp className="w-5 h-5" />
            ) : (
              <ChevronDown className="w-5 h-5" />
            )}
          </button>
          
          <div>
            <h3 className="text-white font-medium flex items-center gap-2">
              <ListVideo className="w-4 h-4" />
              {playlist.title}
            </h3>
            <p className="text-white/50 text-xs mt-0.5">
              {playlist.author.name} · {playlist.videos.length}个视频 · {formatDuration(totalDuration)}
            </p>
          </div>
        </div>

        {/* 播放控制 */}
        <div className="flex items-center gap-1">
          <button
            onClick={() => setIsShuffled(!isShuffled)}
            className={cn(
              'p-2 rounded-lg transition-colors',
              isShuffled ? 'text-blue-400 bg-blue-500/20' : 'text-white/60 hover:text-white hover:bg-white/10'
            )}
            title="随机播放"
          >
            <Shuffle className="w-4 h-4" />
          </button>
          
          <button
            onClick={() => setRepeatMode(prev => {
              const modes: Array<'none' | 'all' | 'one'> = ['none', 'all', 'one'];
              const nextIndex = (modes.indexOf(prev) + 1) % modes.length;
              return modes[nextIndex];
            })}
            className={cn(
              'p-2 rounded-lg transition-colors',
              repeatMode !== 'none' ? 'text-blue-400 bg-blue-500/20' : 'text-white/60 hover:text-white hover:bg-white/10'
            )}
            title={repeatMode === 'one' ? '单曲循环' : repeatMode === 'all' ? '列表循环' : '不循环'}
          >
            <Repeat className="w-4 h-4" />
            {repeatMode === 'one' && (
              <span className="absolute text-[8px] font-bold">1</span>
            )}
          </button>
        </div>
      </div>

      {/* 视频列表 */}
      {isExpanded && (
        <div className="max-h-96 overflow-y-auto">
          {playlist.videos.map((video, index) => {
            const isActive = video.id === currentVideoId;
            const isCompleted = currentIndex > index;
            const isPending = currentIndex < index;

            return (
              <PlaylistItem
                key={video.id}
                video={video}
                index={index + 1}
                isActive={isActive}
                isCompleted={isCompleted}
                isPending={isPending}
                onClick={() => onVideoClick(video, index)}
              />
            );
          })}
        </div>
      )}
    </div>
  );
};

// 播放列表项
interface PlaylistItemProps {
  video: Video;
  index: number;
  isActive: boolean;
  isCompleted: boolean;
  isPending: boolean;
  onClick: () => void;
}

const PlaylistItem: React.FC<PlaylistItemProps> = ({
  video,
  index,
  isActive,
  isCompleted,
  onClick,
}) => {
  const [isHovered, setIsHovered] = useState(false);

  const formatDuration = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  return (
    <div
      onClick={onClick}
      onMouseEnter={() => setIsHovered(true)}
      onMouseLeave={() => setIsHovered(false)}
      className={cn(
        'flex items-center gap-3 px-4 py-2 border-b border-white/5 last:border-b-0 cursor-pointer transition-colors',
        isActive ? 'bg-blue-500/20' : 'hover:bg-white/5'
      )}
    >
      {/* 序号/状态/拖拽 */}
      <div className="w-6 flex-shrink-0 flex justify-center">
        {isActive ? (
          <div className="flex items-center gap-0.5">
            <div className="w-1 h-3 bg-blue-500 animate-pulse" />
            <div className="w-1 h-3 bg-blue-500 animate-pulse delay-75" />
            <div className="w-1 h-3 bg-blue-500 animate-pulse delay-150" />
          </div>
        ) : isCompleted ? (
          <svg className="w-4 h-4 text-blue-500" fill="none" viewBox="0 0 24 24" stroke="currentColor">
            <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
          </svg>
        ) : (
          <span className={cn(
            'text-sm',
            isActive ? 'text-blue-400' : 'text-white/40'
          )}>
            {index}
          </span>
        )}
      </div>

      {/* 缩略图 */}
      <div className="relative flex-shrink-0 w-24 aspect-video bg-gray-800 rounded overflow-hidden">
        <img
          src={video.thumbnail}
          alt={video.title}
          className="w-full h-full object-cover"
        />
        
        {/* 播放遮罩 */}
        {(isHovered || isActive) && (
          <div className="absolute inset-0 bg-black/50 flex items-center justify-center">
            {isActive ? (
              <Pause className="w-6 h-6 text-white" />
            ) : (
              <Play className="w-6 h-6 text-white ml-0.5" />
            )}
          </div>
        )}

        {/* 时长 */}
        <div className="absolute bottom-0.5 right-0.5 px-1 py-0.5 bg-black/80 text-white text-[10px] rounded">
          {formatDuration(video.duration)}
        </div>
      </div>

      {/* 信息 */}
      <div className="flex-1 min-w-0 py-0.5">
        <h4 className={cn(
          'text-sm font-medium line-clamp-2 leading-snug',
          isActive ? 'text-blue-400' : 'text-white'
        )}>
          {video.title}
        </h4>
        <p className="text-white/40 text-xs mt-0.5 truncate">
          {video.author.name}
        </p>
      </div>

      {/* 拖拽手柄 */}
      <button
        className="p-1 text-white/20 hover:text-white/50 cursor-grab"
        onClick={(e) => e.stopPropagation()}
      >
        <GripVertical className="w-4 h-4" />
      </button>
    </div>
  );
};

// 迷你播放列表（用于小空间）
export interface MiniPlaylistProps {
  playlist: VideoPlaylistType;
  currentVideoId?: string;
  onVideoClick: (video: Video, index: number) => void;
  className?: string;
}

export const MiniPlaylist: React.FC<MiniPlaylistProps> = ({
  playlist,
  currentVideoId,
  onVideoClick,
  className,
}) => {
  const currentIndex = playlist.videos.findIndex(v => v.id === currentVideoId);
  const totalVideos = playlist.videos.length;

  return (
    <div className={cn('bg-gray-900 rounded-lg p-3', className)}>
      <div className="flex items-center justify-between mb-2">
        <span className="text-white font-medium text-sm">播放列表</span>
        <span className="text-white/40 text-xs">
          {currentIndex + 1} / {totalVideos}
        </span>
      </div>
      
      <div className="space-y-1">
        {playlist.videos.slice(Math.max(0, currentIndex - 1), currentIndex + 3).map((video, idx) => {
          const actualIndex = Math.max(0, currentIndex - 1) + idx;
          const isActive = video.id === currentVideoId;
          
          return (
            <button
              key={video.id}
              onClick={() => onVideoClick(video, actualIndex)}
              className={cn(
                'w-full text-left px-2 py-1.5 rounded text-sm truncate transition-colors',
                isActive ? 'bg-blue-500/20 text-blue-400' : 'text-white/70 hover:bg-white/5'
              )}
            >
              {actualIndex + 1}. {video.title}
            </button>
          );
        })}
      </div>
    </div>
  );
};
