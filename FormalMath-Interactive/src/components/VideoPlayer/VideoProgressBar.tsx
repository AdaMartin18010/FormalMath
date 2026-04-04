/**
 * 视频进度条组件 - 支持章节标记和缓冲显示
 */

import React, { useState, useCallback, useRef } from 'react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoProgressBarProps } from './types';
import type { VideoChapter } from '../../types/video';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const VideoProgressBar: React.FC<VideoProgressBarProps> = ({
  currentTime,
  duration,
  buffered,
  chapters = [],
  onSeek,
  className,
}) => {
  const progressRef = useRef<HTMLDivElement>(null);
  const [hoverTime, setHoverTime] = useState<number | null>(null);
  const [hoverChapter, setHoverChapter] = useState<VideoChapter | null>(null);
  const [isDragging, setIsDragging] = useState(false);

  const progress = duration > 0 ? (currentTime / duration) * 100 : 0;

  // 计算鼠标位置对应的时间
  const calculateTimeFromPosition = useCallback((clientX: number): number => {
    if (!progressRef.current || duration <= 0) return 0;
    
    const rect = progressRef.current.getBoundingClientRect();
    const position = (clientX - rect.left) / rect.width;
    return Math.max(0, Math.min(duration, position * duration));
  }, [duration]);

  // 鼠标移动处理
  const handleMouseMove = useCallback((e: React.MouseEvent) => {
    const time = calculateTimeFromPosition(e.clientX);
    setHoverTime(time);
    
    // 查找悬停的章节
    const chapter = chapters.find((ch, index) => {
      const nextChapter = chapters[index + 1];
      const endTime = nextChapter ? nextChapter.startTime : duration;
      return time >= ch.startTime && time < endTime;
    });
    setHoverChapter(chapter || null);

    if (isDragging) {
      onSeek(time);
    }
  }, [calculateTimeFromPosition, chapters, duration, isDragging, onSeek]);

  // 鼠标离开处理
  const handleMouseLeave = useCallback(() => {
    setHoverTime(null);
    setHoverChapter(null);
    setIsDragging(false);
  }, []);

  // 点击/开始拖拽处理
  const handleMouseDown = useCallback((e: React.MouseEvent) => {
    setIsDragging(true);
    const time = calculateTimeFromPosition(e.clientX);
    onSeek(time);
  }, [calculateTimeFromPosition, onSeek]);

  // 全局鼠标释放处理
  const handleGlobalMouseUp = useCallback(() => {
    setIsDragging(false);
  }, []);

  // 格式化时间显示
  const formatTime = (seconds: number): string => {
    if (!isFinite(seconds)) return '0:00';
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    const hours = Math.floor(mins / 60);
    
    if (hours > 0) {
      return `${hours}:${String(mins % 60).padStart(2, '0')}:${String(secs).padStart(2, '0')}`;
    }
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  // 计算章节标记位置
  const getChapterPosition = (startTime: number): number => {
    return duration > 0 ? (startTime / duration) * 100 : 0;
  };

  return (
    <div
      ref={progressRef}
      className={cn('relative h-2 cursor-pointer group', className)}
      onMouseMove={handleMouseMove}
      onMouseLeave={handleMouseLeave}
      onMouseDown={handleMouseDown}
      onMouseUp={handleGlobalMouseUp}
    >
      {/* 背景轨道 */}
      <div className="absolute inset-0 bg-white/20 rounded-full overflow-visible">
        {/* 缓冲进度 */}
        {buffered.map((range, index) => {
          const start = duration > 0 ? (range.start / duration) * 100 : 0;
          const end = duration > 0 ? (range.end / duration) * 100 : 0;
          return (
            <div
              key={index}
              className="absolute h-full bg-white/30 rounded-full"
              style={{
                left: `${start}%`,
                width: `${end - start}%`,
              }}
            />
          );
        })}

        {/* 播放进度 */}
        <div
          className="absolute h-full bg-blue-500 rounded-full transition-all duration-100"
          style={{ width: `${progress}%` }}
        />

        {/* 章节标记 */}
        {chapters.map((chapter, index) => {
          const position = getChapterPosition(chapter.startTime);
          return (
            <div
              key={chapter.id}
              className={cn(
                'absolute top-1/2 -translate-y-1/2 w-1 h-3 rounded-full transition-all',
                hoverChapter?.id === chapter.id
                  ? 'bg-yellow-400 scale-125'
                  : 'bg-white/60 hover:bg-white'
              )}
              style={{ left: `${position}%` }}
              title={chapter.title}
            />
          );
        })}
      </div>

      {/* 悬停预览 */}
      {hoverTime !== null && !isDragging && (
        <div
          className="absolute -top-12 transform -translate-x-1/2 bg-gray-900 text-white px-3 py-1.5 rounded-lg text-sm whitespace-nowrap z-10"
          style={{
            left: `${duration > 0 ? (hoverTime / duration) * 100 : 0}%`,
          }}
        >
          <div className="font-medium">{formatTime(hoverTime)}</div>
          {hoverChapter && (
            <div className="text-xs text-white/70 mt-0.5">{hoverChapter.title}</div>
          )}
          {/* 小三角 */}
          <div className="absolute -bottom-1 left-1/2 -translate-x-1/2 w-2 h-2 bg-gray-900 rotate-45" />
        </div>
      )}

      {/* 拖拽指示器 */}
      <div
        className={cn(
          'absolute top-1/2 -translate-y-1/2 w-4 h-4 bg-white rounded-full shadow-lg transform -translate-x-1/2 transition-transform',
          isDragging ? 'scale-125' : 'scale-0 group-hover:scale-100'
        )}
        style={{ left: `${progress}%` }}
      />
    </div>
  );
};
