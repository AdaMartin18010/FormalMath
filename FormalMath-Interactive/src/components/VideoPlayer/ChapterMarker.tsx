/**
 * 视频章节标记组件
 */

import React, { useState } from 'react';
import { ChevronRight, Clock, BookOpen } from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { ChapterMarkerProps } from './types';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const ChapterMarker: React.FC<ChapterMarkerProps> = ({
  chapters,
  duration,
  currentTime,
  onChapterClick,
  className,
}) => {
  const [expandedChapter, setExpandedChapter] = useState<string | null>(null);

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

  // 获取当前章节
  const getCurrentChapter = () => {
    return chapters.find((chapter, index) => {
      const nextChapter = chapters[index + 1];
      const endTime = nextChapter ? nextChapter.startTime : duration;
      return currentTime >= chapter.startTime && currentTime < endTime;
    });
  };

  // 获取章节进度百分比
  const getChapterProgress = (chapter: typeof chapters[0], index: number): number => {
    const nextChapter = chapters[index + 1];
    const endTime = nextChapter ? nextChapter.startTime : duration;
    const chapterDuration = endTime - chapter.startTime;
    
    if (currentTime <= chapter.startTime) return 0;
    if (currentTime >= endTime) return 100;
    
    return ((currentTime - chapter.startTime) / chapterDuration) * 100;
  };

  const currentChapter = getCurrentChapter();

  return (
    <div className={cn('bg-gray-900/95 rounded-lg overflow-hidden', className)}>
      {/* 头部 - 当前章节 */}
      {currentChapter && (
        <div className="px-4 py-3 border-b border-white/10">
          <div className="flex items-center gap-2 text-white/60 text-xs mb-1">
            <BookOpen className="w-3 h-3" />
            <span>当前章节</span>
          </div>
          <div className="text-white font-medium">{currentChapter.title}</div>
        </div>
      )}

      {/* 章节列表 */}
      <div className="max-h-64 overflow-y-auto">
        {chapters.map((chapter, index) => {
          const isActive = currentChapter?.id === chapter.id;
          const isExpanded = expandedChapter === chapter.id;
          const progress = getChapterProgress(chapter, index);

          return (
            <div
              key={chapter.id}
              className={cn(
                'border-b border-white/5 last:border-b-0 transition-colors',
                isActive ? 'bg-blue-500/20' : 'hover:bg-white/5'
              )}
            >
              <button
                onClick={() => onChapterClick(chapter)}
                className="w-full px-4 py-3 flex items-start gap-3 text-left"
              >
                {/* 章节缩略图或序号 */}
                <div className="relative flex-shrink-0 w-16 h-10 bg-gray-800 rounded overflow-hidden">
                  {chapter.thumbnail ? (
                    <img
                      src={chapter.thumbnail}
                      alt={chapter.title}
                      className="w-full h-full object-cover"
                    />
                  ) : (
                    <div className="w-full h-full flex items-center justify-center text-white/30 text-lg font-bold">
                      {index + 1}
                    </div>
                  )}
                  {/* 播放进度指示 */}
                  {isActive && (
                    <div
                      className="absolute bottom-0 left-0 h-0.5 bg-blue-500 transition-all"
                      style={{ width: `${progress}%` }}
                    />
                  )}
                  {/* 已完成标记 */}
                  {!isActive && currentTime > chapter.startTime && (
                    <div className="absolute inset-0 bg-blue-500/20 flex items-center justify-center">
                      <div className="w-5 h-5 rounded-full bg-blue-500 flex items-center justify-center">
                        <svg className="w-3 h-3 text-white" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={3} d="M5 13l4 4L19 7" />
                        </svg>
                      </div>
                    </div>
                  )}
                </div>

                {/* 章节信息 */}
                <div className="flex-1 min-w-0">
                  <div className={cn(
                    'font-medium text-sm truncate',
                    isActive ? 'text-blue-400' : 'text-white'
                  )}>
                    {chapter.title}
                  </div>
                  <div className="flex items-center gap-2 mt-1">
                    <Clock className="w-3 h-3 text-white/40" />
                    <span className="text-xs text-white/50">{formatTime(chapter.startTime)}</span>
                  </div>
                </div>

                {/* 展开按钮 */}
                {chapter.description && (
                  <button
                    onClick={(e) => {
                      e.stopPropagation();
                      setExpandedChapter(isExpanded ? null : chapter.id);
                    }}
                    className="p-1 text-white/40 hover:text-white/70 transition-colors"
                  >
                    <ChevronRight className={cn(
                      'w-4 h-4 transition-transform',
                      isExpanded && 'rotate-90'
                    )} />
                  </button>
                )}
              </button>

              {/* 展开的描述 */}
              {isExpanded && chapter.description && (
                <div className="px-4 pb-3 pl-23">
                  <p className="text-sm text-white/60 leading-relaxed">
                    {chapter.description}
                  </p>
                </div>
              )}
            </div>
          );
        })}
      </div>

      {/* 底部统计 */}
      <div className="px-4 py-2 bg-black/30 text-xs text-white/40 flex items-center justify-between">
        <span>共 {chapters.length} 个章节</span>
        <span>总时长 {formatTime(duration)}</span>
      </div>
    </div>
  );
};
