/**
 * 视频字幕显示组件
 */

import React from 'react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { SubtitleDisplayProps } from './types';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const SubtitleDisplay: React.FC<SubtitleDisplayProps> = ({
  subtitle,
  isVisible,
  position = 'bottom',
  style = 'with-bg',
  className,
}) => {
  if (!subtitle || !isVisible) return null;

  return (
    <div
      className={cn(
        'transition-all duration-300 z-20 max-w-[80%] text-center',
        position === 'bottom' ? 'mb-4' : 'mt-4',
        className
      )}
    >
      <div
        className={cn(
          'px-4 py-2 rounded-lg transition-all',
          style === 'default' && 'text-white drop-shadow-lg',
          style === 'large' && 'text-xl text-white drop-shadow-lg',
          style === 'with-bg' && 'bg-black/70 text-white text-lg',
          'animate-in fade-in slide-in-from-bottom-2 duration-200'
        )}
      >
        {subtitle.text.split('\n').map((line, index) => (
          <p key={index} className="leading-relaxed">
            {line}
          </p>
        ))}
      </div>
    </div>
  );
};

/**
 * 字幕选择器组件
 */
export interface SubtitleSelectorProps {
  tracks: Array<{
    id: string;
    label: string;
    language: string;
  }>;
  selectedId: string | null;
  isVisible: boolean;
  onSelect: (trackId: string | null) => void;
  onToggleVisibility: () => void;
  className?: string;
}

export const SubtitleSelector: React.FC<SubtitleSelectorProps> = ({
  tracks,
  selectedId,
  isVisible,
  onSelect,
  onToggleVisibility,
  className,
}) => {
  return (
    <div className={cn('relative', className)}>
      <button
        onClick={onToggleVisibility}
        className={cn(
          'p-2 rounded-lg transition-colors',
          isVisible
            ? 'bg-blue-500 text-white'
            : 'text-white/70 hover:text-white hover:bg-white/10'
        )}
        title={isVisible ? '隐藏字幕' : '显示字幕'}
      >
        <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M7 8h10M7 12h4m1 8l-4-4H5a2 2 0 01-2-2V6a2 2 0 012-2h14a2 2 0 012 2v8a2 2 0 01-2 2h-3l-4 4z" />
        </svg>
      </button>

      {/* 字幕轨道选择 */}
      {tracks.length > 0 && (
        <select
          value={selectedId || ''}
          onChange={(e) => onSelect(e.target.value || null)}
          className="ml-2 bg-white/10 text-white text-sm rounded px-2 py-1 border border-white/20 focus:outline-none focus:border-blue-500"
        >
          <option value="" className="bg-gray-900">关闭字幕</option>
          {tracks.map((track) => (
            <option key={track.id} value={track.id} className="bg-gray-900">
              {track.label}
            </option>
          ))}
        </select>
      )}
    </div>
  );
};

/**
 * 字幕搜索组件 - 用于跳转到特定字幕
 */
export interface SubtitleSearchProps {
  subtitles: Array<{
    id: string;
    text: string;
    startTime: number;
  }>;
  onSubtitleClick: (time: number) => void;
  className?: string;
}

export const SubtitleSearch: React.FC<SubtitleSearchProps> = ({
  subtitles,
  onSubtitleClick,
  className,
}) => {
  const [searchTerm, setSearchTerm] = React.useState('');
  const [isOpen, setIsOpen] = React.useState(false);

  const filteredSubtitles = searchTerm
    ? subtitles.filter(sub => 
        sub.text.toLowerCase().includes(searchTerm.toLowerCase())
      )
    : [];

  const formatTime = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  return (
    <div className={cn('relative', className)}>
      <button
        onClick={() => setIsOpen(!isOpen)}
        className="p-2 text-white/70 hover:text-white hover:bg-white/10 rounded-lg transition-colors"
      >
        <svg className="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
          <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M21 21l-6-6m2-5a7 7 0 11-14 0 7 7 0 0114 0z" />
        </svg>
      </button>

      {isOpen && (
        <div className="absolute bottom-full right-0 mb-2 w-80 bg-gray-900 rounded-lg shadow-xl overflow-hidden">
          <div className="p-3 border-b border-white/10">
            <input
              type="text"
              placeholder="搜索字幕..."
              value={searchTerm}
              onChange={(e) => setSearchTerm(e.target.value)}
              className="w-full bg-white/10 text-white px-3 py-2 rounded-lg placeholder-white/40 focus:outline-none focus:ring-2 focus:ring-blue-500"
              autoFocus
            />
          </div>
          
          <div className="max-h-64 overflow-y-auto">
            {filteredSubtitles.length === 0 ? (
              <div className="p-4 text-center text-white/40 text-sm">
                {searchTerm ? '未找到匹配的字幕' : '输入关键词搜索字幕'}
              </div>
            ) : (
              filteredSubtitles.map((sub) => (
                <button
                  key={sub.id}
                  onClick={() => {
                    onSubtitleClick(sub.startTime);
                    setIsOpen(false);
                    setSearchTerm('');
                  }}
                  className="w-full px-4 py-3 text-left hover:bg-white/5 transition-colors border-b border-white/5 last:border-b-0"
                >
                  <div className="text-blue-400 text-xs mb-1">{formatTime(sub.startTime)}</div>
                  <div className="text-white text-sm line-clamp-2">{sub.text}</div>
                </button>
              ))
            )}
          </div>
        </div>
      )}
    </div>
  );
};
