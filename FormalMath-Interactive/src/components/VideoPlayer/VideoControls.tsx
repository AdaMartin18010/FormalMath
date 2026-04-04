/**
 * 视频控制栏组件
 */

import React, { useState, useRef, useEffect } from 'react';
import {
  Play,
  Pause,
  Volume2,
  VolumeX,
  Maximize,
  Minimize,
  SkipBack,
  SkipForward,
  Settings,
  PictureInPicture2,
  ChevronRight,
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoControlsProps } from './types';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

const PLAYBACK_RATES = [0.25, 0.5, 0.75, 1, 1.25, 1.5, 1.75, 2];

export const VideoControls: React.FC<VideoControlsProps> = ({
  isPlaying,
  currentTime,
  duration,
  volume,
  isMuted,
  playbackRate,
  isFullscreen,
  onPlayPause,
  onSeek,
  onVolumeChange,
  onMuteToggle,
  onPlaybackRateChange,
  onFullscreenToggle,
  onSkip,
  className,
}) => {
  const [showSettings, setShowSettings] = useState(false);
  const [showVolumeSlider, setShowVolumeSlider] = useState(false);
  const settingsRef = useRef<HTMLDivElement>(null);
  const volumeRef = useRef<HTMLDivElement>(null);

  // 点击外部关闭设置菜单
  useEffect(() => {
    const handleClickOutside = (e: MouseEvent) => {
      if (settingsRef.current && !settingsRef.current.contains(e.target as Node)) {
        setShowSettings(false);
      }
      if (volumeRef.current && !volumeRef.current.contains(e.target as Node)) {
        setShowVolumeSlider(false);
      }
    };

    document.addEventListener('mousedown', handleClickOutside);
    return () => document.removeEventListener('mousedown', handleClickOutside);
  }, []);

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

  return (
    <div className={cn('flex items-center gap-2 px-4 pb-4', className)}>
      {/* 播放/暂停 */}
      <button
        onClick={onPlayPause}
        className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
        aria-label={isPlaying ? '暂停' : '播放'}
      >
        {isPlaying ? <Pause className="w-5 h-5" /> : <Play className="w-5 h-5" />}
      </button>

      {/* 快退 */}
      <button
        onClick={() => onSkip(-10)}
        className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
        aria-label="快退10秒"
      >
        <SkipBack className="w-5 h-5" />
      </button>

      {/* 快进 */}
      <button
        onClick={() => onSkip(10)}
        className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
        aria-label="快进10秒"
      >
        <SkipForward className="w-5 h-5" />
      </button>

      {/* 音量控制 */}
      <div 
        ref={volumeRef}
        className="relative flex items-center"
        onMouseEnter={() => setShowVolumeSlider(true)}
      >
        <button
          onClick={onMuteToggle}
          className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
          aria-label={isMuted ? '取消静音' : '静音'}
        >
          {isMuted || volume === 0 ? (
            <VolumeX className="w-5 h-5" />
          ) : (
            <Volume2 className="w-5 h-5" />
          )}
        </button>

        {showVolumeSlider && (
          <div className="absolute bottom-full left-1/2 -translate-x-1/2 mb-2 p-3 bg-gray-900 rounded-lg">
            <input
              type="range"
              min="0"
              max="1"
              step="0.05"
              value={isMuted ? 0 : volume}
              onChange={(e) => onVolumeChange(parseFloat(e.target.value))}
              className="w-24 accent-blue-500"
            />
          </div>
        )}
      </div>

      {/* 时间显示 */}
      <div className="text-white text-sm font-medium tabular-nums">
        <span>{formatTime(currentTime)}</span>
        <span className="mx-1">/</span>
        <span className="text-white/70">{formatTime(duration)}</span>
      </div>

      {/* 右侧控制 */}
      <div className="flex items-center gap-1 ml-auto">
        {/* 播放速度 */}
        <div ref={settingsRef} className="relative">
          <button
            onClick={() => setShowSettings(!showSettings)}
            className={cn(
              'p-2 text-white rounded-lg transition-colors flex items-center gap-1',
              showSettings ? 'bg-white/20' : 'hover:bg-white/20'
            )}
          >
            <Settings className="w-4 h-4" />
            <span className="text-xs">{playbackRate}x</span>
          </button>

          {showSettings && (
            <div className="absolute bottom-full right-0 mb-2 p-2 bg-gray-900 rounded-lg min-w-[120px]">
              <div className="text-white/70 text-xs mb-2 px-2">播放速度</div>
              {PLAYBACK_RATES.map((rate) => (
                <button
                  key={rate}
                  onClick={() => {
                    onPlaybackRateChange(rate);
                    setShowSettings(false);
                  }}
                  className={cn(
                    'w-full text-left px-3 py-1.5 text-sm rounded transition-colors',
                    rate === playbackRate
                      ? 'bg-blue-500 text-white'
                      : 'text-white hover:bg-white/10'
                  )}
                >
                  {rate === 1 ? '正常' : `${rate}x`}
                </button>
              ))}
            </div>
          )}
        </div>

        {/* 画中画 */}
        <button
          onClick={() => {}}
          className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
          aria-label="画中画"
        >
          <PictureInPicture2 className="w-5 h-5" />
        </button>

        {/* 全屏 */}
        <button
          onClick={onFullscreenToggle}
          className="p-2 text-white hover:bg-white/20 rounded-lg transition-colors"
          aria-label={isFullscreen ? '退出全屏' : '全屏'}
        >
          {isFullscreen ? (
            <Minimize className="w-5 h-5" />
          ) : (
            <Maximize className="w-5 h-5" />
          )}
        </button>
      </div>
    </div>
  );
};
