/**
 * 视频播放器核心组件
 */

import React, { useEffect, useCallback, useState } from 'react';
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
  PictureInPicture2
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoPlayerProps } from './types';
import { useVideoPlayer, useSubtitles, useVideoChapters, usePlaybackProgress } from '../../hooks/useVideo';
import { VideoControls } from './VideoControls';
import { VideoProgressBar } from './VideoProgressBar';
import { SubtitleDisplay } from './SubtitleDisplay';
import { ChapterMarker } from './ChapterMarker';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export const VideoPlayer: React.FC<VideoPlayerProps> = ({
  video,
  config = {},
  chapters = [],
  subtitles = [],
  onTimeUpdate,
  onEnded,
  onPlay,
  onPause,
  className,
}) => {
  const {
    videoRef,
    state,
    togglePlay,
    seekTo,
    skip,
    setVolume,
    toggleMute,
    setPlaybackRate,
    toggleFullscreen,
    togglePIP,
  } = useVideoPlayer(config);

  const [showControls, setShowControls] = useState(true);
  const [controlsTimeout, setControlsTimeout] = useState<NodeJS.Timeout | null>(null);
  const [selectedSubtitleTrack, setSelectedSubtitleTrack] = useState<string | null>(
    subtitles.find(s => s.isDefault)?.id || null
  );

  const { 
    currentSubtitle, 
    isVisible: subtitlesVisible, 
    setIsVisible: setSubtitlesVisible,
    updateCurrentSubtitle 
  } = useSubtitles(
    subtitles.find(s => s.id === selectedSubtitleTrack)?.subtitles || []
  );

  const { activeChapter, updateActiveChapter, seekToChapter } = useVideoChapters(chapters);
  const { saveProgress, loadProgress } = usePlaybackProgress(video.id);

  // 加载保存的进度
  useEffect(() => {
    const progress = loadProgress();
    if (progress && videoRef.current) {
      videoRef.current.currentTime = progress.currentTime;
    }
  }, [loadProgress]);

  // 时间更新处理
  useEffect(() => {
    updateCurrentSubtitle(state.currentTime);
    updateActiveChapter(state.currentTime);
    onTimeUpdate?.(state.currentTime);
    
    // 每5秒保存一次进度
    if (Math.floor(state.currentTime) % 5 === 0) {
      saveProgress({
        currentTime: state.currentTime,
        duration: state.duration,
      });
    }
  }, [state.currentTime, updateCurrentSubtitle, updateActiveChapter, onTimeUpdate, saveProgress]);

  // 键盘快捷键
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.target instanceof HTMLInputElement || e.target instanceof HTMLTextAreaElement) {
        return;
      }

      switch (e.key.toLowerCase()) {
        case ' ':
        case 'k':
          e.preventDefault();
          togglePlay();
          break;
        case 'arrowleft':
          e.preventDefault();
          skip(e.shiftKey ? -10 : -5);
          break;
        case 'arrowright':
          e.preventDefault();
          skip(e.shiftKey ? 10 : 5);
          break;
        case 'arrowup':
          e.preventDefault();
          setVolume(state.volume + 0.1);
          break;
        case 'arrowdown':
          e.preventDefault();
          setVolume(state.volume - 0.1);
          break;
        case 'f':
          e.preventDefault();
          toggleFullscreen();
          break;
        case 'm':
          e.preventDefault();
          toggleMute();
          break;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [togglePlay, skip, setVolume, toggleFullscreen, toggleMute, state.volume]);

  // 控制栏显示/隐藏
  const handleMouseMove = useCallback(() => {
    setShowControls(true);
    if (controlsTimeout) {
      clearTimeout(controlsTimeout);
    }
    if (state.isPlaying) {
      const timeout = setTimeout(() => setShowControls(false), 3000);
      setControlsTimeout(timeout);
    }
  }, [controlsTimeout, state.isPlaying]);

  // 视频结束处理
  const handleEnded = useCallback(() => {
    saveProgress({
      currentTime: state.duration,
      duration: state.duration,
      completed: true,
    });
    onEnded?.();
  }, [onEnded, saveProgress, state.duration]);

  // 格式化时间
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
    <div
      className={cn(
        'relative group bg-black rounded-lg overflow-hidden',
        state.isFullscreen ? 'fixed inset-0 z-50 rounded-none' : '',
        className
      )}
      onMouseMove={handleMouseMove}
      onMouseLeave={() => state.isPlaying && setShowControls(false)}
    >
      {/* 视频元素 */}
      <video
        ref={videoRef}
        src={video.url}
        className="w-full h-full object-contain"
        onEnded={handleEnded}
        onPlay={onPlay}
        onPause={onPause}
        autoPlay={config.autoPlay}
      />

      {/* 字幕显示 */}
      {config.enableSubtitle !== false && (
        <SubtitleDisplay
          subtitle={currentSubtitle}
          isVisible={subtitlesVisible}
          className="absolute bottom-20 left-1/2 -translate-x-1/2"
        />
      )}

      {/* 章节标记（在进度条上方） */}
      {config.enableChapter !== false && chapters.length > 0 && (
        <div className="absolute bottom-16 left-4 right-4 opacity-0 group-hover:opacity-100 transition-opacity">
          <ChapterMarker
            chapters={chapters}
            duration={state.duration}
            currentTime={state.currentTime}
            onChapterClick={(chapter) => seekTo(chapter.startTime)}
          />
        </div>
      )}

      {/* 控制栏 */}
      <div
        className={cn(
          'absolute bottom-0 left-0 right-0 bg-gradient-to-t from-black/90 via-black/50 to-transparent',
          'transition-opacity duration-300',
          showControls ? 'opacity-100' : 'opacity-0'
        )}
      >
        {/* 进度条 */}
        <div className="px-4 pt-4 pb-2">
          <VideoProgressBar
            currentTime={state.currentTime}
            duration={state.duration}
            buffered={state.buffered}
            chapters={chapters}
            onSeek={seekTo}
          />
        </div>

        {/* 控制按钮 */}
        <VideoControls
          isPlaying={state.isPlaying}
          currentTime={state.currentTime}
          duration={state.duration}
          volume={state.volume}
          isMuted={state.isMuted}
          playbackRate={state.playbackRate}
          isFullscreen={state.isFullscreen}
          buffered={state.buffered}
          onPlayPause={togglePlay}
          onSeek={seekTo}
          onVolumeChange={setVolume}
          onMuteToggle={toggleMute}
          onPlaybackRateChange={setPlaybackRate}
          onFullscreenToggle={toggleFullscreen}
          onSkip={skip}
        />
      </div>

      {/* 加载动画 */}
      {!state.duration && (
        <div className="absolute inset-0 flex items-center justify-center bg-black/50">
          <div className="w-12 h-12 border-4 border-white/30 border-t-white rounded-full animate-spin" />
        </div>
      )}

      {/* 当前章节标题 */}
      {activeChapter && showControls && (
        <div className="absolute top-4 left-4 bg-black/60 text-white px-3 py-1.5 rounded-lg text-sm">
          {activeChapter.title}
        </div>
      )}
    </div>
  );
};
