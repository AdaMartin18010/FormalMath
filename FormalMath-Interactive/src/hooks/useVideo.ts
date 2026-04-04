/**
 * 视频播放相关 Hooks
 */

import { useState, useCallback, useRef, useEffect } from 'react';
import type {
  PlayerState,
  PlayerConfig,
  VideoNote,
  SubtitleItem,
  VideoChapter,
  PlaybackProgress,
} from '../types/video';

// 默认播放器配置
const defaultConfig: PlayerConfig = {
  autoPlay: false,
  defaultVolume: 0.8,
  defaultPlaybackRate: 1,
  enableSubtitle: true,
  enableChapter: true,
  enableNote: true,
  theme: 'dark',
};

/**
 * 视频播放器状态管理 Hook
 */
export function useVideoPlayer(config: Partial<PlayerConfig> = {}) {
  const videoRef = useRef<HTMLVideoElement>(null);
  const playerConfig = { ...defaultConfig, ...config };
  
  const [state, setState] = useState<PlayerState>({
    isPlaying: false,
    currentTime: 0,
    duration: 0,
    volume: playerConfig.defaultVolume,
    isMuted: false,
    playbackRate: playerConfig.defaultPlaybackRate,
    isFullscreen: false,
    isPIP: false,
    quality: 'auto',
    buffered: [],
  });

  // 播放/暂停
  const togglePlay = useCallback(() => {
    if (videoRef.current) {
      if (state.isPlaying) {
        videoRef.current.pause();
      } else {
        videoRef.current.play();
      }
    }
  }, [state.isPlaying]);

  // 设置当前时间
  const seekTo = useCallback((time: number) => {
    if (videoRef.current) {
      videoRef.current.currentTime = Math.max(0, Math.min(time, state.duration));
    }
  }, [state.duration]);

  // 快进/快退
  const skip = useCallback((seconds: number) => {
    if (videoRef.current) {
      videoRef.current.currentTime += seconds;
    }
  }, []);

  // 设置音量
  const setVolume = useCallback((volume: number) => {
    if (videoRef.current) {
      const clampedVolume = Math.max(0, Math.min(1, volume));
      videoRef.current.volume = clampedVolume;
      setState(prev => ({ ...prev, volume: clampedVolume }));
    }
  }, []);

  // 静音切换
  const toggleMute = useCallback(() => {
    if (videoRef.current) {
      videoRef.current.muted = !state.isMuted;
    }
  }, [state.isMuted]);

  // 设置播放速度
  const setPlaybackRate = useCallback((rate: number) => {
    if (videoRef.current) {
      videoRef.current.playbackRate = rate;
      setState(prev => ({ ...prev, playbackRate: rate }));
    }
  }, []);

  // 全屏切换
  const toggleFullscreen = useCallback(async () => {
    const videoContainer = videoRef.current?.parentElement;
    if (!videoContainer) return;

    try {
      if (!document.fullscreenElement) {
        await videoContainer.requestFullscreen();
        setState(prev => ({ ...prev, isFullscreen: true }));
      } else {
        await document.exitFullscreen();
        setState(prev => ({ ...prev, isFullscreen: false }));
      }
    } catch (error) {
      console.error('Fullscreen error:', error);
    }
  }, []);

  // 画中画切换
  const togglePIP = useCallback(async () => {
    if (!videoRef.current) return;

    try {
      if (document.pictureInPictureElement) {
        await document.exitPictureInPicture();
        setState(prev => ({ ...prev, isPIP: false }));
      } else {
        await videoRef.current.requestPictureInPicture();
        setState(prev => ({ ...prev, isPIP: true }));
      }
    } catch (error) {
      console.error('PIP error:', error);
    }
  }, []);

  // 视频事件监听
  useEffect(() => {
    const video = videoRef.current;
    if (!video) return;

    const handleTimeUpdate = () => {
      setState(prev => ({ ...prev, currentTime: video.currentTime }));
    };

    const handleDurationChange = () => {
      setState(prev => ({ ...prev, duration: video.duration || 0 }));
    };

    const handlePlay = () => {
      setState(prev => ({ ...prev, isPlaying: true }));
    };

    const handlePause = () => {
      setState(prev => ({ ...prev, isPlaying: false }));
    };

    const handleVolumeChange = () => {
      setState(prev => ({
        ...prev,
        volume: video.volume,
        isMuted: video.muted,
      }));
    };

    const handleProgress = () => {
      const buffered: { start: number; end: number }[] = [];
      for (let i = 0; i < video.buffered.length; i++) {
        buffered.push({
          start: video.buffered.start(i),
          end: video.buffered.end(i),
        });
      }
      setState(prev => ({ ...prev, buffered }));
    };

    video.addEventListener('timeupdate', handleTimeUpdate);
    video.addEventListener('durationchange', handleDurationChange);
    video.addEventListener('play', handlePlay);
    video.addEventListener('pause', handlePause);
    video.addEventListener('volumechange', handleVolumeChange);
    video.addEventListener('progress', handleProgress);

    return () => {
      video.removeEventListener('timeupdate', handleTimeUpdate);
      video.removeEventListener('durationchange', handleDurationChange);
      video.removeEventListener('play', handlePlay);
      video.removeEventListener('pause', handlePause);
      video.removeEventListener('volumechange', handleVolumeChange);
      video.removeEventListener('progress', handleProgress);
    };
  }, []);

  return {
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
  };
}

/**
 * 视频笔记 Hook
 */
export function useVideoNotes(videoId: string) {
  const [notes, setNotes] = useState<VideoNote[]>([]);
  const [isLoading, setIsLoading] = useState(false);

  // 加载笔记
  const loadNotes = useCallback(async () => {
    setIsLoading(true);
    try {
      // TODO: 调用API加载笔记
      const stored = localStorage.getItem(`video-notes-${videoId}`);
      if (stored) {
        setNotes(JSON.parse(stored));
      }
    } finally {
      setIsLoading(false);
    }
  }, [videoId]);

  // 添加笔记
  const addNote = useCallback((note: Omit<VideoNote, 'id' | 'createdAt' | 'updatedAt' | 'likes'>) => {
    const newNote: VideoNote = {
      ...note,
      id: `note-${Date.now()}`,
      createdAt: new Date().toISOString(),
      updatedAt: new Date().toISOString(),
      likes: 0,
    };
    
    setNotes(prev => {
      const updated = [...prev, newNote];
      localStorage.setItem(`video-notes-${videoId}`, JSON.stringify(updated));
      return updated;
    });
    
    return newNote;
  }, [videoId]);

  // 更新笔记
  const updateNote = useCallback((noteId: string, updates: Partial<VideoNote>) => {
    setNotes(prev => {
      const updated = prev.map(note =>
        note.id === noteId
          ? { ...note, ...updates, updatedAt: new Date().toISOString() }
          : note
      );
      localStorage.setItem(`video-notes-${videoId}`, JSON.stringify(updated));
      return updated;
    });
  }, [videoId]);

  // 删除笔记
  const deleteNote = useCallback((noteId: string) => {
    setNotes(prev => {
      const updated = prev.filter(note => note.id !== noteId);
      localStorage.setItem(`video-notes-${videoId}`, JSON.stringify(updated));
      return updated;
    });
  }, [videoId]);

  // 获取指定时间点的笔记
  const getNotesAtTime = useCallback((timestamp: number, window: number = 5) => {
    return notes.filter(
      note => Math.abs(note.timestamp - timestamp) <= window
    );
  }, [notes]);

  useEffect(() => {
    loadNotes();
  }, [loadNotes]);

  return {
    notes,
    isLoading,
    addNote,
    updateNote,
    deleteNote,
    getNotesAtTime,
    refresh: loadNotes,
  };
}

/**
 * 字幕 Hook
 */
export function useSubtitles(subtitles: SubtitleItem[] = []) {
  const [currentSubtitle, setCurrentSubtitle] = useState<SubtitleItem | null>(null);
  const [isVisible, setIsVisible] = useState(true);

  // 根据时间获取当前字幕
  const getSubtitleAtTime = useCallback((time: number) => {
    return subtitles.find(
      sub => time >= sub.startTime && time <= sub.endTime
    ) || null;
  }, [subtitles]);

  // 更新当前字幕
  const updateCurrentSubtitle = useCallback((time: number) => {
    const subtitle = getSubtitleAtTime(time);
    setCurrentSubtitle(subtitle);
  }, [getSubtitleAtTime]);

  // 跳转到字幕时间
  const seekToSubtitle = useCallback((subtitle: SubtitleItem) => {
    return subtitle.startTime;
  }, []);

  return {
    currentSubtitle,
    isVisible,
    setIsVisible,
    updateCurrentSubtitle,
    seekToSubtitle,
    subtitles,
  };
}

/**
 * 视频章节 Hook
 */
export function useVideoChapters(chapters: VideoChapter[] = []) {
  const [activeChapter, setActiveChapter] = useState<VideoChapter | null>(null);

  // 获取当前章节
  const getChapterAtTime = useCallback((time: number) => {
    return chapters.find((chapter, index) => {
      const nextChapter = chapters[index + 1];
      const endTime = nextChapter ? nextChapter.startTime : Infinity;
      return time >= chapter.startTime && time < endTime;
    }) || null;
  }, [chapters]);

  // 更新当前章节
  const updateActiveChapter = useCallback((time: number) => {
    const chapter = getChapterAtTime(time);
    setActiveChapter(chapter);
  }, [getChapterAtTime]);

  // 跳转到章节
  const seekToChapter = useCallback((chapter: VideoChapter) => {
    return chapter.startTime;
  }, []);

  // 获取下一章节
  const getNextChapter = useCallback((time: number) => {
    return chapters.find(ch => ch.startTime > time) || null;
  }, [chapters]);

  // 获取上一章节
  const getPrevChapter = useCallback((time: number) => {
    const prevChapters = chapters.filter(ch => ch.startTime < time);
    return prevChapters[prevChapters.length - 1] || null;
  }, [chapters]);

  return {
    chapters,
    activeChapter,
    updateActiveChapter,
    seekToChapter,
    getNextChapter,
    getPrevChapter,
  };
}

/**
 * 播放进度保存 Hook
 */
export function usePlaybackProgress(videoId: string) {
  const saveProgress = useCallback((progress: Partial<PlaybackProgress>) => {
    const key = `video-progress-${videoId}`;
    const existing = localStorage.getItem(key);
    const current: Partial<PlaybackProgress> = existing ? JSON.parse(existing) : {};
    
    const updated: PlaybackProgress = {
      videoId,
      userId: current.userId || 'anonymous',
      currentTime: progress.currentTime ?? current.currentTime ?? 0,
      duration: progress.duration ?? current.duration ?? 0,
      completed: progress.completed ?? current.completed ?? false,
      lastWatchedAt: new Date().toISOString(),
      watchCount: (current.watchCount || 0) + 1,
    };
    
    localStorage.setItem(key, JSON.stringify(updated));
  }, [videoId]);

  const loadProgress = useCallback((): PlaybackProgress | null => {
    const key = `video-progress-${videoId}`;
    const stored = localStorage.getItem(key);
    return stored ? JSON.parse(stored) : null;
  }, [videoId]);

  return { saveProgress, loadProgress };
}
