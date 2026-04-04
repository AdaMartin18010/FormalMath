/**
 * 视频播放器组件 Props 类型定义
 */

import type {
  Video,
  VideoChapter,
  SubtitleTrack,
  VideoNote,
  VideoRecommendation,
  VideoPlaylist as VideoPlaylistType,
  PlayerConfig,
} from '../../types/video';

// 视频播放器 Props
export interface VideoPlayerProps {
  video: Video;
  config?: Partial<PlayerConfig>;
  chapters?: VideoChapter[];
  subtitles?: SubtitleTrack[];
  onTimeUpdate?: (time: number) => void;
  onEnded?: () => void;
  onPlay?: () => void;
  onPause?: () => void;
  className?: string;
}

// 视频播放器容器 Props
export interface VideoPlayerContainerProps {
  video: Video;
  relatedVideos?: Video[];
  chapters?: VideoChapter[];
  subtitles?: SubtitleTrack[];
  recommendations?: VideoRecommendation[];
  playlist?: VideoPlaylistType;
  config?: Partial<PlayerConfig>;
  onVideoEnd?: () => void;
  onVideoChange?: (video: Video) => void;
}

// 章节标记 Props
export interface ChapterMarkerProps {
  chapters: VideoChapter[];
  duration: number;
  currentTime: number;
  onChapterClick: (chapter: VideoChapter) => void;
  className?: string;
}

// 字幕显示 Props
export interface SubtitleDisplayProps {
  subtitle: { text: string } | null;
  isVisible: boolean;
  position?: 'bottom' | 'top';
  style?: 'default' | 'large' | 'with-bg';
  className?: string;
}

// 视频笔记 Props
export interface VideoNotesProps {
  videoId: string;
  currentTime: number;
  isPlaying: boolean;
  onTimestampClick?: (time: number) => void;
  className?: string;
}

// 视频推荐 Props
export interface VideoRecommendationsProps {
  recommendations: VideoRecommendation[];
  onVideoClick: (video: Video) => void;
  className?: string;
}

// 视频控制栏 Props
export interface VideoControlsProps {
  isPlaying: boolean;
  currentTime: number;
  duration: number;
  volume: number;
  isMuted: boolean;
  playbackRate: number;
  isFullscreen: boolean;
  buffered: { start: number; end: number }[];
  onPlayPause: () => void;
  onSeek: (time: number) => void;
  onVolumeChange: (volume: number) => void;
  onMuteToggle: () => void;
  onPlaybackRateChange: (rate: number) => void;
  onFullscreenToggle: () => void;
  onSkip: (seconds: number) => void;
  className?: string;
}

// 视频进度条 Props
export interface VideoProgressBarProps {
  currentTime: number;
  duration: number;
  buffered: { start: number; end: number }[];
  chapters?: VideoChapter[];
  onSeek: (time: number) => void;
  className?: string;
}

// 播放列表 Props
export interface VideoPlaylistProps {
  playlist: VideoPlaylistType;
  currentVideoId?: string;
  onVideoClick: (video: Video, index: number) => void;
  className?: string;
}

// 视频卡片 Props
export interface VideoCardProps {
  video: Video;
  progress?: number;
  onClick?: () => void;
  className?: string;
}

// 笔记编辑器 Props
export interface NoteEditorProps {
  timestamp: number;
  initialContent?: string;
  onSave: (content: string, type: VideoNote['type']) => void;
  onCancel: () => void;
}
