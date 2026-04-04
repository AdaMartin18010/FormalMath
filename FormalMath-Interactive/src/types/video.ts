/**
 * 视频内容类型定义
 */

// 视频基础信息
export interface Video {
  id: string;
  title: string;
  description: string;
  thumbnail: string;
  duration: number; // 秒
  url: string;
  author: VideoAuthor;
  category: VideoCategory;
  tags: string[];
  createdAt: string;
  updatedAt: string;
  viewCount: number;
  likeCount: number;
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  relatedConcepts: string[]; // 关联的概念ID
}

// 视频作者
export interface VideoAuthor {
  id: string;
  name: string;
  avatar: string;
  bio?: string;
}

// 视频分类
export interface VideoCategory {
  id: string;
  name: string;
  icon?: string;
}

// 视频章节
export interface VideoChapter {
  id: string;
  title: string;
  startTime: number; // 开始时间（秒）
  endTime?: number; // 结束时间（秒）
  description?: string;
  thumbnail?: string;
}

// 字幕条目
export interface SubtitleItem {
  id: string;
  startTime: number; // 开始时间（秒）
  endTime: number; // 结束时间（秒）
  text: string;
  translation?: Record<string, string>; // 多语言翻译
}

// 字幕轨道
export interface SubtitleTrack {
  id: string;
  language: string;
  label: string;
  src: string;
  isDefault?: boolean;
  subtitles: SubtitleItem[];
}

// 视频笔记
export interface VideoNote {
  id: string;
  videoId: string;
  userId: string;
  timestamp: number; // 笔记对应的时间点
  content: string;
  type: 'text' | 'screenshot' | 'drawing' | 'formula';
  createdAt: string;
  updatedAt: string;
  isPublic: boolean;
  likes: number;
  replies?: VideoNoteReply[];
}

// 笔记回复
export interface VideoNoteReply {
  id: string;
  userId: string;
  userName: string;
  avatar: string;
  content: string;
  createdAt: string;
}

// 播放进度
export interface PlaybackProgress {
  videoId: string;
  userId: string;
  currentTime: number;
  duration: number;
  completed: boolean;
  lastWatchedAt: string;
  watchCount: number;
}

// 播放统计
export interface PlaybackStats {
  videoId: string;
  totalViews: number;
  uniqueViewers: number;
  averageWatchTime: number;
  completionRate: number;
  peakConcurrent: number;
  hourlyStats: HourlyStat[];
}

export interface HourlyStat {
  hour: string;
  views: number;
  avgWatchTime: number;
}

// 视频推荐
export interface VideoRecommendation {
  video: Video;
  reason: string;
  score: number;
  type: 'related' | 'trending' | 'personalized' | 'continue';
}

// 播放列表
export interface VideoPlaylist {
  id: string;
  title: string;
  description: string;
  videos: Video[];
  author: VideoAuthor;
  createdAt: string;
  updatedAt: string;
  isPublic: boolean;
}

// 播放器状态
export interface PlayerState {
  isPlaying: boolean;
  currentTime: number;
  duration: number;
  volume: number;
  isMuted: boolean;
  playbackRate: number;
  isFullscreen: boolean;
  isPIP: boolean; // 画中画模式
  quality: string;
  buffered: TimeRange[];
}

export interface TimeRange {
  start: number;
  end: number;
}

// 播放器配置
export interface PlayerConfig {
  autoPlay: boolean;
  defaultVolume: number;
  defaultPlaybackRate: number;
  enableSubtitle: boolean;
  defaultSubtitleLanguage?: string;
  enableChapter: boolean;
  enableNote: boolean;
  theme: 'light' | 'dark';
}

// 视频搜索参数
export interface VideoSearchParams {
  keyword?: string;
  category?: string;
  difficulty?: string;
  tags?: string[];
  sortBy?: 'relevance' | 'date' | 'views' | 'likes';
  page?: number;
  pageSize?: number;
}

// 视频搜索结果
export interface VideoSearchResult {
  videos: Video[];
  total: number;
  page: number;
  pageSize: number;
  hasMore: boolean;
}
