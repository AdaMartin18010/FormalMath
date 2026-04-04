/**
 * 视频播放器容器组件
 * 整合播放器、章节、字幕、笔记、推荐等功能
 */

import React, { useState, useCallback, useEffect } from 'react';
import { 
  ChevronRight, 
  ChevronLeft,
  BookOpen,
  MessageSquare,
  ThumbsUp,
  Share2,
  MoreHorizontal,
  Plus,
  Check
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoPlayerContainerProps } from './types';
import type { Video } from '../../types/video';
import { VideoPlayer } from './VideoPlayer';
import { ChapterMarker } from './ChapterMarker';
import { VideoNotes } from './VideoNotes';
import { VideoRecommendations, CompactRecommendations } from './VideoRecommendations';
import { VideoPlaylist, MiniPlaylist } from './VideoPlaylist';
import { SubtitleSelector, SubtitleSearch } from './SubtitleDisplay';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

type SidebarTab = 'chapters' | 'notes' | 'playlist' | 'recommendations';

export const VideoPlayerContainer: React.FC<VideoPlayerContainerProps> = ({
  video,
  relatedVideos = [],
  chapters = [],
  subtitles = [],
  recommendations = [],
  playlist,
  config = {},
  onVideoEnd,
  onVideoChange,
}) => {
  const [activeTab, setActiveTab] = useState<SidebarTab>('chapters');
  const [currentTime, setCurrentTime] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [isSubscribed, setIsSubscribed] = useState(false);
  const [isLiked, setIsLiked] = useState(false);
  const [selectedSubtitle, setSelectedSubtitle] = useState<string | null>(
    subtitles.find(s => s.isDefault)?.id || null
  );
  const [subtitlesVisible, setSubtitlesVisible] = useState(true);
  const [sidebarCollapsed, setSidebarCollapsed] = useState(false);

  // 处理时间更新
  const handleTimeUpdate = useCallback((time: number) => {
    setCurrentTime(time);
  }, []);

  // 处理播放状态变化
  const handlePlay = useCallback(() => {
    setIsPlaying(true);
  }, []);

  const handlePause = useCallback(() => {
    setIsPlaying(false);
  }, []);

  // 跳转到指定时间
  const handleSeekToTime = useCallback((time: number) => {
    setCurrentTime(time);
    // 实际跳转需要在 VideoPlayer 中处理
    const videoElement = document.querySelector('video');
    if (videoElement) {
      videoElement.currentTime = time;
    }
  }, []);

  // 处理视频结束
  const handleEnded = useCallback(() => {
    onVideoEnd?.();
  }, [onVideoEnd]);

  // 处理视频切换
  const handleVideoChange = useCallback((newVideo: Video) => {
    onVideoChange?.(newVideo);
  }, [onVideoChange]);

  // 处理字幕选择
  const handleSubtitleSelect = useCallback((trackId: string | null) => {
    setSelectedSubtitle(trackId);
  }, []);

  // 格式化观看数
  const formatViews = (views: number): string => {
    if (views >= 10000) {
      return `${(views / 10000).toFixed(1)}万`;
    }
    if (views >= 1000) {
      return `${(views / 1000).toFixed(1)}k`;
    }
    return views.toString();
  };

  // 格式化日期
  const formatDate = (dateString: string): string => {
    const date = new Date(dateString);
    return date.toLocaleDateString('zh-CN', {
      year: 'numeric',
      month: 'long',
      day: 'numeric',
    });
  };

  const tabs = [
    { id: 'chapters' as const, label: '章节', icon: BookOpen },
    { id: 'notes' as const, label: '笔记', icon: MessageSquare },
    ...(playlist ? [{ id: 'playlist' as const, label: '列表', icon: Plus }] : []),
    { id: 'recommendations' as const, label: '推荐', icon: ThumbsUp },
  ];

  return (
    <div className="flex gap-4 h-full">
      {/* 主内容区 */}
      <div className={cn(
        'flex-1 flex flex-col gap-4 transition-all',
        sidebarCollapsed ? 'mr-0' : 'mr-0'
      )}>
        {/* 视频播放器 */}
        <div className="relative">
          <VideoPlayer
            video={video}
            config={config}
            chapters={chapters}
            subtitles={subtitles}
            onTimeUpdate={handleTimeUpdate}
            onEnded={handleEnded}
            onPlay={handlePlay}
            onPause={handlePause}
            className="aspect-video w-full"
          />

          {/* 字幕控制 */}
          {subtitles.length > 0 && (
            <div className="absolute top-4 right-4 flex items-center gap-2">
              <SubtitleSearch
                subtitles={subtitles.find(s => s.id === selectedSubtitle)?.subtitles || []}
                onSubtitleClick={handleSeekToTime}
              />
              <SubtitleSelector
                tracks={subtitles.map(s => ({ id: s.id, label: s.label, language: s.language }))}
                selectedId={selectedSubtitle}
                isVisible={subtitlesVisible}
                onSelect={handleSubtitleSelect}
                onToggleVisibility={() => setSubtitlesVisible(!subtitlesVisible)}
              />
            </div>
          )}
        </div>

        {/* 视频信息 */}
        <div className="bg-gray-900 rounded-lg p-4">
          <h1 className="text-xl font-bold text-white mb-2">{video.title}</h1>
          
          <div className="flex items-start justify-between gap-4">
            {/* 左侧：作者信息 */}
            <div className="flex items-center gap-3">
              <img
                src={video.author.avatar}
                alt={video.author.name}
                className="w-10 h-10 rounded-full bg-gray-700"
              />
              <div>
                <div className="text-white font-medium">{video.author.name}</div>
                <div className="text-white/50 text-sm">
                  {formatViews(video.viewCount)}次观看 · {formatDate(video.createdAt)}
                </div>
              </div>
              <button
                onClick={() => setIsSubscribed(!isSubscribed)}
                className={cn(
                  'ml-3 px-4 py-1.5 rounded-full text-sm font-medium transition-colors',
                  isSubscribed
                    ? 'bg-white/10 text-white hover:bg-white/20'
                    : 'bg-white text-black hover:bg-white/90'
                )}
              >
                {isSubscribed ? '已订阅' : '订阅'}
              </button>
            </div>

            {/* 右侧：操作按钮 */}
            <div className="flex items-center gap-2">
              <button
                onClick={() => setIsLiked(!isLiked)}
                className={cn(
                  'flex items-center gap-1.5 px-4 py-1.5 rounded-full transition-colors',
                  isLiked
                    ? 'bg-blue-500 text-white'
                    : 'bg-white/10 text-white hover:bg-white/20'
                )}
              >
                <ThumbsUp className="w-4 h-4" />
                <span className="text-sm">{formatViews(video.likeCount)}</span>
              </button>
              
              <button className="flex items-center gap-1.5 px-4 py-1.5 rounded-full bg-white/10 text-white hover:bg-white/20 transition-colors">
                <Share2 className="w-4 h-4" />
                <span className="text-sm">分享</span>
              </button>
              
              <button className="p-2 rounded-full bg-white/10 text-white hover:bg-white/20 transition-colors">
                <MoreHorizontal className="w-4 h-4" />
              </button>
            </div>
          </div>

          {/* 视频描述 */}
          {video.description && (
            <div className="mt-4 p-3 bg-white/5 rounded-lg">
              <p className="text-white/70 text-sm whitespace-pre-line line-clamp-3">
                {video.description}
              </p>
            </div>
          )}

          {/* 标签 */}
          {video.tags.length > 0 && (
            <div className="flex flex-wrap gap-2 mt-3">
              {video.tags.map((tag) => (
                <span
                  key={tag}
                  className="px-2 py-1 bg-white/10 text-white/70 text-xs rounded-full hover:bg-white/20 cursor-pointer transition-colors"
                >
                  #{tag}
                </span>
              ))}
            </div>
          )}
        </div>

        {/* 评论区占位 */}
        <div className="bg-gray-900 rounded-lg p-4">
          <h3 className="text-white font-medium mb-4">评论</h3>
          <div className="text-white/40 text-center py-8">
            评论功能即将上线
          </div>
        </div>
      </div>

      {/* 侧边栏 */}
      <div className={cn(
        'flex-shrink-0 transition-all duration-300',
        sidebarCollapsed ? 'w-0 overflow-hidden' : 'w-80'
      )}>
        {/* 标签切换 */}
        <div className="flex items-center gap-1 mb-4 overflow-x-auto pb-2">
          {tabs.map((tab) => (
            <button
              key={tab.id}
              onClick={() => setActiveTab(tab.id)}
              className={cn(
                'flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm whitespace-nowrap transition-colors',
                activeTab === tab.id
                  ? 'bg-blue-500 text-white'
                  : 'text-white/60 hover:text-white hover:bg-white/10'
              )}
            >
              <tab.icon className="w-4 h-4" />
              {tab.label}
            </button>
          ))}
        </div>

        {/* 侧边栏内容 */}
        <div className="space-y-4">
          {activeTab === 'chapters' && chapters.length > 0 && (
            <ChapterMarker
              chapters={chapters}
              duration={video.duration}
              currentTime={currentTime}
              onChapterClick={(chapter) => handleSeekToTime(chapter.startTime)}
            />
          )}

          {activeTab === 'notes' && (
            <VideoNotes
              videoId={video.id}
              currentTime={currentTime}
              isPlaying={isPlaying}
              onTimestampClick={handleSeekToTime}
            />
          )}

          {activeTab === 'playlist' && playlist && (
            <VideoPlaylist
              playlist={playlist}
              currentVideoId={video.id}
              onVideoClick={(v) => handleVideoChange(v)}
            />
          )}

          {activeTab === 'recommendations' && recommendations.length > 0 && (
            <VideoRecommendations
              recommendations={recommendations}
              onVideoClick={handleVideoChange}
            />
          )}

          {/* 如果没有内容，显示提示 */}
          {activeTab === 'chapters' && chapters.length === 0 && (
            <div className="bg-gray-900 rounded-lg p-8 text-center text-white/40">
              <BookOpen className="w-12 h-12 mx-auto mb-3 opacity-30" />
              <p>暂无章节信息</p>
            </div>
          )}

          {activeTab === 'recommendations' && recommendations.length === 0 && (
            <div className="bg-gray-900 rounded-lg p-8 text-center text-white/40">
              <ThumbsUp className="w-12 h-12 mx-auto mb-3 opacity-30" />
              <p>暂无推荐视频</p>
            </div>
          )}
        </div>
      </div>

      {/* 侧边栏折叠按钮 */}
      <button
        onClick={() => setSidebarCollapsed(!sidebarCollapsed)}
        className={cn(
          'fixed right-0 top-1/2 -translate-y-1/2 z-10 p-2 bg-gray-800 text-white rounded-l-lg shadow-lg transition-all',
          sidebarCollapsed ? 'translate-x-0' : 'translate-x-full'
        )}
      >
        <ChevronLeft className="w-5 h-5" />
      </button>
    </div>
  );
};

// 简化的视频播放器页面
export interface VideoPlayerPageProps {
  video: Video;
  chapters?: VideoPlayerContainerProps['chapters'];
  subtitles?: VideoPlayerContainerProps['subtitles'];
  recommendations?: VideoPlayerContainerProps['recommendations'];
  playlist?: VideoPlayerContainerProps['playlist'];
}

export const VideoPlayerPage: React.FC<VideoPlayerPageProps> = ({
  video,
  chapters = [],
  subtitles = [],
  recommendations = [],
  playlist,
}) => {
  return (
    <div className="min-h-screen bg-black p-4">
      <VideoPlayerContainer
        video={video}
        chapters={chapters}
        subtitles={subtitles}
        recommendations={recommendations}
        playlist={playlist}
      />
    </div>
  );
};
