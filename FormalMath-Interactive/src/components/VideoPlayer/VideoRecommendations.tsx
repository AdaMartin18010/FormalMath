/**
 * 视频推荐组件
 */

import React, { useState, useMemo } from 'react';
import { 
  Play, 
  Clock, 
  Eye, 
  ThumbsUp, 
  TrendingUp, 
  Sparkles,
  History,
  ChevronRight
} from 'lucide-react';
import { clsx, type ClassValue } from 'clsx';
import { twMerge } from 'tailwind-merge';
import type { VideoRecommendationsProps } from './types';
import type { Video, VideoRecommendation } from '../../types/video';

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

type TabType = 'all' | 'related' | 'trending' | 'personalized' | 'continue';

export const VideoRecommendations: React.FC<VideoRecommendationsProps> = ({
  recommendations,
  onVideoClick,
  className,
}) => {
  const [activeTab, setActiveTab] = useState<TabType>('all');

  // 按类型过滤推荐
  const filteredRecommendations = useMemo(() => {
    if (activeTab === 'all') return recommendations;
    return recommendations.filter(rec => rec.type === activeTab);
  }, [recommendations, activeTab]);

  // 按推荐分数排序
  const sortedRecommendations = useMemo(() => {
    return [...filteredRecommendations].sort((a, b) => b.score - a.score);
  }, [filteredRecommendations]);

  const tabs: { id: TabType; label: string; icon: React.ReactNode }[] = [
    { id: 'all', label: '全部', icon: <Sparkles className="w-4 h-4" /> },
    { id: 'related', label: '相关', icon: <ChevronRight className="w-4 h-4" /> },
    { id: 'trending', label: '热门', icon: <TrendingUp className="w-4 h-4" /> },
    { id: 'personalized', label: '推荐', icon: <Sparkles className="w-4 h-4" /> },
    { id: 'continue', label: '续播', icon: <History className="w-4 h-4" /> },
  ];

  return (
    <div className={cn('bg-gray-900 rounded-lg overflow-hidden', className)}>
      {/* 标签页 */}
      <div className="flex items-center gap-1 px-4 py-3 border-b border-white/10 overflow-x-auto">
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
            {tab.icon}
            {tab.label}
          </button>
        ))}
      </div>

      {/* 推荐列表 */}
      <div className="p-4 space-y-3">
        {sortedRecommendations.length === 0 ? (
          <div className="text-center py-8 text-white/40">
            <Sparkles className="w-12 h-12 mx-auto mb-3 opacity-30" />
            <p>暂无推荐视频</p>
          </div>
        ) : (
          sortedRecommendations.map((recommendation, index) => (
            <VideoRecommendationCard
              key={recommendation.video.id}
              recommendation={recommendation}
              index={index + 1}
              onClick={() => onVideoClick(recommendation.video)}
            />
          ))
        )}
      </div>
    </div>
  );
};

// 推荐视频卡片
interface VideoRecommendationCardProps {
  recommendation: VideoRecommendation;
  index: number;
  onClick: () => void;
}

const VideoRecommendationCard: React.FC<VideoRecommendationCardProps> = ({
  recommendation,
  index,
  onClick,
}) => {
  const { video, reason, type, score } = recommendation;

  const formatDuration = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    const hours = Math.floor(mins / 60);
    
    if (hours > 0) {
      return `${hours}:${String(mins % 60).padStart(2, '0')}:${String(secs).padStart(2, '0')}`;
    }
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  const formatViews = (views: number): string => {
    if (views >= 10000) {
      return `${(views / 10000).toFixed(1)}万`;
    }
    if (views >= 1000) {
      return `${(views / 1000).toFixed(1)}k`;
    }
    return views.toString();
  };

  const getTypeBadge = () => {
    switch (type) {
      case 'trending':
        return { icon: <TrendingUp className="w-3 h-3" />, label: '热门', color: 'text-red-400 bg-red-500/20' };
      case 'personalized':
        return { icon: <Sparkles className="w-3 h-3" />, label: '推荐', color: 'text-purple-400 bg-purple-500/20' };
      case 'continue':
        return { icon: <History className="w-3 h-3" />, label: '续看', color: 'text-blue-400 bg-blue-500/20' };
      case 'related':
        return { icon: <ChevronRight className="w-3 h-3" />, label: '相关', color: 'text-green-400 bg-green-500/20' };
      default:
        return null;
    }
  };

  const badge = getTypeBadge();

  return (
    <div
      onClick={onClick}
      className="flex gap-3 p-2 -mx-2 rounded-lg hover:bg-white/5 transition-colors cursor-pointer group"
    >
      {/* 缩略图 */}
      <div className="relative flex-shrink-0 w-36 aspect-video bg-gray-800 rounded-lg overflow-hidden">
        <img
          src={video.thumbnail}
          alt={video.title}
          className="w-full h-full object-cover group-hover:scale-105 transition-transform duration-300"
        />
        
        {/* 时长 */}
        <div className="absolute bottom-1 right-1 px-1.5 py-0.5 bg-black/80 text-white text-xs rounded">
          {formatDuration(video.duration)}
        </div>

        {/* 播放按钮遮罩 */}
        <div className="absolute inset-0 bg-black/50 opacity-0 group-hover:opacity-100 transition-opacity flex items-center justify-center">
          <div className="w-10 h-10 rounded-full bg-blue-500 flex items-center justify-center">
            <Play className="w-5 h-5 text-white ml-0.5" fill="white" />
          </div>
        </div>

        {/* 排名 */}
        {index <= 3 && (
          <div className={cn(
            'absolute top-1 left-1 w-5 h-5 rounded flex items-center justify-center text-xs font-bold',
            index === 1 ? 'bg-yellow-500 text-black' :
            index === 2 ? 'bg-gray-300 text-black' :
            index === 3 ? 'bg-amber-600 text-white' :
            'bg-black/60 text-white'
          )}>
            {index}
          </div>
        )}
      </div>

      {/* 信息 */}
      <div className="flex-1 min-w-0 py-0.5">
        {/* 标题 */}
        <h4 className="text-white font-medium text-sm line-clamp-2 leading-snug group-hover:text-blue-400 transition-colors">
          {video.title}
        </h4>

        {/* 作者 */}
        <p className="text-white/50 text-xs mt-1 truncate">
          {video.author.name}
        </p>

        {/* 统计 */}
        <div className="flex items-center gap-3 mt-1.5 text-xs text-white/40">
          <span className="flex items-center gap-1">
            <Eye className="w-3 h-3" />
            {formatViews(video.viewCount)}
          </span>
          <span className="flex items-center gap-1">
            <ThumbsUp className="w-3 h-3" />
            {formatViews(video.likeCount)}
          </span>
        </div>

        {/* 推荐理由 */}
        <div className="flex items-center gap-2 mt-2">
          {badge && (
            <span className={cn('px-1.5 py-0.5 rounded text-xs flex items-center gap-1', badge.color)}>
              {badge.icon}
              {badge.label}
            </span>
          )}
          {reason && (
            <span className="text-xs text-white/30 truncate">{reason}</span>
          )}
        </div>
      </div>
    </div>
  );
};

// 紧凑版推荐列表（用于侧边栏）
export interface CompactRecommendationsProps {
  recommendations: VideoRecommendation[];
  onVideoClick: (video: Video) => void;
  className?: string;
}

export const CompactRecommendations: React.FC<CompactRecommendationsProps> = ({
  recommendations,
  onVideoClick,
  className,
}) => {
  return (
    <div className={cn('space-y-2', className)}>
      {recommendations.slice(0, 6).map((recommendation) => (
        <CompactVideoCard
          key={recommendation.video.id}
          video={recommendation.video}
          onClick={() => onVideoClick(recommendation.video)}
        />
      ))}
    </div>
  );
};

// 紧凑视频卡片
const CompactVideoCard: React.FC<{ video: Video; onClick: () => void }> = ({
  video,
  onClick,
}) => {
  const formatDuration = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = Math.floor(seconds % 60);
    return `${mins}:${String(secs).padStart(2, '0')}`;
  };

  return (
    <div
      onClick={onClick}
      className="flex gap-2 p-1.5 -mx-1.5 rounded-lg hover:bg-white/5 transition-colors cursor-pointer group"
    >
      <div className="relative flex-shrink-0 w-24 aspect-video bg-gray-800 rounded overflow-hidden">
        <img
          src={video.thumbnail}
          alt={video.title}
          className="w-full h-full object-cover"
        />
        <div className="absolute bottom-0.5 right-0.5 px-1 py-0.5 bg-black/80 text-white text-[10px] rounded">
          {formatDuration(video.duration)}
        </div>
      </div>
      
      <div className="flex-1 min-w-0 py-0.5">
        <h4 className="text-white text-xs font-medium line-clamp-2 leading-snug">
          {video.title}
        </h4>
        <p className="text-white/40 text-[10px] mt-1 truncate">
          {video.author.name}
        </p>
      </div>
    </div>
  );
};
