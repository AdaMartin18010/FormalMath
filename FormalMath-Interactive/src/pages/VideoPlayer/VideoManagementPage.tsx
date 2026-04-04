/**
 * 视频管理页面
 * 用于管理员管理视频内容
 */

import React, { useState } from 'react';
import { VideoManagement } from '../../components/VideoPlayer/VideoManagement';
import { PlaybackStatsView, PlaybackHeatmap, RetentionCurve } from '../../components/VideoPlayer/PlaybackStats';
import type { Video, VideoCategory, PlaybackStats, VideoSearchParams } from '../../types/video';

// 模拟视频数据
const mockVideos: Video[] = [
  {
    id: 'video-1',
    title: '微积分基础：极限的概念与应用',
    description: '本视频将深入讲解微积分中最核心的概念——极限。',
    thumbnail: 'https://picsum.photos/seed/calculus/400/225',
    duration: 3600,
    url: '/videos/calculus.mp4',
    author: { id: 'author-1', name: '张教授', avatar: 'https://picsum.photos/seed/professor/100/100' },
    category: { id: 'cat-1', name: '微积分' },
    tags: ['微积分', '极限'],
    createdAt: '2024-03-15T08:00:00Z',
    updatedAt: '2024-03-15T08:00:00Z',
    viewCount: 12580,
    likeCount: 892,
    difficulty: 'beginner',
    relatedConcepts: ['limit'],
  },
  {
    id: 'video-2',
    title: '导数的几何意义',
    description: '理解导数作为切线斜率的概念',
    thumbnail: 'https://picsum.photos/seed/derivative/400/225',
    duration: 2400,
    url: '/videos/derivative.mp4',
    author: { id: 'author-1', name: '张教授', avatar: 'https://picsum.photos/seed/professor/100/100' },
    category: { id: 'cat-1', name: '微积分' },
    tags: ['导数', '微积分'],
    createdAt: '2024-03-10T08:00:00Z',
    updatedAt: '2024-03-10T08:00:00Z',
    viewCount: 8920,
    likeCount: 654,
    difficulty: 'beginner',
    relatedConcepts: ['derivative'],
  },
  {
    id: 'video-3',
    title: '连续性原理详解',
    description: '深入理解函数的连续性',
    thumbnail: 'https://picsum.photos/seed/continuity/400/225',
    duration: 1800,
    url: '/videos/continuity.mp4',
    author: { id: 'author-2', name: '李老师', avatar: 'https://picsum.photos/seed/teacher/100/100' },
    category: { id: 'cat-1', name: '微积分' },
    tags: ['连续性', '微积分'],
    createdAt: '2024-03-12T08:00:00Z',
    updatedAt: '2024-03-12T08:00:00Z',
    viewCount: 5670,
    likeCount: 432,
    difficulty: 'intermediate',
    relatedConcepts: ['continuity'],
  },
  {
    id: 'video-4',
    title: '线性代数：矩阵基础',
    description: '学习矩阵的基本概念和运算',
    thumbnail: 'https://picsum.photos/seed/matrix/400/225',
    duration: 2700,
    url: '/videos/matrix.mp4',
    author: { id: 'author-3', name: '王博士', avatar: 'https://picsum.photos/seed/doctor/100/100' },
    category: { id: 'cat-2', name: '线性代数' },
    tags: ['矩阵', '线性代数'],
    createdAt: '2024-03-14T08:00:00Z',
    updatedAt: '2024-03-14T08:00:00Z',
    viewCount: 7890,
    likeCount: 567,
    difficulty: 'beginner',
    relatedConcepts: ['matrix'],
  },
  {
    id: 'video-5',
    title: '概率论入门',
    description: '概率论的基本概念和应用',
    thumbnail: 'https://picsum.photos/seed/probability/400/225',
    duration: 3200,
    url: '/videos/probability.mp4',
    author: { id: 'author-2', name: '李老师', avatar: 'https://picsum.photos/seed/teacher/100/100' },
    category: { id: 'cat-3', name: '概率统计' },
    tags: ['概率', '统计'],
    createdAt: '2024-03-11T08:00:00Z',
    updatedAt: '2024-03-11T08:00:00Z',
    viewCount: 6540,
    likeCount: 489,
    difficulty: 'beginner',
    relatedConcepts: ['probability'],
  },
  {
    id: 'video-6',
    title: '群论基础',
    description: '抽象代数中的群论入门',
    thumbnail: 'https://picsum.photos/seed/group/400/225',
    duration: 4200,
    url: '/videos/group.mp4',
    author: { id: 'author-3', name: '王博士', avatar: 'https://picsum.photos/seed/doctor/100/100' },
    category: { id: 'cat-4', name: '抽象代数' },
    tags: ['群论', '抽象代数'],
    createdAt: '2024-03-09T08:00:00Z',
    updatedAt: '2024-03-09T08:00:00Z',
    viewCount: 3210,
    likeCount: 298,
    difficulty: 'advanced',
    relatedConcepts: ['group'],
  },
];

// 模拟分类数据
const mockCategories: VideoCategory[] = [
  { id: 'cat-1', name: '微积分' },
  { id: 'cat-2', name: '线性代数' },
  { id: 'cat-3', name: '概率统计' },
  { id: 'cat-4', name: '抽象代数' },
  { id: 'cat-5', name: '数论' },
  { id: 'cat-6', name: '几何' },
];

// 模拟播放统计数据
const mockPlaybackStats: PlaybackStats = {
  videoId: 'video-1',
  totalViews: 12580,
  uniqueViewers: 8432,
  averageWatchTime: 1860,
  completionRate: 0.52,
  peakConcurrent: 342,
  hourlyStats: Array.from({ length: 24 }, (_, i) => ({
    hour: `2024-03-15 ${String(i).padStart(2, '0')}:00`,
    views: Math.floor(Math.random() * 500) + 50,
    avgWatchTime: Math.floor(Math.random() * 1800) + 300,
  })),
};

// 模拟热力图数据
const mockHeatmapData = Array.from({ length: 50 }, (_, i) => ({
  timestamp: i * 72,
  views: Math.floor(Math.random() * 1000) + 100,
}));

// 模拟留存数据
const mockRetentionData = Array.from({ length: 20 }, (_, i) => ({
  percentage: i * 5,
  retention: Math.max(0, 1 - i * 0.04 + Math.random() * 0.1),
}));

export const VideoManagementPage: React.FC = () => {
  const [videos, setVideos] = useState<Video[]>(mockVideos);
  const [selectedVideo, setSelectedVideo] = useState<Video | null>(null);
  const [activeTab, setActiveTab] = useState<'list' | 'stats'>('list');

  const handleUpload = () => {
    console.log('打开上传对话框');
  };

  const handleEdit = (video: Video) => {
    console.log('编辑视频:', video.id);
    setSelectedVideo(video);
  };

  const handleDelete = (video: Video) => {
    if (confirm(`确定要删除视频 "${video.title}" 吗？`)) {
      setVideos(prev => prev.filter(v => v.id !== video.id));
    }
  };

  const handleSearch = (params: VideoSearchParams) => {
    console.log('搜索参数:', params);
    // 实际应用中这里会调用API
  };

  return (
    <div className="min-h-screen bg-gray-950 p-4 md:p-6">
      {/* 页面标题 */}
      <div className="mb-6">
        <h1 className="text-2xl font-bold text-white">视频管理</h1>
        <p className="text-white/50 mt-1">管理和分析您的视频内容</p>
      </div>

      {/* 标签切换 */}
      <div className="flex items-center gap-2 mb-6">
        <button
          onClick={() => setActiveTab('list')}
          className={`
            px-4 py-2 rounded-lg text-sm font-medium transition-colors
            ${activeTab === 'list' 
              ? 'bg-blue-500 text-white' 
              : 'text-white/60 hover:text-white hover:bg-white/10'}
          `}
        >
          视频列表
        </button>
        <button
          onClick={() => setActiveTab('stats')}
          className={`
            px-4 py-2 rounded-lg text-sm font-medium transition-colors
            ${activeTab === 'stats' 
              ? 'bg-blue-500 text-white' 
              : 'text-white/60 hover:text-white hover:bg-white/10'}
          `}
        >
          数据分析
        </button>
      </div>

      {/* 内容区域 */}
      {activeTab === 'list' ? (
        <VideoManagement
          videos={videos}
          categories={mockCategories}
          onUpload={handleUpload}
          onEdit={handleEdit}
          onDelete={handleDelete}
          onSearch={handleSearch}
        />
      ) : (
        <div className="space-y-6">
          {/* 选择视频 */}
          <div className="bg-gray-900 rounded-lg p-4">
            <label className="text-white/70 text-sm block mb-2">选择要分析的视频</label>
            <select
              value={selectedVideo?.id || videos[0].id}
              onChange={(e) => {
                const video = videos.find(v => v.id === e.target.value);
                setSelectedVideo(video || null);
              }}
              className="w-full max-w-md bg-gray-800 text-white px-3 py-2 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
            >
              {videos.map((video) => (
                <option key={video.id} value={video.id}>{video.title}</option>
              ))}
            </select>
          </div>

          {/* 播放统计 */}
          <PlaybackStatsView stats={mockPlaybackStats} />

          {/* 热力图和留存曲线 */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
            <div className="bg-gray-900 rounded-lg p-4">
              <PlaybackHeatmap 
                data={mockHeatmapData} 
                duration={3600}
              />
            </div>
            <div className="bg-gray-900 rounded-lg p-4">
              <RetentionCurve data={mockRetentionData} />
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

export default VideoManagementPage;
