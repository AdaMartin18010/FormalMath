/**
 * 视频播放器页面
 */

import React, { useState, useEffect } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { VideoPlayerContainer } from '../../components/VideoPlayer';
import type { Video, VideoChapter, SubtitleTrack, VideoRecommendation, VideoPlaylist } from '../../types/video';

// 模拟视频数据
const mockVideo: Video = {
  id: 'video-1',
  title: '微积分基础：极限的概念与应用',
  description: `本视频将深入讲解微积分中最核心的概念——极限。

我们将从数列极限开始，逐步过渡到函数极限，并通过大量例题帮助您理解极限的计算方法。

主要内容包括：
- 数列极限的定义与性质
- 函数极限的ε-δ定义
- 极限的四则运算
- 两个重要极限
- 洛必达法则简介

适合初学者和需要复习基础的同学观看。`,
  thumbnail: 'https://picsum.photos/seed/calculus/1280/720',
  duration: 3600,
  url: 'https://commondatastorage.googleapis.com/gtv-videos-bucket/sample/BigBuckBunny.mp4',
  author: {
    id: 'author-1',
    name: '张教授',
    avatar: 'https://picsum.photos/seed/professor/100/100',
    bio: '数学系教授，从事数学教育20余年',
  },
  category: {
    id: 'cat-1',
    name: '微积分',
  },
  tags: ['微积分', '极限', '数学分析', '入门'],
  createdAt: '2024-03-15T08:00:00Z',
  updatedAt: '2024-03-15T08:00:00Z',
  viewCount: 12580,
  likeCount: 892,
  difficulty: 'beginner',
  relatedConcepts: ['limit', 'derivative', 'continuity'],
};

// 模拟章节数据
const mockChapters: VideoChapter[] = [
  {
    id: 'ch-1',
    title: '引言：为什么学习极限？',
    startTime: 0,
    description: '介绍极限在微积分中的重要性',
  },
  {
    id: 'ch-2',
    title: '数列极限的直观理解',
    startTime: 300,
    description: '通过图形和例子理解数列极限',
  },
  {
    id: 'ch-3',
    title: '数列极限的严格定义',
    startTime: 720,
    description: 'ε-N定义详解',
  },
  {
    id: 'ch-4',
    title: '函数极限的概念',
    startTime: 1260,
    description: '从数列极限到函数极限的过渡',
  },
  {
    id: 'ch-5',
    title: 'ε-δ定义与证明',
    startTime: 1860,
    description: '函数极限的严格定义',
  },
  {
    id: 'ch-6',
    title: '极限的四则运算',
    startTime: 2460,
    description: '如何计算复杂函数的极限',
  },
  {
    id: 'ch-7',
    title: '两个重要极限',
    startTime: 3000,
    description: 'sin(x)/x 和 (1+1/n)^n',
  },
  {
    id: 'ch-8',
    title: '洛必达法则',
    startTime: 3300,
    description: '0/0型和∞/∞型极限的计算方法',
  },
];

// 模拟字幕数据
const mockSubtitles: SubtitleTrack[] = [
  {
    id: 'sub-zh',
    language: 'zh-CN',
    label: '中文',
    src: '/subtitles/video-1-zh.vtt',
    isDefault: true,
    subtitles: [
      { id: 's1', startTime: 0, endTime: 5, text: '欢迎来到微积分基础课程' },
      { id: 's2', startTime: 5, endTime: 10, text: '今天我们将学习极限的概念' },
      { id: 's3', startTime: 10, endTime: 15, text: '极限是微积分的基础' },
      { id: 's4', startTime: 15, endTime: 20, text: '让我们一起开始这段学习之旅' },
    ],
  },
  {
    id: 'sub-en',
    language: 'en',
    label: 'English',
    src: '/subtitles/video-1-en.vtt',
    subtitles: [
      { id: 'e1', startTime: 0, endTime: 5, text: 'Welcome to Calculus Fundamentals' },
      { id: 'e2', startTime: 5, endTime: 10, text: 'Today we will learn about limits' },
      { id: 'e3', startTime: 10, endTime: 15, text: 'Limits are the foundation of calculus' },
      { id: 'e4', startTime: 15, endTime: 20, text: 'Let\'s begin this learning journey' },
    ],
  },
];

// 模拟推荐视频
const mockRecommendations: VideoRecommendation[] = [
  {
    video: {
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
    reason: '相关内容',
    score: 0.95,
    type: 'related',
  },
  {
    video: {
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
    reason: '热门视频',
    score: 0.88,
    type: 'trending',
  },
  {
    video: {
      id: 'video-4',
      title: '无穷小量与无穷大量',
      description: '探讨无穷概念的奥秘',
      thumbnail: 'https://picsum.photos/seed/infinity/400/225',
      duration: 2100,
      url: '/videos/infinity.mp4',
      author: { id: 'author-1', name: '张教授', avatar: 'https://picsum.photos/seed/professor/100/100' },
      category: { id: 'cat-1', name: '微积分' },
      tags: ['无穷', '微积分'],
      createdAt: '2024-03-08T08:00:00Z',
      updatedAt: '2024-03-08T08:00:00Z',
      viewCount: 4320,
      likeCount: 321,
      difficulty: 'intermediate',
      relatedConcepts: ['infinity'],
    },
    reason: '为你推荐',
    score: 0.82,
    type: 'personalized',
  },
];

// 模拟播放列表
const mockPlaylist: VideoPlaylist = {
  id: 'playlist-1',
  title: '微积分入门系列',
  description: '从零开始学习微积分',
  videos: [
    mockVideo,
    mockRecommendations[0].video,
    mockRecommendations[1].video,
    mockRecommendations[2].video,
  ],
  author: { id: 'author-1', name: '张教授', avatar: 'https://picsum.photos/seed/professor/100/100' },
  createdAt: '2024-03-01T08:00:00Z',
  updatedAt: '2024-03-15T08:00:00Z',
  isPublic: true,
};

export const VideoPlayerPage: React.FC = () => {
  const { videoId } = useParams<{ videoId: string }>();
  const navigate = useNavigate();
  const [video, setVideo] = useState<Video>(mockVideo);
  const [loading, setLoading] = useState(true);

  // 模拟加载视频数据
  useEffect(() => {
    setLoading(true);
    // 模拟API调用
    setTimeout(() => {
      setVideo(mockVideo);
      setLoading(false);
    }, 500);
  }, [videoId]);

  const handleVideoEnd = () => {
    console.log('视频播放结束');
    // 可以自动播放下一个视频
  };

  const handleVideoChange = (newVideo: Video) => {
    navigate(`/video/${newVideo.id}`);
  };

  if (loading) {
    return (
      <div className="min-h-screen bg-black flex items-center justify-center">
        <div className="text-center">
          <div className="w-12 h-12 border-4 border-blue-500 border-t-transparent rounded-full animate-spin mx-auto mb-4" />
          <p className="text-white/60">加载中...</p>
        </div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-black p-4 md:p-6">
      <VideoPlayerContainer
        video={video}
        chapters={mockChapters}
        subtitles={mockSubtitles}
        recommendations={mockRecommendations}
        playlist={mockPlaylist}
        onVideoEnd={handleVideoEnd}
        onVideoChange={handleVideoChange}
      />
    </div>
  );
};

export default VideoPlayerPage;
