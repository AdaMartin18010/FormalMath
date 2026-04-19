---
title: 视频播放器组件
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 视频播放器组件

FormalMath-Interactive 的视频播放器组件系统，提供完整的视频播放、管理、统计功能。

## 功能特性

### 1. 视频播放器 (VideoPlayer)
- 自定义控制栏设计
- 全屏、画中画模式
- 播放速度调节 (0.25x - 2x)
- 键盘快捷键支持
- 缓冲进度显示

### 2. 章节标记 (ChapterMarker)
- 视频章节可视化
- 章节快速跳转
- 当前章节高亮
- 章节完成状态追踪

### 3. 字幕支持 (SubtitleDisplay)
- 多语言字幕切换
- 字幕样式自定义
- 字幕搜索跳转
- WebVTT 格式支持

### 4. 视频笔记 (VideoNotes)
- 时间戳笔记
- 多种笔记类型（文本、公式、截图）
- 笔记管理与编辑
- 本地存储持久化

### 5. 视频推荐 (VideoRecommendations)
- 相关视频推荐
- 热门视频展示
- 个性化推荐
- 续播视频提醒

### 6. 播放列表 (VideoPlaylist)
- 顺序播放/随机播放
- 循环模式设置
- 播放进度保存
- 列表拖拽排序

### 7. 视频管理 (VideoManagement)
- 视频上传/编辑/删除
- 批量操作支持
- 分类管理
- 搜索与筛选

### 8. 播放统计 (PlaybackStats)
- 观看次数统计
- 观众留存分析
- 热力图展示
- 互动数据分析

## 快速开始

### 基础使用

```tsx
import { VideoPlayer } from './components/VideoPlayer';
import type { Video } from './types/video';

const video: Video = {
  id: 'video-1',
  title: '视频标题',
  description: '视频描述',
  thumbnail: '/thumbnail.jpg',
  duration: 3600,
  url: '/video.mp4',
  author: {
    id: 'author-1',
    name: '作者名',
    avatar: '/avatar.jpg',
  },
  category: { id: 'cat-1', name: '分类' },
  tags: ['标签1', '标签2'],
  createdAt: '2024-01-01T00:00:00Z',
  updatedAt: '2024-01-01T00:00:00Z',
  viewCount: 1000,
  likeCount: 100,
  difficulty: 'beginner',
  relatedConcepts: [],
};

function App() {
  return (
    <VideoPlayer
      video={video}
      onTimeUpdate={(time) => console.log('当前时间:', time)}
      onEnded={() => console.log('播放结束')}
    />
  );
}
```

### 完整容器使用

```tsx
import { VideoPlayerContainer } from './components/VideoPlayer';

function VideoPage() {
  return (
    <VideoPlayerContainer
      video={video}
      chapters={chapters}
      subtitles={subtitles}
      recommendations={recommendations}
      playlist={playlist}
      onVideoEnd={() => console.log('视频结束')}
      onVideoChange={(newVideo) => console.log('切换视频:', newVideo.id)}
    />
  );
}
```

### 使用 Hooks

```tsx
import { useVideoPlayer, useVideoNotes, useSubtitles } from './hooks';

function CustomVideoPlayer() {
  const { 
    videoRef, 
    state, 
    togglePlay, 
    seekTo,
    setVolume,
    toggleFullscreen 
  } = useVideoPlayer({
    autoPlay: false,
    defaultVolume: 0.8,
  });

  const { notes, addNote, deleteNote } = useVideoNotes('video-1');
  
  const { currentSubtitle, updateCurrentSubtitle } = useSubtitles(subtitleItems);

  return (
    // 自定义播放器UI
  );
}
```

## 组件 API

### VideoPlayer Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| video | Video | 必填 | 视频数据 |
| config | Partial<PlayerConfig> | {} | 播放器配置 |
| chapters | VideoChapter[] | [] | 章节数据 |
| subtitles | SubtitleTrack[] | [] | 字幕轨道 |
| onTimeUpdate | (time: number) => void | - | 时间更新回调 |
| onEnded | () => void | - | 播放结束回调 |
| onPlay | () => void | - | 播放回调 |
| onPause | () => void | - | 暂停回调 |
| className | string | - | 自定义类名 |

### VideoPlayerContainer Props

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| video | Video | 必填 | 视频数据 |
| chapters | VideoChapter[] | [] | 章节数据 |
| subtitles | SubtitleTrack[] | [] | 字幕轨道 |
| recommendations | VideoRecommendation[] | [] | 推荐视频 |
| playlist | VideoPlaylist | - | 播放列表 |
| onVideoEnd | () => void | - | 视频结束回调 |
| onVideoChange | (video: Video) => void | - | 视频切换回调 |

### PlayerConfig

| 属性 | 类型 | 默认值 | 说明 |
|------|------|--------|------|
| autoPlay | boolean | false | 自动播放 |
| defaultVolume | number | 0.8 | 默认音量 |
| defaultPlaybackRate | number | 1 | 默认播放速度 |
| enableSubtitle | boolean | true | 启用字幕 |
| enableChapter | boolean | true | 启用章节 |
| enableNote | boolean | true | 启用笔记 |
| theme | 'light' \| 'dark' | 'dark' | 主题 |

## 键盘快捷键

| 快捷键 | 功能 |
|--------|------|
| Space / K | 播放/暂停 |
| ← | 后退5秒 |
| → | 前进5秒 |
| Shift + ← | 后退10秒 |
| Shift + → | 前进10秒 |
| ↑ | 增加音量 |
| ↓ | 降低音量 |
| F | 全屏切换 |
| M | 静音切换 |

## 类型定义

```typescript
// 视频基础类型
interface Video {
  id: string;
  title: string;
  description: string;
  thumbnail: string;
  duration: number;
  url: string;
  author: VideoAuthor;
  category: VideoCategory;
  tags: string[];
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  viewCount: number;
  likeCount: number;
  createdAt: string;
  updatedAt: string;
}

// 视频章节
interface VideoChapter {
  id: string;
  title: string;
  startTime: number;
  endTime?: number;
  description?: string;
  thumbnail?: string;
}

// 字幕条目
interface SubtitleItem {
  id: string;
  startTime: number;
  endTime: number;
  text: string;
  translation?: Record<string, string>;
}

// 视频笔记
interface VideoNote {
  id: string;
  videoId: string;
  timestamp: number;
  content: string;
  type: 'text' | 'formula' | 'screenshot';
  createdAt: string;
  updatedAt: string;
  isPublic: boolean;
  likes: number;
}
```

## 文件结构

```
components/VideoPlayer/
├── index.ts              # 组件导出
├── types.ts              # 类型定义
├── VideoPlayer.tsx       # 核心播放器
├── VideoPlayerContainer.tsx  # 播放器容器
├── VideoControls.tsx     # 控制栏
├── VideoProgressBar.tsx  # 进度条
├── ChapterMarker.tsx     # 章节标记
├── SubtitleDisplay.tsx   # 字幕显示
├── VideoNotes.tsx        # 视频笔记
├── VideoRecommendations.tsx  # 视频推荐
├── VideoPlaylist.tsx     # 播放列表
├── VideoManagement.tsx   # 视频管理
└── PlaybackStats.tsx     # 播放统计
```

## 示例页面

- `VideoPlayerPage` - 视频播放页面
- `VideoManagementPage` - 视频管理页面

## 依赖

- React 18+
- Lucide React (图标)
- Tailwind CSS (样式)
- clsx + tailwind-merge (类名处理)
