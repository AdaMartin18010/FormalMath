import React, { useState } from 'react';
import {
  FileText,
  Video,
  Code,
  BookOpen,
  Link as LinkIcon,
  MoreHorizontal,
  Heart,
  Download,
  MessageSquare,
  Share2,
  Search,
  Filter,
  Plus,
  ExternalLink,
  FileCode,
  Image as ImageIcon,
  Calendar,
  User,
  Tag,
  Star
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { SharedResource, ResourceType } from '../../types/community';

interface ResourceSharingProps {
  className?: string;
}

const resourceTypes: { value: ResourceType; label: string; icon: React.ElementType; color: string }[] = [
  { value: 'note', label: '笔记', icon: FileText, color: 'bg-blue-100 text-blue-700' },
  { value: 'article', label: '文章', icon: BookOpen, color: 'bg-green-100 text-green-700' },
  { value: 'video', label: '视频', icon: Video, color: 'bg-red-100 text-red-700' },
  { value: 'code', label: '代码', icon: Code, color: 'bg-purple-100 text-purple-700' },
  { value: 'problem', label: '题目', icon: FileCode, color: 'bg-orange-100 text-orange-700' },
  { value: 'book', label: '书籍', icon: BookOpen, color: 'bg-yellow-100 text-yellow-700' },
  { value: 'link', label: '链接', icon: LinkIcon, color: 'bg-gray-100 text-gray-700' },
];

// 格式化时间
const formatDistanceToNow = (timestamp: number): string => {
  const seconds = Math.floor((Date.now() - timestamp) / 1000);
  if (seconds < 60) return '刚刚';
  const minutes = Math.floor(seconds / 60);
  if (minutes < 60) return `${minutes}分钟前`;
  const hours = Math.floor(minutes / 60);
  if (hours < 24) return `${hours}小时前`;
  const days = Math.floor(hours / 24);
  return `${days}天前`;
};

// 格式化文件大小
const formatFileSize = (bytes: number): string => {
  if (bytes === 0) return '0 Bytes';
  const k = 1024;
  const sizes = ['Bytes', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];
};

// 模拟资源数据
const mockResources: SharedResource[] = [
  {
    id: 'r1',
    title: '抽象代数完整笔记 - 群论部分',
    description: '包含群论基本概念、子群、正规子群、商群等核心内容的详细笔记，配有大量例题。',
    type: 'note',
    author: { id: 'u1', name: '代数达人', level: 10, points: 5000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 200 },
    tags: ['抽象代数', '群论', '笔记'],
    createdAt: Date.now() - 86400000 * 5,
    likes: 234,
    downloads: 567,
    comments: [],
  },
  {
    id: 'r2',
    title: '数学分析视频教程系列',
    description: '从实数理论到多元微积分的完整视频教程，共50讲，适合自学。',
    type: 'video',
    url: 'https://example.com/video-series',
    author: { id: 'u2', name: '分析专家', level: 12, points: 8000, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 300 },
    tags: ['数学分析', '视频教程', '自学'],
    createdAt: Date.now() - 86400000 * 3,
    likes: 456,
    downloads: 0,
    comments: [],
  },
  {
    id: 'r3',
    title: '拓扑学证明题代码实现',
    description: '使用Python实现的拓扑学基本概念可视化代码，包括连续映射、紧致性等。',
    type: 'code',
    file: { name: 'topology_viz.py', size: 15360, mimeType: 'text/python', url: '#' },
    author: { id: 'u3', name: '代码数学家', level: 8, points: 3200, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 150 },
    tags: ['拓扑学', 'Python', '可视化'],
    createdAt: Date.now() - 86400000 * 2,
    likes: 189,
    downloads: 342,
    comments: [],
  },
  {
    id: 'r4',
    title: '《数学之美》读书笔记',
    description: '对吴军博士《数学之美》一书的详细读书笔记，包含重点摘录和个人思考。',
    type: 'article',
    author: { id: 'u4', name: '读书爱好者', level: 6, points: 1800, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 100 },
    tags: ['读书', '数学文化', '读书笔记'],
    createdAt: Date.now() - 86400000,
    likes: 123,
    downloads: 0,
    comments: [],
  },
  {
    id: 'r5',
    title: '历年数学竞赛真题汇总',
    description: '收集整理了2000-2023年各类数学竞赛真题及详细解答。',
    type: 'problem',
    author: { id: 'u5', name: '竞赛达人', level: 9, points: 4200, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 180 },
    tags: ['竞赛', '真题', '习题集'],
    createdAt: Date.now() - 3600000 * 12,
    likes: 567,
    downloads: 1234,
    comments: [],
  },
];

export const ResourceSharing: React.FC<ResourceSharingProps> = ({ className }) => {
  const [resources, setResources] = useState<SharedResource[]>(mockResources);
  const [selectedResource, setSelectedResource] = useState<SharedResource | null>(null);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedType, setSelectedType] = useState<ResourceType | null>(null);
  const [sortBy, setSortBy] = useState<'latest' | 'popular' | 'downloads'>('latest');

  const filteredResources = resources
    .filter(r => {
      if (selectedType && r.type !== selectedType) return false;
      if (searchQuery && !r.title.toLowerCase().includes(searchQuery.toLowerCase())) return false;
      return true;
    })
    .sort((a, b) => {
      if (sortBy === 'latest') return b.createdAt - a.createdAt;
      if (sortBy === 'popular') return b.likes - a.likes;
      if (sortBy === 'downloads') return b.downloads - a.downloads;
      return 0;
    });

  const handleLike = (e: React.MouseEvent, resourceId: string) => {
    e.stopPropagation();
    setResources(prev => prev.map(r => 
      r.id === resourceId ? { ...r, likes: r.likes + 1 } : r
    ));
  };

  const handleDownload = (e: React.MouseEvent, resourceId: string) => {
    e.stopPropagation();
    setResources(prev => prev.map(r => 
      r.id === resourceId ? { ...r, downloads: r.downloads + 1 } : r
    ));
  };

  // 资源详情视图
  if (selectedResource) {
    const typeConfig = resourceTypes.find(t => t.value === selectedResource.type);
    const Icon = typeConfig?.icon || FileText;

    return (
      <div className={cn("space-y-6", className)}>
        {/* 返回按钮 */}
        <button
          onClick={() => setSelectedResource(null)}
          className="flex items-center gap-2 text-gray-600 hover:text-gray-900 dark:text-gray-400 dark:hover:text-white transition-colors"
        >
          <ExternalLink className="w-4 h-4 rotate-[-135deg]" />
          返回资源列表
        </button>

        {/* 资源详情卡片 */}
        <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden">
          {/* 头部 */}
          <div className="p-6 border-b border-gray-200 dark:border-slate-700">
            <div className="flex items-start gap-4">
              <div className={cn("w-16 h-16 rounded-xl flex items-center justify-center", typeConfig?.color)}>
                <Icon className="w-8 h-8" />
              </div>
              
              <div className="flex-1">
                <div className="flex items-center gap-2 mb-2">
                  <span className={cn("px-2 py-1 text-xs font-medium rounded-full", typeConfig?.color)}>
                    {typeConfig?.label}
                  </span>
                  {selectedResource.file && (
                    <span className="text-sm text-gray-500">
                      {formatFileSize(selectedResource.file.size)}
                    </span>
                  )}
                </div>
                
                <h1 className="text-2xl font-bold text-gray-900 dark:text-white mb-2">
                  {selectedResource.title}
                </h1>
                
                <p className="text-gray-600 dark:text-gray-400">
                  {selectedResource.description}
                </p>
              </div>
            </div>
          </div>

          {/* 作者信息 */}
          <div className="px-6 py-4 bg-gray-50 dark:bg-slate-700/50 border-b border-gray-200 dark:border-slate-700">
            <div className="flex items-center justify-between">
              <div className="flex items-center gap-3">
                <div className="w-10 h-10 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white font-medium">
                  {selectedResource.author.name.charAt(0)}
                </div>
                <div>
                  <div className="font-medium text-gray-900 dark:text-white">
                    {selectedResource.author.name}
                  </div>
                  <div className="text-sm text-gray-500">
                    等级 {selectedResource.author.level} · {formatDistanceToNow(selectedResource.createdAt)}
                  </div>
                </div>
              </div>

              {/* 操作按钮 */}
              <div className="flex items-center gap-3">
                <button 
                  onClick={(e) => handleLike(e, selectedResource.id)}
                  className="flex items-center gap-2 px-4 py-2 bg-pink-100 dark:bg-pink-900/30 text-pink-700 dark:text-pink-400 rounded-lg hover:bg-pink-200 transition-colors"
                >
                  <Heart className="w-5 h-5" />
                  {selectedResource.likes}
                </button>
                
                {selectedResource.file && (
                  <button 
                    onClick={(e) => handleDownload(e, selectedResource.id)}
                    className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
                  >
                    <Download className="w-5 h-5" />
                    下载 ({selectedResource.downloads})
                  </button>
                )}
                
                {selectedResource.url && (
                  <a 
                    href={selectedResource.url}
                    target="_blank"
                    rel="noopener noreferrer"
                    className="flex items-center gap-2 px-4 py-2 bg-green-600 text-white rounded-lg hover:bg-green-700 transition-colors"
                  >
                    <ExternalLink className="w-5 h-5" />
                    访问链接
                  </a>
                )}
                
                <button className="p-2 hover:bg-gray-200 dark:hover:bg-slate-600 rounded-lg transition-colors">
                  <Share2 className="w-5 h-5 text-gray-500" />
                </button>
              </div>
            </div>
          </div>

          {/* 标签 */}
          <div className="px-6 py-4">
            <div className="flex items-center gap-2">
              <Tag className="w-4 h-4 text-gray-400" />
              {selectedResource.tags.map(tag => (
                <span key={tag} className="px-3 py-1 bg-gray-100 dark:bg-slate-700 text-gray-700 dark:text-gray-300 rounded-full text-sm">
                  {tag}
                </span>
              ))}
            </div>
          </div>
        </div>

        {/* 评论区 */}
        <div className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 p-6">
          <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">
            评论 ({selectedResource.comments.length})
          </h3>
          
          {selectedResource.comments.length === 0 ? (
            <p className="text-gray-500 text-center py-8">暂无评论，来说点什么吧</p>
          ) : (
            <div className="space-y-4">
              {selectedResource.comments.map(comment => (
                <div key={comment.id} className="flex gap-3">
                  <div className="w-8 h-8 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white text-sm font-medium">
                    {comment.author.name.charAt(0)}
                  </div>
                  <div className="flex-1">
                    <div className="flex items-center gap-2">
                      <span className="font-medium text-gray-900 dark:text-white">{comment.author.name}</span>
                      <span className="text-sm text-gray-500">{formatDistanceToNow(comment.createdAt)}</span>
                    </div>
                    <p className="text-gray-700 dark:text-gray-300 mt-1">{comment.content}</p>
                  </div>
                </div>
              ))}
            </div>
          )}
        </div>
      </div>
    );
  }

  return (
    <div className={cn("space-y-6", className)}>
      {/* 头部工具栏 */}
      <div className="flex flex-col sm:flex-row gap-4 items-start sm:items-center justify-between">
        <div className="relative flex-1 max-w-md">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
          <input
            type="text"
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            placeholder="搜索资源..."
            className="w-full pl-10 pr-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          />
        </div>

        <div className="flex items-center gap-2">
          <select
            value={sortBy}
            onChange={(e) => setSortBy(e.target.value as any)}
            className="px-3 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          >
            <option value="latest">最新发布</option>
            <option value="popular">最受欢迎</option>
            <option value="downloads">最多下载</option>
          </select>
          <button className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors">
            <Plus className="w-4 h-4" />
            分享资源
          </button>
        </div>
      </div>

      {/* 类型筛选 */}
      <div className="flex flex-wrap gap-2">
        <button
          onClick={() => setSelectedType(null)}
          className={cn(
            "px-3 py-1.5 rounded-full text-sm font-medium transition-colors",
            !selectedType
              ? "bg-gray-900 text-white dark:bg-white dark:text-gray-900"
              : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
          )}
        >
          全部
        </button>
        {resourceTypes.map(type => (
          <button
            key={type.value}
            onClick={() => setSelectedType(type.value)}
            className={cn(
              "px-3 py-1.5 rounded-full text-sm font-medium transition-colors flex items-center gap-1",
              selectedType === type.value
                ? type.color
                : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
            )}
          >
            <type.icon className="w-3 h-3" />
            {type.label}
          </button>
        ))}
      </div>

      {/* 资源列表 */}
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
        {filteredResources.length === 0 ? (
          <div className="col-span-full text-center py-12">
            <FileText className="w-12 h-12 text-gray-300 mx-auto mb-4" />
            <p className="text-gray-500">暂无资源</p>
          </div>
        ) : (
          filteredResources.map(resource => {
            const typeConfig = resourceTypes.find(t => t.value === resource.type);
            const Icon = typeConfig?.icon || FileText;

            return (
              <div
                key={resource.id}
                onClick={() => setSelectedResource(resource)}
                className="bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700 overflow-hidden hover:shadow-lg transition-shadow cursor-pointer group"
              >
                {/* 类型图标 */}
                <div className={cn("h-32 flex items-center justify-center", typeConfig?.color)}>
                  <Icon className="w-16 h-16 opacity-50 group-hover:scale-110 transition-transform" />
                </div>

                <div className="p-4">
                  {/* 类型标签 */}
                  <div className="flex items-center gap-2 mb-2">
                    <span className={cn("px-2 py-0.5 text-xs rounded-full", typeConfig?.color)}>
                      {typeConfig?.label}
                    </span>
                    {resource.file && (
                      <span className="text-xs text-gray-500">{formatFileSize(resource.file.size)}</span>
                    )}
                  </div>

                  {/* 标题 */}
                  <h3 className="font-semibold text-gray-900 dark:text-white mb-2 line-clamp-2">
                    {resource.title}
                  </h3>

                  {/* 描述 */}
                  <p className="text-gray-600 dark:text-gray-400 text-sm line-clamp-2 mb-3">
                    {resource.description}
                  </p>

                  {/* 作者和时间 */}
                  <div className="flex items-center gap-2 text-sm text-gray-500 mb-3">
                    <User className="w-4 h-4" />
                    <span>{resource.author.name}</span>
                    <span>·</span>
                    <span>{formatDistanceToNow(resource.createdAt)}</span>
                  </div>

                  {/* 统计 */}
                  <div className="flex items-center gap-4 text-sm text-gray-500">
                    <button 
                      onClick={(e) => handleLike(e, resource.id)}
                      className="flex items-center gap-1 hover:text-pink-500 transition-colors"
                    >
                      <Heart className="w-4 h-4" />
                      {resource.likes}
                    </button>
                    {resource.file && (
                      <span className="flex items-center gap-1">
                        <Download className="w-4 h-4" />
                        {resource.downloads}
                      </span>
                    )}
                    <span className="flex items-center gap-1">
                      <MessageSquare className="w-4 h-4" />
                      {resource.comments.length}
                    </span>
                  </div>

                  {/* 标签 */}
                  <div className="flex flex-wrap gap-1 mt-3">
                    {resource.tags.slice(0, 3).map(tag => (
                      <span key={tag} className="text-xs px-2 py-0.5 bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-400 rounded">
                        {tag}
                      </span>
                    ))}
                  </div>
                </div>
              </div>
            );
          })
        )}
      </div>
    </div>
  );
};

export default ResourceSharing;
