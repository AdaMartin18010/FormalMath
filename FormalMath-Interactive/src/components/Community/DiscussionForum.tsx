import React, { useState, useEffect, useCallback } from 'react';
import { 
  MessageSquare, 
  ThumbsUp, 
  Eye, 
  Tag, 
  Pin, 
  Lock,
  ChevronUp,
  Clock,
  User,
  Filter,
  Search,
  Plus,
  MoreHorizontal
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { DiscussionTopic, DiscussionCategory, Reply } from '../../types/community';

interface DiscussionForumProps {
  className?: string;
}

const categories: { value: DiscussionCategory; label: string; color: string }[] = [
  { value: 'general', label: '综合讨论', color: 'bg-blue-100 text-blue-700' },
  { value: 'question', label: '问题求助', color: 'bg-red-100 text-red-700' },
  { value: 'share', label: '学习分享', color: 'bg-green-100 text-green-700' },
  { value: 'challenge', label: '挑战讨论', color: 'bg-purple-100 text-purple-700' },
  { value: 'resource', label: '资源分享', color: 'bg-yellow-100 text-yellow-700' },
  { value: 'announcement', label: '公告', color: 'bg-orange-100 text-orange-700' },
];

const sortOptions = [
  { value: 'latest', label: '最新发布' },
  { value: 'hot', label: '热门讨论' },
  { value: 'unanswered', label: '等待回复' },
  { value: 'top', label: '最多点赞' },
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
  if (days < 30) return `${days}天前`;
  const months = Math.floor(days / 30);
  if (months < 12) return `${months}个月前`;
  return `${Math.floor(months / 12)}年前`;
};

// 模拟数据
const mockTopics: DiscussionTopic[] = [
  {
    id: '1',
    title: '如何理解群论中的Sylow定理？',
    content: '在学习有限群理论时，Sylow定理一直是一个难点。有没有好的学习方法或直观解释？',
    category: 'question',
    author: { id: 'u1', name: '数学爱好者', level: 5, points: 1200, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 30 },
    tags: ['群论', 'Sylow定理', '抽象代数'],
    createdAt: Date.now() - 3600000 * 2,
    updatedAt: Date.now() - 3600000 * 2,
    views: 156,
    replies: [],
    likes: 23,
    isPinned: true,
    isLocked: false,
  },
  {
    id: '2',
    title: '分享一些拓扑学的学习资源',
    content: '整理了一些点集拓扑和代数拓扑的优质资源，包括教材、视频课程和习题集。',
    category: 'resource',
    author: { id: 'u2', name: '拓扑迷', level: 8, points: 3500, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 90 },
    tags: ['拓扑学', '学习资源', '推荐'],
    createdAt: Date.now() - 86400000,
    updatedAt: Date.now() - 86400000,
    views: 423,
    replies: [],
    likes: 67,
    isPinned: false,
    isLocked: false,
  },
  {
    id: '3',
    title: '本周学习挑战：证明黎曼ζ函数的欧拉乘积公式',
    content: '欢迎大家参与本周的数学挑战！目标：理解并证明黎曼ζ函数的欧拉乘积公式。',
    category: 'challenge',
    author: { id: 'u3', name: '挑战发起者', level: 10, points: 5200, badges: [], role: 'moderator', joinDate: Date.now() - 86400000 * 180 },
    tags: ['黎曼ζ函数', '数论', '挑战'],
    createdAt: Date.now() - 86400000 * 2,
    updatedAt: Date.now() - 86400000 * 2,
    views: 892,
    replies: [],
    likes: 145,
    isPinned: true,
    isLocked: false,
  },
];

export const DiscussionForum: React.FC<DiscussionForumProps> = ({ className }) => {
  const [topics, setTopics] = useState<DiscussionTopic[]>(mockTopics);
  const [loading, setLoading] = useState(false);
  const [selectedCategory, setSelectedCategory] = useState<DiscussionCategory | null>(null);
  const [sortBy, setSortBy] = useState('latest');
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedTopic, setSelectedTopic] = useState<DiscussionTopic | null>(null);
  const [replyContent, setReplyContent] = useState('');
  const [isSubmitting, setIsSubmitting] = useState(false);

  const filteredTopics = topics.filter(topic => {
    if (selectedCategory && topic.category !== selectedCategory) return false;
    if (searchQuery && !topic.title.toLowerCase().includes(searchQuery.toLowerCase())) return false;
    return true;
  });

  const handleTopicClick = (topic: DiscussionTopic) => {
    setSelectedTopic(topic);
  };

  const handleSubmitReply = async () => {
    if (!selectedTopic || !replyContent.trim()) return;
    
    setIsSubmitting(true);
    // 模拟提交
    setTimeout(() => {
      const newReply: Reply = {
        id: `r${Date.now()}`,
        topicId: selectedTopic.id,
        content: replyContent,
        author: { id: 'me', name: '我', level: 3, points: 500, badges: [], role: 'member', joinDate: Date.now() },
        createdAt: Date.now(),
        updatedAt: Date.now(),
        likes: 0,
        replies: [],
        isAccepted: false,
      };
      setSelectedTopic({
        ...selectedTopic,
        replies: [...selectedTopic.replies, newReply],
      });
      setReplyContent('');
      setIsSubmitting(false);
    }, 500);
  };

  const handleLikeTopic = (e: React.MouseEvent, topicId: string) => {
    e.stopPropagation();
    setTopics(prev => prev.map(t => 
      t.id === topicId ? { ...t, likes: t.likes + 1 } : t
    ));
  };

  // 主题详情视图
  if (selectedTopic) {
    return (
      <div className={cn("space-y-6", className)}>
        {/* 返回按钮 */}
        <button
          onClick={() => setSelectedTopic(null)}
          className="flex items-center gap-2 text-gray-600 hover:text-gray-900 dark:text-gray-400 dark:hover:text-white transition-colors"
        >
          <ChevronUp className="w-4 h-4 rotate-[-90deg]" />
          返回列表
        </button>

        {/* 主题内容 */}
        <div className="bg-white dark:bg-slate-800 rounded-xl shadow-sm border border-gray-200 dark:border-slate-700">
          <div className="p-6">
            <div className="flex items-start gap-4">
              {/* 投票区 */}
              <div className="flex flex-col items-center gap-1">
                <button className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors">
                  <ChevronUp className="w-6 h-6 text-gray-500" />
                </button>
                <span className="text-lg font-semibold text-gray-900 dark:text-white">
                  {selectedTopic.likes}
                </span>
              </div>

              <div className="flex-1 min-w-0">
                {/* 分类和标签 */}
                <div className="flex items-center gap-2 mb-3">
                  <span className={cn(
                    "px-2 py-1 text-xs font-medium rounded-full",
                    categories.find(c => c.value === selectedTopic.category)?.color
                  )}>
                    {categories.find(c => c.value === selectedTopic.category)?.label}
                  </span>
                  {selectedTopic.isPinned && (
                    <Pin className="w-4 h-4 text-orange-500" />
                  )}
                  {selectedTopic.isLocked && (
                    <Lock className="w-4 h-4 text-gray-500" />
                  )}
                </div>

                {/* 标题 */}
                <h1 className="text-2xl font-bold text-gray-900 dark:text-white mb-4">
                  {selectedTopic.title}
                </h1>

                {/* 作者信息 */}
                <div className="flex items-center gap-3 mb-4">
                  <div className="w-10 h-10 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white font-medium">
                    {selectedTopic.author.name.charAt(0)}
                  </div>
                  <div>
                    <div className="font-medium text-gray-900 dark:text-white">
                      {selectedTopic.author.name}
                    </div>
                    <div className="text-sm text-gray-500">
                      等级 {selectedTopic.author.level} · {formatDistanceToNow(selectedTopic.createdAt)}
                    </div>
                  </div>
                </div>

                {/* 内容 */}
                <div className="prose dark:prose-invert max-w-none mb-6 text-gray-700 dark:text-gray-300">
                  {selectedTopic.content}
                </div>

                {/* 标签 */}
                {selectedTopic.tags.length > 0 && (
                  <div className="flex flex-wrap gap-2 mb-4">
                    {selectedTopic.tags.map(tag => (
                      <span key={tag} className="flex items-center gap-1 px-2 py-1 bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-300 text-sm rounded">
                        <Tag className="w-3 h-3" />
                        {tag}
                      </span>
                    ))}
                  </div>
                )}

                {/* 统计 */}
                <div className="flex items-center gap-6 text-sm text-gray-500">
                  <span className="flex items-center gap-1">
                    <Eye className="w-4 h-4" />
                    {selectedTopic.views} 浏览
                  </span>
                  <span className="flex items-center gap-1">
                    <MessageSquare className="w-4 h-4" />
                    {selectedTopic.replies.length} 回复
                  </span>
                </div>
              </div>
            </div>
          </div>
        </div>

        {/* 回复列表 */}
        <div className="space-y-4">
          <h3 className="text-lg font-semibold text-gray-900 dark:text-white">
            {selectedTopic.replies.length} 条回复
          </h3>
          
          {selectedTopic.replies.map(reply => (
            <ReplyCard key={reply.id} reply={reply} />
          ))}
        </div>

        {/* 回复框 */}
        <div className="bg-white dark:bg-slate-800 rounded-xl shadow-sm border border-gray-200 dark:border-slate-700 p-6">
          <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">发表回复</h3>
          <textarea
            value={replyContent}
            onChange={(e) => setReplyContent(e.target.value)}
            placeholder="分享你的想法..."
            className="w-full h-32 px-4 py-3 border border-gray-300 dark:border-slate-600 rounded-lg resize-none focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          />
          <div className="flex justify-end mt-4">
            <button
              onClick={handleSubmitReply}
              disabled={!replyContent.trim() || isSubmitting}
              className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              {isSubmitting ? '发送中...' : '发送回复'}
            </button>
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className={cn("space-y-6", className)}>
      {/* 头部工具栏 */}
      <div className="flex flex-col sm:flex-row gap-4 items-start sm:items-center justify-between">
        {/* 搜索 */}
        <div className="relative flex-1 max-w-md">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
          <input
            type="text"
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            placeholder="搜索讨论..."
            className="w-full pl-10 pr-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          />
        </div>

        {/* 排序 */}
        <div className="flex items-center gap-2">
          <Filter className="w-5 h-5 text-gray-500" />
          <select
            value={sortBy}
            onChange={(e) => setSortBy(e.target.value)}
            className="px-3 py-2 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          >
            {sortOptions.map(opt => (
              <option key={opt.value} value={opt.value}>{opt.label}</option>
            ))}
          </select>
          <button className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors">
            <Plus className="w-4 h-4" />
            新建讨论
          </button>
        </div>
      </div>

      {/* 分类筛选 */}
      <div className="flex flex-wrap gap-2">
        <button
          onClick={() => setSelectedCategory(null)}
          className={cn(
            "px-3 py-1.5 rounded-full text-sm font-medium transition-colors",
            !selectedCategory
              ? "bg-gray-900 text-white dark:bg-white dark:text-gray-900"
              : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
          )}
        >
          全部
        </button>
        {categories.map(cat => (
          <button
            key={cat.value}
            onClick={() => setSelectedCategory(cat.value)}
            className={cn(
              "px-3 py-1.5 rounded-full text-sm font-medium transition-colors",
              selectedCategory === cat.value
                ? cat.color
                : "bg-gray-100 text-gray-700 hover:bg-gray-200 dark:bg-slate-700 dark:text-gray-300"
            )}
          >
            {cat.label}
          </button>
        ))}
      </div>

      {/* 主题列表 */}
      <div className="space-y-3">
        {loading ? (
          // 加载骨架
          Array.from({ length: 3 }).map((_, i) => (
            <div key={i} className="bg-white dark:bg-slate-800 rounded-xl p-6 animate-pulse">
              <div className="h-4 bg-gray-200 dark:bg-slate-700 rounded w-3/4 mb-3" />
              <div className="h-3 bg-gray-200 dark:bg-slate-700 rounded w-1/2" />
            </div>
          ))
        ) : filteredTopics.length === 0 ? (
          <div className="text-center py-12">
            <MessageSquare className="w-12 h-12 text-gray-300 mx-auto mb-4" />
            <p className="text-gray-500">暂无讨论主题</p>
          </div>
        ) : (
          filteredTopics.map(topic => (
            <div
              key={topic.id}
              onClick={() => handleTopicClick(topic)}
              className="bg-white dark:bg-slate-800 rounded-xl p-5 border border-gray-200 dark:border-slate-700 hover:shadow-md transition-shadow cursor-pointer"
            >
              <div className="flex items-start gap-4">
                {/* 投票数 */}
                <div className="flex flex-col items-center min-w-[60px]">
                  <ChevronUp className="w-5 h-5 text-gray-400" />
                  <span className="font-semibold text-gray-900 dark:text-white">{topic.likes}</span>
                </div>

                <div className="flex-1 min-w-0">
                  {/* 标题和标签 */}
                  <div className="flex items-center gap-2 mb-2">
                    <h3 className="font-semibold text-gray-900 dark:text-white truncate">
                      {topic.isPinned && <Pin className="w-4 h-4 text-orange-500 inline mr-1" />}
                      {topic.isLocked && <Lock className="w-4 h-4 text-gray-500 inline mr-1" />}
                      {topic.title}
                    </h3>
                    <span className={cn(
                      "px-2 py-0.5 text-xs rounded-full",
                      categories.find(c => c.value === topic.category)?.color
                    )}>
                      {categories.find(c => c.value === topic.category)?.label}
                    </span>
                  </div>

                  {/* 内容预览 */}
                  <p className="text-gray-600 dark:text-gray-400 text-sm line-clamp-2 mb-3">
                    {topic.content}
                  </p>

                  {/* 底部信息 */}
                  <div className="flex items-center justify-between">
                    <div className="flex items-center gap-4 text-sm text-gray-500">
                      <span className="flex items-center gap-1">
                        <User className="w-4 h-4" />
                        {topic.author.name}
                      </span>
                      <span className="flex items-center gap-1">
                        <Clock className="w-4 h-4" />
                        {formatDistanceToNow(topic.createdAt)}
                      </span>
                      <span className="flex items-center gap-1">
                        <MessageSquare className="w-4 h-4" />
                        {topic.replies.length}
                      </span>
                      <span className="flex items-center gap-1">
                        <Eye className="w-4 h-4" />
                        {topic.views}
                      </span>
                    </div>

                    <div className="flex items-center gap-2">
                      {topic.tags.slice(0, 3).map(tag => (
                        <span key={tag} className="text-xs text-gray-500 bg-gray-100 dark:bg-slate-700 px-2 py-0.5 rounded">
                          {tag}
                        </span>
                      ))}
                    </div>
                  </div>
                </div>

                {/* 操作按钮 */}
                <button
                  onClick={(e) => handleLikeTopic(e, topic.id)}
                  className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors"
                >
                  <ThumbsUp className="w-5 h-5 text-gray-400 hover:text-blue-500" />
                </button>
              </div>
            </div>
          ))
        )}
      </div>
    </div>
  );
};

// 回复卡片组件
const ReplyCard: React.FC<{ reply: Reply; depth?: number }> = ({ reply, depth = 0 }) => {
  return (
    <div className={cn(
      "bg-white dark:bg-slate-800 rounded-xl border border-gray-200 dark:border-slate-700",
      depth > 0 && "ml-8 border-l-4 border-l-blue-200"
    )}>
      <div className="p-5">
        <div className="flex items-start gap-3">
          <div className="w-8 h-8 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white text-sm font-medium">
            {reply.author.name.charAt(0)}
          </div>
          <div className="flex-1">
            <div className="flex items-center gap-2 mb-2">
              <span className="font-medium text-gray-900 dark:text-white">
                {reply.author.name}
              </span>
              <span className="text-sm text-gray-500">
                {formatDistanceToNow(reply.createdAt)}
              </span>
              {reply.isAccepted && (
                <span className="px-2 py-0.5 bg-green-100 text-green-700 text-xs rounded-full">
                  已采纳
                </span>
              )}
            </div>
            <div className="text-gray-700 dark:text-gray-300 mb-3">
              {reply.content}
            </div>
            <div className="flex items-center gap-4">
              <button className="flex items-center gap-1 text-sm text-gray-500 hover:text-blue-600 transition-colors">
                <ThumbsUp className="w-4 h-4" />
                {reply.likes}
              </button>
              <button className="text-sm text-gray-500 hover:text-blue-600 transition-colors">
                回复
              </button>
            </div>
          </div>
        </div>
      </div>
      
      {/* 嵌套回复 */}
      {reply.replies?.length > 0 && (
        <div className="pb-4">
          {reply.replies.map(nestedReply => (
            <ReplyCard key={nestedReply.id} reply={nestedReply} depth={depth + 1} />
          ))}
        </div>
      )}
    </div>
  );
};

export default DiscussionForum;
