import React, { useState } from 'react';
import {
  HelpCircle,
  CheckCircle2,
  MessageCircle,
  Award,
  TrendingUp,
  Clock,
  User,
  Search,
  Filter,
  Plus,
  ChevronUp,
  ChevronDown,
  Tag,
  Bookmark
} from 'lucide-react';
import { cn } from '@utils/classNames';
import type { Question, Answer, QuestionStatus } from '../../types/community';

interface QASystemProps {
  className?: string;
}

const difficulties = [
  { value: 'beginner', label: '入门', color: 'bg-green-100 text-green-700' },
  { value: 'intermediate', label: '中级', color: 'bg-blue-100 text-blue-700' },
  { value: 'advanced', label: '高级', color: 'bg-purple-100 text-purple-700' },
  { value: 'expert', label: '专家', color: 'bg-red-100 text-red-700' },
];

const statuses: { value: QuestionStatus; label: string; color: string }[] = [
  { value: 'open', label: '待解答', color: 'bg-yellow-100 text-yellow-700' },
  { value: 'answered', label: '已回答', color: 'bg-blue-100 text-blue-700' },
  { value: 'resolved', label: '已解决', color: 'bg-green-100 text-green-700' },
  { value: 'closed', label: '已关闭', color: 'bg-gray-100 text-gray-700' },
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

// 模拟问题数据
const mockQuestions: Question[] = [
  {
    id: 'q1',
    title: '如何证明连续函数在闭区间上必定有界？',
    content: '这是数学分析中的一个基本定理，我知道要用到闭区间的紧致性，但不太理解具体的证明过程。',
    author: { id: 'u1', name: '分析新手', level: 3, points: 450, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 20 },
    tags: ['数学分析', '连续性', '紧致性'],
    difficulty: 'intermediate',
    conceptId: 'continuity',
    bounty: 50,
    status: 'open',
    createdAt: Date.now() - 3600000 * 4,
    updatedAt: Date.now() - 3600000 * 4,
    views: 89,
    votes: 12,
    answers: [],
    comments: [],
  },
  {
    id: 'q2',
    title: '群同态基本定理的完整证明',
    content: '请详细证明：若 φ: G → H 是群同态，则 G/ker(φ) ≅ im(φ)。',
    author: { id: 'u2', name: '代数学习者', level: 5, points: 1200, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 60 },
    tags: ['抽象代数', '群论', '同态'],
    difficulty: 'advanced',
    conceptId: 'group-homomorphism',
    bounty: 100,
    status: 'resolved',
    createdAt: Date.now() - 86400000 * 2,
    updatedAt: Date.now() - 3600000 * 6,
    views: 234,
    votes: 28,
    answers: [
      {
        id: 'a1',
        questionId: 'q2',
        content: '证明分为以下几个步骤：\n\n1. 首先定义映射 ψ: G/ker(φ) → im(φ) 为 ψ(g ker(φ)) = φ(g)...',
        author: { id: 'u3', name: '数学专家', level: 12, points: 8500, badges: [], role: 'expert', joinDate: Date.now() - 86400000 * 365 },
        createdAt: Date.now() - 86400000,
        updatedAt: Date.now() - 86400000,
        votes: 45,
        isAccepted: true,
        comments: [],
      }
    ],
    comments: [],
  },
  {
    id: 'q3',
    title: '拓扑空间中紧致性的等价定义',
    content: '在度量空间中，紧致性等价于有界闭集。在一般拓扑空间中，有哪些等价的紧致性定义？',
    author: { id: 'u4', name: '拓扑爱好者', level: 7, points: 2300, badges: [], role: 'member', joinDate: Date.now() - 86400000 * 120 },
    tags: ['拓扑学', '紧致性', '度量空间'],
    difficulty: 'advanced',
    conceptId: 'compactness',
    bounty: 75,
    status: 'answered',
    createdAt: Date.now() - 86400000 * 3,
    updatedAt: Date.now() - 86400000,
    views: 156,
    votes: 18,
    answers: [],
    comments: [],
  },
];

export const QASystem: React.FC<QASystemProps> = ({ className }) => {
  const [questions, setQuestions] = useState<Question[]>(mockQuestions);
  const [selectedQuestion, setSelectedQuestion] = useState<Question | null>(null);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedDifficulty, setSelectedDifficulty] = useState<string | null>(null);
  const [selectedStatus, setSelectedStatus] = useState<QuestionStatus | null>(null);
  const [answerContent, setAnswerContent] = useState('');
  const [activeTab, setActiveTab] = useState<'all' | 'unanswered' | 'bounty'>('all');

  const filteredQuestions = questions.filter(q => {
    if (searchQuery && !q.title.toLowerCase().includes(searchQuery.toLowerCase())) return false;
    if (selectedDifficulty && q.difficulty !== selectedDifficulty) return false;
    if (selectedStatus && q.status !== selectedStatus) return false;
    if (activeTab === 'unanswered' && q.status !== 'open') return false;
    if (activeTab === 'bounty' && q.bounty <= 0) return false;
    return true;
  });

  const handleVote = (questionId: string, vote: 'up' | 'down') => {
    setQuestions(prev => prev.map(q => {
      if (q.id === questionId) {
        return { ...q, votes: q.votes + (vote === 'up' ? 1 : -1) };
      }
      return q;
    }));
  };

  const handleSubmitAnswer = () => {
    if (!selectedQuestion || !answerContent.trim()) return;
    
    const newAnswer: Answer = {
      id: `a${Date.now()}`,
      questionId: selectedQuestion.id,
      content: answerContent,
      author: { id: 'me', name: '我', level: 5, points: 1000, badges: [], role: 'member', joinDate: Date.now() },
      createdAt: Date.now(),
      updatedAt: Date.now(),
      votes: 0,
      isAccepted: false,
      comments: [],
    };
    
    setSelectedQuestion({
      ...selectedQuestion,
      answers: [...selectedQuestion.answers, newAnswer],
      status: 'answered',
    });
    setAnswerContent('');
  };

  const handleAcceptAnswer = (answerId: string) => {
    if (!selectedQuestion) return;
    
    setSelectedQuestion({
      ...selectedQuestion,
      answers: selectedQuestion.answers.map(a => ({
        ...a,
        isAccepted: a.id === answerId,
      })),
      status: 'resolved',
    });
  };

  // 问题详情视图
  if (selectedQuestion) {
    return (
      <div className={cn("space-y-6", className)}>
        {/* 返回按钮 */}
        <button
          onClick={() => setSelectedQuestion(null)}
          className="flex items-center gap-2 text-gray-600 hover:text-gray-900 dark:text-gray-400 dark:hover:text-white transition-colors"
        >
          <ChevronUp className="w-4 h-4 rotate-[-90deg]" />
          返回问题列表
        </button>

        {/* 问题内容 */}
        <div className="bg-white dark:bg-slate-800 rounded-xl shadow-sm border border-gray-200 dark:border-slate-700">
          <div className="p-6">
            <div className="flex items-start gap-4">
              {/* 投票 */}
              <div className="flex flex-col items-center gap-1">
                <button 
                  onClick={() => handleVote(selectedQuestion.id, 'up')}
                  className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors"
                >
                  <ChevronUp className="w-6 h-6 text-gray-500" />
                </button>
                <span className="text-lg font-semibold text-gray-900 dark:text-white">
                  {selectedQuestion.votes}
                </span>
                <button 
                  onClick={() => handleVote(selectedQuestion.id, 'down')}
                  className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors"
                >
                  <ChevronDown className="w-6 h-6 text-gray-500" />
                </button>
                
                {selectedQuestion.bounty > 0 && (
                  <div className="mt-2 flex flex-col items-center text-orange-500">
                    <Award className="w-5 h-5" />
                    <span className="text-xs font-medium">{selectedQuestion.bounty}</span>
                  </div>
                )}
              </div>

              <div className="flex-1 min-w-0">
                {/* 难度和状态 */}
                <div className="flex items-center gap-2 mb-3">
                  <span className={cn(
                    "px-2 py-1 text-xs font-medium rounded-full",
                    difficulties.find(d => d.value === selectedQuestion.difficulty)?.color
                  )}>
                    {difficulties.find(d => d.value === selectedQuestion.difficulty)?.label}
                  </span>
                  <span className={cn(
                    "px-2 py-1 text-xs font-medium rounded-full",
                    statuses.find(s => s.value === selectedQuestion.status)?.color
                  )}>
                    {statuses.find(s => s.value === selectedQuestion.status)?.label}
                  </span>
                  {selectedQuestion.bounty > 0 && (
                    <span className="px-2 py-1 text-xs font-medium rounded-full bg-orange-100 text-orange-700">
                      悬赏 {selectedQuestion.bounty} 积分
                    </span>
                  )}
                </div>

                {/* 标题 */}
                <h1 className="text-2xl font-bold text-gray-900 dark:text-white mb-4">
                  {selectedQuestion.title}
                </h1>

                {/* 作者信息 */}
                <div className="flex items-center gap-3 mb-4">
                  <div className="w-10 h-10 rounded-full bg-gradient-to-br from-green-500 to-teal-500 flex items-center justify-center text-white font-medium">
                    {selectedQuestion.author.name.charAt(0)}
                  </div>
                  <div>
                    <div className="font-medium text-gray-900 dark:text-white">
                      {selectedQuestion.author.name}
                    </div>
                    <div className="text-sm text-gray-500">
                      等级 {selectedQuestion.author.level} · {formatDistanceToNow(selectedQuestion.createdAt)}
                    </div>
                  </div>
                </div>

                {/* 内容 */}
                <div className="prose dark:prose-invert max-w-none mb-6 text-gray-700 dark:text-gray-300">
                  {selectedQuestion.content}
                </div>

                {/* 标签 */}
                {selectedQuestion.tags.length > 0 && (
                  <div className="flex flex-wrap gap-2 mb-4">
                    {selectedQuestion.tags.map(tag => (
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
                    <TrendingUp className="w-4 h-4" />
                    {selectedQuestion.views} 浏览
                  </span>
                  <span className="flex items-center gap-1">
                    <MessageCircle className="w-4 h-4" />
                    {selectedQuestion.answers.length} 回答
                  </span>
                  <span className="flex items-center gap-1">
                    <Clock className="w-4 h-4" />
                    {formatDistanceToNow(selectedQuestion.updatedAt)}更新
                  </span>
                </div>
              </div>

              {/* 收藏 */}
              <button className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors">
                <Bookmark className="w-5 h-5 text-gray-400 hover:text-blue-500" />
              </button>
            </div>
          </div>
        </div>

        {/* 答案列表 */}
        <div className="space-y-4">
          <h3 className="text-lg font-semibold text-gray-900 dark:text-white">
            {selectedQuestion.answers.length} 个回答
          </h3>
          
          {selectedQuestion.answers.map(answer => (
            <div 
              key={answer.id}
              className={cn(
                "bg-white dark:bg-slate-800 rounded-xl border",
                answer.isAccepted 
                  ? "border-green-500 dark:border-green-500" 
                  : "border-gray-200 dark:border-slate-700"
              )}
            >
              <div className="p-6">
                <div className="flex items-start gap-4">
                  {/* 投票 */}
                  <div className="flex flex-col items-center gap-1">
                    <button className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors">
                      <ChevronUp className="w-5 h-5 text-gray-500" />
                    </button>
                    <span className="font-semibold text-gray-900 dark:text-white">{answer.votes}</span>
                    <button className="p-2 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors">
                      <ChevronDown className="w-5 h-5 text-gray-500" />
                    </button>
                    
                    {answer.isAccepted && (
                      <div className="mt-2 text-green-500">
                        <CheckCircle2 className="w-6 h-6" />
                      </div>
                    )}
                  </div>

                  <div className="flex-1">
                    {/* 作者信息 */}
                    <div className="flex items-center gap-3 mb-3">
                      <div className="w-8 h-8 rounded-full bg-gradient-to-br from-blue-500 to-purple-500 flex items-center justify-center text-white text-sm font-medium">
                        {answer.author.name.charAt(0)}
                      </div>
                      <div>
                        <span className="font-medium text-gray-900 dark:text-white">
                          {answer.author.name}
                        </span>
                        <span className="text-sm text-gray-500 ml-2">
                          {formatDistanceToNow(answer.createdAt)}
                        </span>
                      </div>
                    </div>

                    {/* 答案内容 */}
                    <div className="prose dark:prose-invert max-w-none mb-4 text-gray-700 dark:text-gray-300 whitespace-pre-line">
                      {answer.content}
                    </div>

                    {/* 操作按钮 */}
                    <div className="flex items-center gap-4">
                      {!answer.isAccepted && selectedQuestion.status !== 'resolved' && (
                        <button 
                          onClick={() => handleAcceptAnswer(answer.id)}
                          className="text-sm text-green-600 hover:text-green-700 font-medium"
                        >
                          采纳为答案
                        </button>
                      )}
                      <button className="text-sm text-gray-500 hover:text-gray-700">
                        评论
                      </button>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          ))}
        </div>

        {/* 写答案 */}
        {selectedQuestion.status !== 'resolved' && (
          <div className="bg-white dark:bg-slate-800 rounded-xl shadow-sm border border-gray-200 dark:border-slate-700 p-6">
            <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-4">撰写答案</h3>
            <textarea
              value={answerContent}
              onChange={(e) => setAnswerContent(e.target.value)}
              placeholder="分享你的解答..."
              className="w-full h-40 px-4 py-3 border border-gray-300 dark:border-slate-600 rounded-lg resize-none focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
            />
            <div className="flex justify-between items-center mt-4">
              <span className="text-sm text-gray-500">
                支持 Markdown 格式
              </span>
              <button
                onClick={handleSubmitAnswer}
                disabled={!answerContent.trim()}
                className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
              >
                提交答案
              </button>
            </div>
          </div>
        )}
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
            placeholder="搜索问题..."
            className="w-full pl-10 pr-4 py-2 border border-gray-300 dark:border-slate-600 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent bg-white dark:bg-slate-700 text-gray-900 dark:text-white"
          />
        </div>

        <button className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors">
          <Plus className="w-4 h-4" />
          提问
        </button>
      </div>

      {/* 筛选标签 */}
      <div className="flex flex-wrap items-center gap-4">
        {/* 难度筛选 */}
        <div className="flex items-center gap-2">
          <Filter className="w-4 h-4 text-gray-500" />
          <select
            value={selectedDifficulty || ''}
            onChange={(e) => setSelectedDifficulty(e.target.value || null)}
            className="px-3 py-1.5 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-sm text-gray-900 dark:text-white"
          >
            <option value="">所有难度</option>
            {difficulties.map(d => (
              <option key={d.value} value={d.value}>{d.label}</option>
            ))}
          </select>
        </div>

        {/* 状态筛选 */}
        <div className="flex items-center gap-2">
          <HelpCircle className="w-4 h-4 text-gray-500" />
          <select
            value={selectedStatus || ''}
            onChange={(e) => setSelectedStatus((e.target.value || null) as QuestionStatus)}
            className="px-3 py-1.5 border border-gray-300 dark:border-slate-600 rounded-lg bg-white dark:bg-slate-700 text-sm text-gray-900 dark:text-white"
          >
            <option value="">所有状态</option>
            {statuses.map(s => (
              <option key={s.value} value={s.value}>{s.label}</option>
            ))}
          </select>
        </div>
      </div>

      {/* Tab 切换 */}
      <div className="flex gap-2 border-b border-gray-200 dark:border-slate-700">
        {[
          { key: 'all', label: '全部问题' },
          { key: 'unanswered', label: '待解答' },
          { key: 'bounty', label: '悬赏问题' },
        ].map(tab => (
          <button
            key={tab.key}
            onClick={() => setActiveTab(tab.key as any)}
            className={cn(
              "px-4 py-2 text-sm font-medium transition-colors border-b-2",
              activeTab === tab.key
                ? "text-blue-600 border-blue-600"
                : "text-gray-600 border-transparent hover:text-gray-900 dark:text-gray-400 dark:hover:text-white"
            )}
          >
            {tab.label}
          </button>
        ))}
      </div>

      {/* 问题列表 */}
      <div className="space-y-3">
        {filteredQuestions.length === 0 ? (
          <div className="text-center py-12">
            <HelpCircle className="w-12 h-12 text-gray-300 mx-auto mb-4" />
            <p className="text-gray-500">暂无问题</p>
          </div>
        ) : (
          filteredQuestions.map(question => (
            <div
              key={question.id}
              onClick={() => setSelectedQuestion(question)}
              className="bg-white dark:bg-slate-800 rounded-xl p-5 border border-gray-200 dark:border-slate-700 hover:shadow-md transition-shadow cursor-pointer"
            >
              <div className="flex items-start gap-4">
                {/* 左侧统计 */}
                <div className="flex flex-col items-center gap-2 min-w-[60px]">
                  <div className="flex flex-col items-center">
                    <span className="text-lg font-semibold text-gray-900 dark:text-white">
                      {question.votes}
                    </span>
                    <span className="text-xs text-gray-500">投票</span>
                  </div>
                  <div className={cn(
                    "flex flex-col items-center px-3 py-1 rounded-lg",
                    question.answers.length > 0 
                      ? question.status === 'resolved'
                        ? "bg-green-100 dark:bg-green-900/30 text-green-700 dark:text-green-400"
                        : "bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-400"
                      : "bg-gray-100 dark:bg-slate-700 text-gray-600 dark:text-gray-400"
                  )}>
                    <span className="text-lg font-semibold">{question.answers.length}</span>
                    <span className="text-xs">回答</span>
                  </div>
                  {question.bounty > 0 && (
                    <div className="flex flex-col items-center text-orange-500">
                      <Award className="w-5 h-5" />
                      <span className="text-xs font-medium">{question.bounty}</span>
                    </div>
                  )}
                </div>

                <div className="flex-1 min-w-0">
                  {/* 标题 */}
                  <h3 className="font-semibold text-gray-900 dark:text-white mb-2 hover:text-blue-600 transition-colors">
                    {question.title}
                  </h3>

                  {/* 内容预览 */}
                  <p className="text-gray-600 dark:text-gray-400 text-sm line-clamp-2 mb-3">
                    {question.content}
                  </p>

                  {/* 底部信息 */}
                  <div className="flex items-center justify-between flex-wrap gap-2">
                    <div className="flex items-center gap-3">
                      <span className={cn(
                        "px-2 py-0.5 text-xs rounded-full",
                        difficulties.find(d => d.value === question.difficulty)?.color
                      )}>
                        {difficulties.find(d => d.value === question.difficulty)?.label}
                      </span>
                      
                      {question.tags.slice(0, 3).map(tag => (
                        <span key={tag} className="text-xs text-gray-500 bg-gray-100 dark:bg-slate-700 px-2 py-0.5 rounded">
                          {tag}
                        </span>
                      ))}
                    </div>

                    <div className="flex items-center gap-4 text-sm text-gray-500">
                      <span className="flex items-center gap-1">
                        <User className="w-4 h-4" />
                        {question.author.name}
                      </span>
                      <span className="flex items-center gap-1">
                        <Clock className="w-4 h-4" />
                        {formatDistanceToNow(question.createdAt)}
                      </span>
                      <span>{question.views} 浏览</span>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          ))
        )}
      </div>
    </div>
  );
};

export default QASystem;
