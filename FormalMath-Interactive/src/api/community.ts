// ==================== 学习社区 API ====================

import apiClient from './client';
import type {
  DiscussionTopic,
  Reply,
  Question,
  Answer,
  StudyGroup,
  SharedResource,
  PointsRecord,
  CommunityStats,
  UserCommunityStats,
  CommunityEvent,
  Report,
  CommunityNotification,
  DiscussionCategory,
  QuestionStatus,
  GroupCategory,
  ActivityType,
  ResourceType,
  PointsType,
} from '../types/community';

// ==================== 讨论区 API ====================

export const discussionApi = {
  // 获取主题列表
  getTopics: async (params?: {
    category?: DiscussionCategory;
    tag?: string;
    author?: string;
    search?: string;
    sortBy?: 'latest' | 'hot' | 'unanswered' | 'top';
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      topics: DiscussionTopic[];
      total: number;
      hasMore: boolean;
    }>('/community/discussions', { params });
    return response.data;
  },

  // 获取单个主题
  getTopic: async (id: string) => {
    const response = await apiClient.get<DiscussionTopic>(`/community/discussions/${id}`);
    return response.data;
  },

  // 创建主题
  createTopic: async (data: {
    title: string;
    content: string;
    category: DiscussionCategory;
    tags: string[];
  }) => {
    const response = await apiClient.post<DiscussionTopic>('/community/discussions', data);
    return response.data;
  },

  // 更新主题
  updateTopic: async (id: string, data: Partial<DiscussionTopic>) => {
    const response = await apiClient.put<DiscussionTopic>(`/community/discussions/${id}`, data);
    return response.data;
  },

  // 删除主题
  deleteTopic: async (id: string) => {
    await apiClient.delete(`/community/discussions/${id}`);
  },

  // 点赞主题
  likeTopic: async (id: string) => {
    const response = await apiClient.post<{ likes: number }>(`/community/discussions/${id}/like`);
    return response.data;
  },

  // 添加回复
  addReply: async (topicId: string, content: string, parentReplyId?: string) => {
    const response = await apiClient.post<Reply>(`/community/discussions/${topicId}/replies`, {
      content,
      parentReplyId,
    });
    return response.data;
  },

  // 更新回复
  updateReply: async (replyId: string, content: string) => {
    const response = await apiClient.put<Reply>(`/community/replies/${replyId}`, { content });
    return response.data;
  },

  // 删除回复
  deleteReply: async (replyId: string) => {
    await apiClient.delete(`/community/replies/${replyId}`);
  },

  // 点赞回复
  likeReply: async (replyId: string) => {
    const response = await apiClient.post<{ likes: number }>(`/community/replies/${replyId}/like`);
    return response.data;
  },

  // 采纳回复
  acceptReply: async (topicId: string, replyId: string) => {
    const response = await apiClient.post<DiscussionTopic>(
      `/community/discussions/${topicId}/accept-reply`,
      { replyId }
    );
    return response.data;
  },

  // 获取热门标签
  getPopularTags: async (limit: number = 20) => {
    const response = await apiClient.get<{ tag: string; count: number }[]>(
      '/community/discussions/tags',
      { params: { limit } }
    );
    return response.data;
  },
};

// ==================== 问答系统 API ====================

export const qaApi = {
  // 获取问题列表
  getQuestions: async (params?: {
    status?: QuestionStatus;
    difficulty?: string;
    tag?: string;
    conceptId?: string;
    unanswered?: boolean;
    bounty?: boolean;
    search?: string;
    sortBy?: 'latest' | 'votes' | 'bounty' | 'unanswered';
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      questions: Question[];
      total: number;
      hasMore: boolean;
    }>('/community/questions', { params });
    return response.data;
  },

  // 获取单个问题
  getQuestion: async (id: string) => {
    const response = await apiClient.get<Question>(`/community/questions/${id}`);
    return response.data;
  },

  // 创建问题
  createQuestion: async (data: {
    title: string;
    content: string;
    difficulty: string;
    conceptId?: string;
    tags: string[];
    bounty?: number;
  }) => {
    const response = await apiClient.post<Question>('/community/questions', data);
    return response.data;
  },

  // 更新问题
  updateQuestion: async (id: string, data: Partial<Question>) => {
    const response = await apiClient.put<Question>(`/community/questions/${id}`, data);
    return response.data;
  },

  // 删除问题
  deleteQuestion: async (id: string) => {
    await apiClient.delete(`/community/questions/${id}`);
  },

  // 投票问题
  voteQuestion: async (id: string, vote: 'up' | 'down') => {
    const response = await apiClient.post<{ votes: number }>(`/community/questions/${id}/vote`, {
      vote,
    });
    return response.data;
  },

  // 添加答案
  addAnswer: async (questionId: string, content: string) => {
    const response = await apiClient.post<Answer>(`/community/questions/${questionId}/answers`, {
      content,
    });
    return response.data;
  },

  // 更新答案
  updateAnswer: async (answerId: string, content: string) => {
    const response = await apiClient.put<Answer>(`/community/answers/${answerId}`, { content });
    return response.data;
  },

  // 删除答案
  deleteAnswer: async (answerId: string) => {
    await apiClient.delete(`/community/answers/${answerId}`);
  },

  // 投票答案
  voteAnswer: async (answerId: string, vote: 'up' | 'down') => {
    const response = await apiClient.post<{ votes: number }>(`/community/answers/${answerId}/vote`, {
      vote,
    });
    return response.data;
  },

  // 采纳答案
  acceptAnswer: async (questionId: string, answerId: string) => {
    const response = await apiClient.post<Question>(
      `/community/questions/${questionId}/accept-answer`,
      { answerId }
    );
    return response.data;
  },

  // 添加评论
  addComment: async (targetType: 'question' | 'answer', targetId: string, content: string) => {
    const response = await apiClient.post(`/community/${targetType}s/${targetId}/comments`, {
      content,
    });
    return response.data;
  },
};

// ==================== 学习小组 API ====================

export const groupApi = {
  // 获取小组列表
  getGroups: async (params?: {
    category?: GroupCategory;
    search?: string;
    sortBy?: 'members' | 'activity' | 'newest';
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      groups: StudyGroup[];
      total: number;
      hasMore: boolean;
    }>('/community/groups', { params });
    return response.data;
  },

  // 获取推荐小组
  getRecommendedGroups: async (limit: number = 5) => {
    const response = await apiClient.get<StudyGroup[]>('/community/groups/recommended', {
      params: { limit },
    });
    return response.data;
  },

  // 获取我的小组
  getMyGroups: async () => {
    const response = await apiClient.get<StudyGroup[]>('/community/groups/my');
    return response.data;
  },

  // 获取单个小组
  getGroup: async (id: string) => {
    const response = await apiClient.get<StudyGroup>(`/community/groups/${id}`);
    return response.data;
  },

  // 创建小组
  createGroup: async (data: {
    name: string;
    description: string;
    category: GroupCategory;
    tags: string[];
    maxMembers: number;
    isPublic: boolean;
  }) => {
    const response = await apiClient.post<StudyGroup>('/community/groups', data);
    return response.data;
  },

  // 更新小组
  updateGroup: async (id: string, data: Partial<StudyGroup>) => {
    const response = await apiClient.put<StudyGroup>(`/community/groups/${id}`, data);
    return response.data;
  },

  // 删除小组
  deleteGroup: async (id: string) => {
    await apiClient.delete(`/community/groups/${id}`);
  },

  // 加入小组
  joinGroup: async (id: string) => {
    const response = await apiClient.post<StudyGroup>(`/community/groups/${id}/join`);
    return response.data;
  },

  // 离开小组
  leaveGroup: async (id: string) => {
    await apiClient.post(`/community/groups/${id}/leave`);
  },

  // 邀请成员
  inviteMember: async (groupId: string, userId: string) => {
    const response = await apiClient.post(`/community/groups/${groupId}/invite`, { userId });
    return response.data;
  },

  // 移除成员
  removeMember: async (groupId: string, userId: string) => {
    await apiClient.delete(`/community/groups/${groupId}/members/${userId}`);
  },

  // 创建活动
  createActivity: async (
    groupId: string,
    data: {
      type: ActivityType;
      title: string;
      description: string;
      scheduledAt: number;
      duration: number;
    }
  ) => {
    const response = await apiClient.post(`/community/groups/${groupId}/activities`, data);
    return response.data;
  },

  // 参加活动
  joinActivity: async (groupId: string, activityId: string) => {
    const response = await apiClient.post(
      `/community/groups/${groupId}/activities/${activityId}/join`
    );
    return response.data;
  },
};

// ==================== 内容分享 API ====================

export const resourceApi = {
  // 获取资源列表
  getResources: async (params?: {
    type?: ResourceType;
    tag?: string;
    author?: string;
    groupId?: string;
    search?: string;
    sortBy?: 'latest' | 'popular' | 'downloads';
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      resources: SharedResource[];
      total: number;
      hasMore: boolean;
    }>('/community/resources', { params });
    return response.data;
  },

  // 获取单个资源
  getResource: async (id: string) => {
    const response = await apiClient.get<SharedResource>(`/community/resources/${id}`);
    return response.data;
  },

  // 创建资源
  createResource: async (data: {
    title: string;
    description: string;
    type: ResourceType;
    url?: string;
    tags: string[];
    groupId?: string;
  }) => {
    const response = await apiClient.post<SharedResource>('/community/resources', data);
    return response.data;
  },

  // 更新资源
  updateResource: async (id: string, data: Partial<SharedResource>) => {
    const response = await apiClient.put<SharedResource>(`/community/resources/${id}`, data);
    return response.data;
  },

  // 删除资源
  deleteResource: async (id: string) => {
    await apiClient.delete(`/community/resources/${id}`);
  },

  // 点赞资源
  likeResource: async (id: string) => {
    const response = await apiClient.post<{ likes: number }>(`/community/resources/${id}/like`);
    return response.data;
  },

  // 下载资源
  downloadResource: async (id: string) => {
    const response = await apiClient.get<{ url: string; downloads: number }>(
      `/community/resources/${id}/download`
    );
    return response.data;
  },

  // 上传文件
  uploadFile: async (file: File) => {
    const formData = new FormData();
    formData.append('file', file);
    const response = await apiClient.post('/community/resources/upload', formData, {
      headers: { 'Content-Type': 'multipart/form-data' },
    });
    return response.data;
  },
};

// ==================== 积分系统 API ====================

export const pointsApi = {
  // 获取积分记录
  getPointsRecords: async (params?: {
    type?: PointsType;
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      records: PointsRecord[];
      total: number;
    }>('/community/points/records', { params });
    return response.data;
  },

  // 获取积分规则
  getPointsRules: async () => {
    const response = await apiClient.get('/community/points/rules');
    return response.data;
  },

  // 获取等级定义
  getLevelDefinitions: async () => {
    const response = await apiClient.get('/community/points/levels');
    return response.data;
  },

  // 获取排行榜
  getLeaderboard: async (params?: {
    type?: 'total' | 'weekly' | 'monthly';
    limit?: number;
  }) => {
    const response = await apiClient.get('/community/points/leaderboard', { params });
    return response.data;
  },

  // 签到
  checkIn: async () => {
    const response = await apiClient.post('/community/points/checkin');
    return response.data;
  },

  // 获取签到状态
  getCheckInStatus: async () => {
    const response = await apiClient.get('/community/points/checkin-status');
    return response.data;
  },
};

// ==================== 社区统计 API ====================

export const statsApi = {
  // 获取社区统计
  getCommunityStats: async () => {
    const response = await apiClient.get<CommunityStats>('/community/stats');
    return response.data;
  },

  // 获取用户社区统计
  getUserStats: async (userId?: string) => {
    const response = await apiClient.get<UserCommunityStats>(
      `/community/stats/user${userId ? `/${userId}` : ''}`
    );
    return response.data;
  },

  // 获取活动日历
  getActivityCalendar: async (year: number, month: number) => {
    const response = await apiClient.get('/community/stats/calendar', {
      params: { year, month },
    });
    return response.data;
  },
};

// ==================== 社区事件 API ====================

export const eventApi = {
  // 获取事件列表
  getEvents: async (params?: {
    status?: string;
    type?: string;
    page?: number;
    limit?: number;
  }) => {
    const response = await apiClient.get<{
      events: CommunityEvent[];
      total: number;
    }>('/community/events', { params });
    return response.data;
  },

  // 获取单个事件
  getEvent: async (id: string) => {
    const response = await apiClient.get<CommunityEvent>(`/community/events/${id}`);
    return response.data;
  },

  // 报名参加事件
  registerEvent: async (id: string) => {
    const response = await apiClient.post<CommunityEvent>(`/community/events/${id}/register`);
    return response.data;
  },

  // 取消报名
  cancelRegistration: async (id: string) => {
    await apiClient.post(`/community/events/${id}/cancel`);
  },
};

// ==================== 举报 API ====================

export const reportApi = {
  // 创建举报
  createReport: async (data: {
    targetType: string;
    targetId: string;
    reason: string;
    description: string;
  }) => {
    const response = await apiClient.post<Report>('/community/reports', data);
    return response.data;
  },

  // 获取我的举报
  getMyReports: async () => {
    const response = await apiClient.get<Report[]>('/community/reports/my');
    return response.data;
  },
};

// ==================== 通知 API ====================

export const notificationApi = {
  // 获取通知列表
  getNotifications: async (params?: { unreadOnly?: boolean; page?: number; limit?: number }) => {
    const response = await apiClient.get<{
      notifications: CommunityNotification[];
      unreadCount: number;
    }>('/community/notifications', { params });
    return response.data;
  },

  // 标记通知为已读
  markAsRead: async (id: string) => {
    await apiClient.post(`/community/notifications/${id}/read`);
  },

  // 标记所有通知为已读
  markAllAsRead: async () => {
    await apiClient.post('/community/notifications/read-all');
  },

  // 删除通知
  deleteNotification: async (id: string) => {
    await apiClient.delete(`/community/notifications/${id}`);
  },

  // 订阅通知（WebSocket）
  subscribeNotifications: (_callback: (notification: CommunityNotification) => void) => {
    // 实际实现会使用 WebSocket
    console.log('Subscribing to notifications...');
    return () => {
      console.log('Unsubscribing from notifications...');
    };
  },
};
