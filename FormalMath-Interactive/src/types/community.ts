// ==================== 学习社区类型定义 ====================

// 讨论主题分类
export type DiscussionCategory = 
  | 'general'      // 综合讨论
  | 'question'     // 问题求助
  | 'share'        // 学习分享
  | 'challenge'    // 挑战讨论
  | 'resource'     // 资源分享
  | 'announcement'; // 公告

// 讨论主题
export interface DiscussionTopic {
  id: string;
  title: string;
  content: string;
  category: DiscussionCategory;
  author: CommunityUser;
  tags: string[];
  createdAt: number;
  updatedAt: number;
  views: number;
  replies: Reply[];
  likes: number;
  isPinned: boolean;
  isLocked: boolean;
  acceptedAnswerId?: string;
}

// 回复
export interface Reply {
  id: string;
  topicId: string;
  content: string;
  author: CommunityUser;
  createdAt: number;
  updatedAt: number;
  likes: number;
  replies: Reply[]; // 嵌套回复
  isAccepted: boolean;
}

// 社区用户
export interface CommunityUser {
  id: string;
  name: string;
  avatar?: string;
  level: number;
  points: number;
  badges: Badge[];
  role: UserRole;
  joinDate: number;
}

// 用户角色
export type UserRole = 'admin' | 'moderator' | 'expert' | 'member' | 'newbie';

// 徽章
export interface Badge {
  id: string;
  name: string;
  description: string;
  icon: string;
  category: BadgeCategory;
  earnedAt: number;
  rarity: 'common' | 'rare' | 'epic' | 'legendary';
}

// 徽章类别
export type BadgeCategory = 
  | 'participation'  // 参与类
  | 'achievement'    // 成就类
  | 'contribution'   // 贡献类
  | 'expertise'      // 专业类
  | 'social';        // 社交类

// 问答问题
export interface Question {
  id: string;
  title: string;
  content: string;
  author: CommunityUser;
  tags: string[];
  difficulty: 'beginner' | 'intermediate' | 'advanced' | 'expert';
  conceptId?: string; // 关联的概念ID
  bounty: number; // 悬赏积分
  status: QuestionStatus;
  createdAt: number;
  updatedAt: number;
  views: number;
  votes: number;
  answers: Answer[];
  comments: Comment[];
}

// 问题状态
export type QuestionStatus = 'open' | 'answered' | 'resolved' | 'closed';

// 答案
export interface Answer {
  id: string;
  questionId: string;
  content: string;
  author: CommunityUser;
  createdAt: number;
  updatedAt: number;
  votes: number;
  isAccepted: boolean;
  comments: Comment[];
}

// 评论
export interface Comment {
  id: string;
  content: string;
  author: CommunityUser;
  createdAt: number;
  likes: number;
}

// 学习小组
export interface StudyGroup {
  id: string;
  name: string;
  description: string;
  cover?: string;
  category: GroupCategory;
  tags: string[];
  owner: CommunityUser;
  members: GroupMember[];
  maxMembers: number;
  isPublic: boolean;
  createdAt: number;
  activities: GroupActivity[];
  resources: SharedResource[];
  discussionTopics: string[]; // 关联的讨论主题ID
  schedule: StudySchedule[];
}

// 小组成员
export interface GroupMember {
  user: CommunityUser;
  role: GroupRole;
  joinedAt: number;
  contribution: number;
  lastActive: number;
}

// 小组角色
export type GroupRole = 'owner' | 'admin' | 'member';

// 小组分类
export type GroupCategory = 
  | 'algebra' 
  | 'geometry' 
  | 'analysis' 
  | 'topology' 
  | 'logic' 
  | 'number-theory'
  | 'applied-math'
  | 'general';

// 小组活动
export interface GroupActivity {
  id: string;
  type: ActivityType;
  title: string;
  description: string;
  scheduledAt: number;
  duration: number; // 分钟
  participants: string[];
  status: ActivityStatus;
}

// 活动类型
export type ActivityType = 'study' | 'discussion' | 'challenge' | 'review' | 'qanda';

// 活动状态
export type ActivityStatus = 'upcoming' | 'ongoing' | 'completed' | 'cancelled';

// 学习日程
export interface StudySchedule {
  id: string;
  dayOfWeek: number; // 0-6
  startTime: string; // HH:mm
  duration: number; // 分钟
  topic: string;
  isRecurring: boolean;
}

// 分享资源
export interface SharedResource {
  id: string;
  title: string;
  description: string;
  type: ResourceType;
  url?: string;
  file?: FileInfo;
  author: CommunityUser;
  groupId?: string;
  tags: string[];
  createdAt: number;
  likes: number;
  downloads: number;
  comments: Comment[];
}

// 资源类型
export type ResourceType = 'note' | 'article' | 'video' | 'code' | 'problem' | 'book' | 'link';

// 文件信息
export interface FileInfo {
  name: string;
  size: number;
  mimeType: string;
  url: string;
}

// 积分记录
export interface PointsRecord {
  id: string;
  userId: string;
  points: number; // 正数表示获得，负数表示扣除
  type: PointsType;
  description: string;
  relatedId?: string; // 关联的资源ID
  createdAt: number;
}

// 积分类型
export type PointsType = 
  | 'daily_login'      // 每日登录
  | 'post_topic'       // 发布主题
  | 'post_reply'       // 发布回复
  | 'receive_like'     // 获得点赞
  | 'answer_accepted'  // 答案被采纳
  | 'share_resource'   // 分享资源
  | 'complete_challenge' // 完成挑战
  | 'help_others'      // 帮助他人
  | 'excellent_content' // 优质内容
  | 'report_violation' // 举报违规
  | 'purchase';        // 购买/兑换

// 积分规则
export interface PointsRule {
  type: PointsType;
  points: number;
  dailyLimit?: number;
  description: string;
}

// 等级定义
export interface LevelDefinition {
  level: number;
  name: string;
  minPoints: number;
  maxPoints: number;
  icon: string;
  privileges: string[];
}

// 社区统计
export interface CommunityStats {
  totalUsers: number;
  totalTopics: number;
  totalReplies: number;
  totalQuestions: number;
  totalAnswers: number;
  totalGroups: number;
  totalResources: number;
  activeUsersToday: number;
  newUsersToday: number;
}

// 用户社区统计
export interface UserCommunityStats {
  userId: string;
  topicsPosted: number;
  repliesPosted: number;
  questionsAsked: number;
  questionsAnswered: number;
  answersAccepted: number;
  resourcesShared: number;
  groupsJoined: number;
  totalLikesReceived: number;
  currentStreak: number; // 连续登录天数
  longestStreak: number;
}

// 社区事件
export interface CommunityEvent {
  id: string;
  type: EventType;
  title: string;
  description: string;
  startTime: number;
  endTime: number;
  maxParticipants?: number;
  participants: string[];
  rewards: EventReward[];
  status: EventStatus;
}

// 事件类型
export type EventType = 'competition' | 'workshop' | 'challenge' | 'meetup';

// 事件状态
export type EventStatus = 'upcoming' | 'registration' | 'ongoing' | 'ended';

// 事件奖励
export interface EventReward {
  rank?: number; // 为空表示参与奖
  points: number;
  badge?: string;
  description: string;
}

// 举报
export interface Report {
  id: string;
  reporterId: string;
  targetType: ReportTargetType;
  targetId: string;
  reason: ReportReason;
  description: string;
  status: ReportStatus;
  createdAt: number;
  handledBy?: string;
  handledAt?: number;
  result?: ReportResult;
}

// 举报目标类型
export type ReportTargetType = 'topic' | 'reply' | 'question' | 'answer' | 'resource' | 'user';

// 举报原因
export type ReportReason = 
  | 'spam' 
  | 'inappropriate' 
  | 'harassment' 
  | 'copyright' 
  | 'misinformation' 
  | 'other';

// 举报状态
export type ReportStatus = 'pending' | 'investigating' | 'resolved';

// 举报结果
export type ReportResult = 'dismissed' | 'warning' | 'removed' | 'banned';

// 社区通知
export interface CommunityNotification {
  id: string;
  userId: string;
  type: NotificationType;
  title: string;
  content: string;
  relatedId?: string;
  isRead: boolean;
  createdAt: number;
}

// 通知类型
export type NotificationType = 
  | 'reply' 
  | 'like' 
  | 'mention' 
  | 'follow' 
  | 'system' 
  | 'achievement' 
  | 'group_invite'
  | 'answer_accepted'
  | 'level_up';

// 社区状态存储
export interface CommunityState {
  currentUser: CommunityUser | null;
  notifications: CommunityNotification[];
  unreadNotifications: number;
  joinedGroups: StudyGroup[];
  followedTopics: string[];
  draftTopics: Partial<DiscussionTopic>[];
  draftQuestions: Partial<Question>[];
}
