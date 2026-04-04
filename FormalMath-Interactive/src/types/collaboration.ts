// ==================== 协作功能类型定义 ====================

// 用户在线状态
export type UserStatus = 'online' | 'away' | 'busy' | 'offline';

// 协作角色
export type CollaboratorRole = 'owner' | 'editor' | 'viewer' | 'commenter';

// 用户 presence 信息
export interface UserPresence {
  id: string;
  name: string;
  avatar?: string;
  color: string;
  status: UserStatus;
  cursor?: CursorPosition;
  selection?: TextSelection;
  lastSeen: number;
  currentRoom?: string;
}

// 光标位置
export interface CursorPosition {
  x: number;
  y: number;
  line?: number;
  column?: number;
  documentId: string;
}

// 文本选择
export interface TextSelection {
  start: number;
  end: number;
  documentId: string;
}

// 协作房间
export interface CollaborationRoom {
  id: string;
  name: string;
  type: RoomType;
  documentId: string;
  createdBy: string;
  createdAt: number;
  participants: UserPresence[];
  settings: RoomSettings;
}

// 房间类型
export type RoomType = 'document' | 'study-group' | 'challenge' | 'discussion';

// 房间设置
export interface RoomSettings {
  allowEdit: boolean;
  allowChat: boolean;
  allowComments: boolean;
  isPublic: boolean;
  maxParticipants?: number;
}

// 聊天消息
export interface ChatMessage {
  id: string;
  roomId: string;
  userId: string;
  userName: string;
  userAvatar?: string;
  content: string;
  type: MessageType;
  timestamp: number;
  replyTo?: string;
  reactions?: MessageReaction[];
}

// 消息类型
export type MessageType = 'text' | 'system' | 'emoji' | 'file' | 'voice';

// 消息反应
export interface MessageReaction {
  emoji: string;
  users: string[];
}

// 文档版本
export interface DocumentVersion {
  id: string;
  documentId: string;
  version: number;
  content: unknown;
  createdBy: string;
  createdAt: number;
  comment?: string;
  changes: VersionChange[];
}

// 版本变更
export interface VersionChange {
  type: 'insert' | 'delete' | 'update' | 'format';
  position: number;
  length: number;
  content?: string;
  author: string;
}

// 评论/批注
export interface Comment {
  id: string;
  documentId: string;
  userId: string;
  userName: string;
  userAvatar?: string;
  content: string;
  position: CommentPosition;
  timestamp: number;
  resolved: boolean;
  replies: CommentReply[];
}

// 评论位置
export interface CommentPosition {
  start: number;
  end: number;
  line?: number;
}

// 评论回复
export interface CommentReply {
  id: string;
  userId: string;
  userName: string;
  content: string;
  timestamp: number;
}

// 共享学习路径
export interface SharedLearningPath {
  id: string;
  name: string;
  description?: string;
  ownerId: string;
  participants: PathParticipant[];
  nodes: PathNode[];
  progress: Record<string, number>; // userId -> progress percentage
  createdAt: number;
  updatedAt: number;
}

// 路径参与者
export interface PathParticipant {
  userId: string;
  role: 'owner' | 'member';
  joinedAt: number;
  completedNodes: string[];
}

// 路径节点
export interface PathNode {
  id: string;
  conceptId: string;
  order: number;
  estimatedTime: number; // minutes
  dependencies: string[];
}

// 组队挑战
export interface TeamChallenge {
  id: string;
  name: string;
  description: string;
  type: ChallengeType;
  teams: Team[];
  problems: ChallengeProblem[];
  startTime: number;
  endTime?: number;
  status: ChallengeStatus;
  settings: ChallengeSettings;
}

// 挑战类型
export type ChallengeType = 'speed' | 'accuracy' | 'collaboration' | 'creativity';

// 挑战状态
export type ChallengeStatus = 'waiting' | 'in-progress' | 'completed' | 'cancelled';

// 团队
export interface Team {
  id: string;
  name: string;
  members: TeamMember[];
  score: number;
  progress: number;
  currentProblem?: number;
}

// 团队成员
export interface TeamMember {
  userId: string;
  userName: string;
  avatar?: string;
  joinedAt: number;
  contributions: number;
}

// 挑战问题
export interface ChallengeProblem {
  id: string;
  conceptId: string;
  difficulty: number;
  points: number;
  timeLimit?: number; // seconds
}

// 挑战设置
export interface ChallengeSettings {
  maxTeamSize: number;
  minTeamSize: number;
  allowRandomTeams: boolean;
  timeLimit?: number; // total seconds
}

// 实时进度更新
export interface ProgressUpdate {
  userId: string;
  conceptId: string;
  type: 'started' | 'completed' | 'struggling' | 'help-needed';
  timestamp: number;
  details?: string;
}

// 连接状态
export type ConnectionState = 'connecting' | 'connected' | 'disconnected' | 'reconnecting' | 'error';

// WebSocket 事件类型
export interface CollaborationEvents {
  // 连接事件
  'connect': () => void;
  'disconnect': (reason: string) => void;
  'connect_error': (error: Error) => void;
  'reconnect': (attemptNumber: number) => void;
  'reconnect_attempt': (attemptNumber: number) => void;
  'reconnect_error': (error: Error) => void;
  'reconnect_failed': () => void;

  // 房间事件
  'room:joined': (room: CollaborationRoom) => void;
  'room:left': (roomId: string) => void;
  'room:user-joined': (user: UserPresence) => void;
  'room:user-left': (userId: string) => void;
  'room:user-updated': (user: UserPresence) => void;
  'room:updated': (room: CollaborationRoom) => void;

  // 光标/选择事件
  'cursor:updated': (userId: string, cursor: CursorPosition) => void;
  'selection:updated': (userId: string, selection: TextSelection) => void;

  // 聊天事件
  'chat:message': (message: ChatMessage) => void;
  'chat:reaction': (messageId: string, reaction: MessageReaction) => void;
  'chat:typing': (userId: string, isTyping: boolean) => void;

  // 评论事件
  'comment:created': (comment: Comment) => void;
  'comment:updated': (comment: Comment) => void;
  'comment:deleted': (commentId: string) => void;
  'comment:resolved': (commentId: string) => void;

  // 版本事件
  'version:created': (version: DocumentVersion) => void;
  'version:restored': (versionId: string) => void;

  // 学习路径事件
  'path:progress': (update: ProgressUpdate) => void;
  'path:node-completed': (userId: string, nodeId: string) => void;
  'path:updated': (path: SharedLearningPath) => void;

  // 挑战事件
  'challenge:started': (challenge: TeamChallenge) => void;
  'challenge:progress': (challengeId: string, teamId: string, progress: number) => void;
  'challenge:completed': (challengeId: string, winnerTeamId: string) => void;
  'challenge:score-update': (challengeId: string, teamId: string, score: number) => void;
}

// 协作状态存储
export interface CollaborationState {
  connectionState: ConnectionState;
  currentUser: UserPresence | null;
  currentRoom: CollaborationRoom | null;
  onlineUsers: UserPresence[];
  messages: ChatMessage[];
  comments: Comment[];
  versions: DocumentVersion[];
  unreadCount: number;
  typingUsers: string[];
}

// Yjs 文档同步状态
export interface YjsSyncState {
  synced: boolean;
  awareness: unknown;
  updateCount: number;
  lastUpdate: number;
}
