// ==================== 协作服务 - WebSocket连接管理 ====================

import { io, Socket } from 'socket.io-client';
import * as Y from 'yjs';
import { WebsocketProvider } from 'y-websocket';
import {
  ConnectionState,
  CollaborationRoom,
  UserPresence,
  CursorPosition,
  TextSelection,
  ChatMessage,
  Comment,
  DocumentVersion,
  ProgressUpdate,
  SharedLearningPath,
  TeamChallenge,
  CollaborationEvents,
  RoomType,
  RoomSettings,
  UserStatus,
} from '@types/collaboration';

// WebSocket 配置
const WS_CONFIG = {
  URL: import.meta.env.VITE_WS_URL || 'ws://localhost:3001',
  RECONNECTION_ATTEMPTS: 5,
  RECONNECTION_DELAY: 1000,
  RECONNECTION_DELAY_MAX: 5000,
  HEARTBEAT_INTERVAL: 30000,
  TIMEOUT: 10000,
};

// 颜色池用于分配用户颜色
const USER_COLORS = [
  '#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4', '#FFEAA7',
  '#DDA0DD', '#98D8C8', '#F7DC6F', '#BB8FCE', '#85C1E9',
];

// 协作服务类
class CollaborationService {
  private socket: Socket | null = null;
  private yDoc: Y.Doc | null = null;
  private yProvider: WebsocketProvider | null = null;
  private heartbeatTimer: NodeJS.Timeout | null = null;
  private reconnectionAttempts = 0;
  private eventListeners: Map<keyof CollaborationEvents, Set<Function>> = new Map();
  private currentRoom: CollaborationRoom | null = null;
  private currentUser: UserPresence | null = null;
  private connectionState: ConnectionState = 'disconnected';
  private typingTimers: Map<string, NodeJS.Timeout> = new Map();

  // ========== 连接管理 ==========

  /**
   * 初始化Socket.io连接
   */
  connect(userId: string, userName: string, avatar?: string): Promise<void> {
    return new Promise((resolve, reject) => {
      if (this.socket?.connected) {
        resolve();
        return;
      }

      this.setConnectionState('connecting');

      // 创建Socket.io客户端
      this.socket = io(WS_CONFIG.URL, {
        transports: ['websocket', 'polling'],
        reconnection: true,
        reconnectionAttempts: WS_CONFIG.RECONNECTION_ATTEMPTS,
        reconnectionDelay: WS_CONFIG.RECONNECTION_DELAY,
        reconnectionDelayMax: WS_CONFIG.RECONNECTION_DELAY_MAX,
        timeout: WS_CONFIG.TIMEOUT,
        auth: {
          token: localStorage.getItem('auth_token'),
          userId,
        },
      });

      // 设置用户presence信息
      this.currentUser = {
        id: userId,
        name: userName,
        avatar,
        color: this.assignUserColor(userId),
        status: 'online',
        lastSeen: Date.now(),
      };

      // 绑定事件处理
      this.bindSocketEvents(resolve, reject);
    });
  }

  /**
   * 断开连接
   */
  disconnect(): void {
    this.stopHeartbeat();
    this.leaveRoom();
    
    if (this.yProvider) {
      this.yProvider.destroy();
      this.yProvider = null;
    }
    
    if (this.yDoc) {
      this.yDoc.destroy();
      this.yDoc = null;
    }

    if (this.socket) {
      this.socket.disconnect();
      this.socket = null;
    }

    this.setConnectionState('disconnected');
    this.reconnectionAttempts = 0;
  }

  /**
   * 重新连接
   */
  reconnect(): Promise<void> {
    if (!this.currentUser) {
      return Promise.reject(new Error('No current user, cannot reconnect'));
    }
    
    this.disconnect();
    return this.connect(
      this.currentUser.id,
      this.currentUser.name,
      this.currentUser.avatar
    );
  }

  // ========== 房间管理 ==========

  /**
   * 创建协作房间
   */
  async createRoom(
    name: string,
    type: RoomType,
    documentId: string,
    settings?: Partial<RoomSettings>
  ): Promise<CollaborationRoom> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'room:create',
        { name, type, documentId, settings },
        (response: { success: boolean; room?: CollaborationRoom; error?: string }) => {
          if (response.success && response.room) {
            resolve(response.room);
          } else {
            reject(new Error(response.error || 'Failed to create room'));
          }
        }
      );
    });
  }

  /**
   * 加入协作房间
   */
  async joinRoom(roomId: string): Promise<CollaborationRoom> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'room:join',
        { roomId, user: this.currentUser },
        (response: { success: boolean; room?: CollaborationRoom; error?: string }) => {
          if (response.success && response.room) {
            this.currentRoom = response.room;
            this.initYjsProvider(roomId);
            this.startHeartbeat();
            this.emit('room:joined', response.room);
            resolve(response.room);
          } else {
            reject(new Error(response.error || 'Failed to join room'));
          }
        }
      );
    });
  }

  /**
   * 离开协作房间
   */
  leaveRoom(): void {
    if (this.currentRoom && this.socket?.connected) {
      this.socket.emit('room:leave', { roomId: this.currentRoom.id });
      this.emit('room:left', this.currentRoom.id);
    }
    
    this.currentRoom = null;
    this.stopHeartbeat();
    
    if (this.yProvider) {
      this.yProvider.destroy();
      this.yProvider = null;
    }
  }

  /**
   * 获取房间列表
   */
  async getRooms(type?: RoomType): Promise<CollaborationRoom[]> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'room:list',
        { type },
        (response: { success: boolean; rooms?: CollaborationRoom[]; error?: string }) => {
          if (response.success) {
            resolve(response.rooms || []);
          } else {
            reject(new Error(response.error || 'Failed to get rooms'));
          }
        }
      );
    });
  }

  // ========== Yjs 协同编辑 ==========

  /**
   * 初始化Yjs文档和Provider
   */
  private initYjsProvider(roomId: string): void {
    // 销毁旧的provider
    if (this.yProvider) {
      this.yProvider.destroy();
    }
    if (this.yDoc) {
      this.yDoc.destroy();
    }

    // 创建新的Yjs文档
    this.yDoc = new Y.Doc();

    // 创建WebSocket provider
    const wsUrl = WS_CONFIG.URL.replace(/^http/, 'ws');
    this.yProvider = new WebsocketProvider(
      wsUrl,
      roomId,
      this.yDoc,
      { connect: true }
    );

    // 设置awareness（用户awareness信息）
    if (this.currentUser) {
      this.yProvider.awareness.setLocalStateField('user', this.currentUser);
    }

    // 监听同步状态
    this.yProvider.on('status', (event: { status: string }) => {
      console.log('Yjs provider status:', event.status);
    });
  }

  /**
   * 获取Yjs文档
   */
  getYDoc(): Y.Doc | null {
    return this.yDoc;
  }

  /**
   * 获取Yjs Provider
   */
  getYProvider(): WebsocketProvider | null {
    return this.yProvider;
  }

  /**
   * 获取共享文本类型
   */
  getSharedText(name: string = 'content'): Y.Text | null {
    if (!this.yDoc) return null;
    return this.yDoc.getText(name);
  }

  /**
   * 获取共享Map
   */
  getSharedMap<T>(name: string): Y.Map<T> | null {
    if (!this.yDoc) return null;
    return this.yDoc.getMap<T>(name);
  }

  /**
   * 获取共享Array
   */
  getSharedArray<T>(name: string): Y.Array<T> | null {
    if (!this.yDoc) return null;
    return this.yDoc.getArray<T>(name);
  }

  // ========== 光标与选择同步 ==========

  /**
   * 更新光标位置
   */
  updateCursor(cursor: CursorPosition): void {
    if (!this.socket?.connected || !this.currentRoom) return;

    this.socket.emit('cursor:update', {
      roomId: this.currentRoom.id,
      cursor,
    });

    // 更新本地awareness
    if (this.yProvider) {
      this.yProvider.awareness.setLocalStateField('cursor', cursor);
    }
  }

  /**
   * 更新文本选择
   */
  updateSelection(selection: TextSelection): void {
    if (!this.socket?.connected || !this.currentRoom) return;

    this.socket.emit('selection:update', {
      roomId: this.currentRoom.id,
      selection,
    });

    // 更新本地awareness
    if (this.yProvider) {
      this.yProvider.awareness.setLocalStateField('selection', selection);
    }
  }

  // ========== 聊天功能 ==========

  /**
   * 发送聊天消息
   */
  sendMessage(content: string, replyTo?: string): Promise<ChatMessage> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected || !this.currentRoom) {
        reject(new Error('Not connected or not in a room'));
        return;
      }

      const message = {
        roomId: this.currentRoom.id,
        content,
        replyTo,
        timestamp: Date.now(),
      };

      this.socket.emit(
        'chat:message',
        message,
        (response: { success: boolean; message?: ChatMessage; error?: string }) => {
          if (response.success && response.message) {
            resolve(response.message);
          } else {
            reject(new Error(response.error || 'Failed to send message'));
          }
        }
      );
    });
  }

  /**
   * 发送正在输入状态
   */
  sendTypingStatus(isTyping: boolean): void {
    if (!this.socket?.connected || !this.currentRoom || !this.currentUser) return;

    // 防抖处理
    const key = `typing-${this.currentUser.id}`;
    const existingTimer = this.typingTimers.get(key);
    if (existingTimer) {
      clearTimeout(existingTimer);
    }

    if (isTyping) {
      // 3秒后自动停止输入状态
      const timer = setTimeout(() => {
        this.socket?.emit('chat:typing', {
          roomId: this.currentRoom?.id,
          isTyping: false,
        });
        this.typingTimers.delete(key);
      }, 3000);
      this.typingTimers.set(key, timer);
    }

    this.socket.emit('chat:typing', {
      roomId: this.currentRoom.id,
      isTyping,
    });
  }

  /**
   * 添加消息反应
   */
  addReaction(messageId: string, emoji: string): void {
    if (!this.socket?.connected || !this.currentRoom) return;

    this.socket.emit('chat:reaction', {
      roomId: this.currentRoom.id,
      messageId,
      emoji,
    });
  }

  /**
   * 获取聊天记录
   */
  async getMessages(limit: number = 50, before?: number): Promise<ChatMessage[]> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected || !this.currentRoom) {
        reject(new Error('Not connected or not in a room'));
        return;
      }

      this.socket.emit(
        'chat:history',
        { roomId: this.currentRoom.id, limit, before },
        (response: { success: boolean; messages?: ChatMessage[]; error?: string }) => {
          if (response.success) {
            resolve(response.messages || []);
          } else {
            reject(new Error(response.error || 'Failed to get messages'));
          }
        }
      );
    });
  }

  // ========== 评论/批注功能 ==========

  /**
   * 创建评论
   */
  async createComment(
    content: string,
    position: { start: number; end: number; line?: number }
  ): Promise<Comment> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected || !this.currentRoom) {
        reject(new Error('Not connected or not in a room'));
        return;
      }

      this.socket.emit(
        'comment:create',
        {
          roomId: this.currentRoom.id,
          documentId: this.currentRoom.documentId,
          content,
          position,
        },
        (response: { success: boolean; comment?: Comment; error?: string }) => {
          if (response.success && response.comment) {
            resolve(response.comment);
          } else {
            reject(new Error(response.error || 'Failed to create comment'));
          }
        }
      );
    });
  }

  /**
   * 回复评论
   */
  async replyToComment(commentId: string, content: string): Promise<void> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'comment:reply',
        { commentId, content },
        (response: { success: boolean; error?: string }) => {
          if (response.success) {
            resolve();
          } else {
            reject(new Error(response.error || 'Failed to reply'));
          }
        }
      );
    });
  }

  /**
   * 解决评论
   */
  resolveComment(commentId: string): void {
    if (!this.socket?.connected) return;

    this.socket.emit('comment:resolve', { commentId });
  }

  /**
   * 删除评论
   */
  deleteComment(commentId: string): void {
    if (!this.socket?.connected) return;

    this.socket.emit('comment:delete', { commentId });
  }

  /**
   * 获取评论列表
   */
  async getComments(documentId: string): Promise<Comment[]> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'comment:list',
        { documentId },
        (response: { success: boolean; comments?: Comment[]; error?: string }) => {
          if (response.success) {
            resolve(response.comments || []);
          } else {
            reject(new Error(response.error || 'Failed to get comments'));
          }
        }
      );
    });
  }

  // ========== 版本历史 ==========

  /**
   * 创建版本快照
   */
  async createVersion(comment?: string): Promise<DocumentVersion> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected || !this.currentRoom) {
        reject(new Error('Not connected or not in a room'));
        return;
      }

      // 获取当前文档内容
      const content = this.yDoc ? this.getDocumentContent() : null;

      this.socket.emit(
        'version:create',
        {
          roomId: this.currentRoom.id,
          documentId: this.currentRoom.documentId,
          content,
          comment,
        },
        (response: { success: boolean; version?: DocumentVersion; error?: string }) => {
          if (response.success && response.version) {
            resolve(response.version);
          } else {
            reject(new Error(response.error || 'Failed to create version'));
          }
        }
      );
    });
  }

  /**
   * 恢复到指定版本
   */
  async restoreVersion(versionId: string): Promise<void> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'version:restore',
        { versionId },
        (response: { success: boolean; error?: string }) => {
          if (response.success) {
            resolve();
          } else {
            reject(new Error(response.error || 'Failed to restore version'));
          }
        }
      );
    });
  }

  /**
   * 获取版本历史
   */
  async getVersions(documentId: string): Promise<DocumentVersion[]> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'version:list',
        { documentId },
        (response: { success: boolean; versions?: DocumentVersion[]; error?: string }) => {
          if (response.success) {
            resolve(response.versions || []);
          } else {
            reject(new Error(response.error || 'Failed to get versions'));
          }
        }
      );
    });
  }

  // ========== 共享学习路径 ==========

  /**
   * 创建共享学习路径
   */
  async createSharedPath(
    name: string,
    description: string,
    participants: string[]
  ): Promise<SharedLearningPath> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'path:create',
        { name, description, participants },
        (response: { success: boolean; path?: SharedLearningPath; error?: string }) => {
          if (response.success && response.path) {
            resolve(response.path);
          } else {
            reject(new Error(response.error || 'Failed to create path'));
          }
        }
      );
    });
  }

  /**
   * 更新学习进度
   */
  updateProgress(update: ProgressUpdate): void {
    if (!this.socket?.connected) return;

    this.socket.emit('path:progress', update);
  }

  /**
   * 获取共享学习路径
   */
  async getSharedPaths(): Promise<SharedLearningPath[]> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'path:list',
        {},
        (response: { success: boolean; paths?: SharedLearningPath[]; error?: string }) => {
          if (response.success) {
            resolve(response.paths || []);
          } else {
            reject(new Error(response.error || 'Failed to get paths'));
          }
        }
      );
    });
  }

  // ========== 组队挑战 ==========

  /**
   * 创建组队挑战
   */
  async createChallenge(challenge: Partial<TeamChallenge>): Promise<TeamChallenge> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'challenge:create',
        challenge,
        (response: { success: boolean; challenge?: TeamChallenge; error?: string }) => {
          if (response.success && response.challenge) {
            resolve(response.challenge);
          } else {
            reject(new Error(response.error || 'Failed to create challenge'));
          }
        }
      );
    });
  }

  /**
   * 加入挑战
   */
  async joinChallenge(challengeId: string, teamId?: string): Promise<TeamChallenge> {
    return new Promise((resolve, reject) => {
      if (!this.socket?.connected) {
        reject(new Error('Not connected'));
        return;
      }

      this.socket.emit(
        'challenge:join',
        { challengeId, teamId },
        (response: { success: boolean; challenge?: TeamChallenge; error?: string }) => {
          if (response.success && response.challenge) {
            resolve(response.challenge);
          } else {
            reject(new Error(response.error || 'Failed to join challenge'));
          }
        }
      );
    });
  }

  /**
   * 更新挑战进度
   */
  updateChallengeProgress(challengeId: string, teamId: string, progress: number): void {
    if (!this.socket?.connected) return;

    this.socket.emit('challenge:progress', { challengeId, teamId, progress });
  }

  /**
   * 更新挑战分数
   */
  updateChallengeScore(challengeId: string, teamId: string, points: number): void {
    if (!this.socket?.connected) return;

    this.socket.emit('challenge:score', { challengeId, teamId, points });
  }

  // ========== 事件监听 ==========

  /**
   * 监听事件
   */
  on<K extends keyof CollaborationEvents>(
    event: K,
    listener: CollaborationEvents[K]
  ): () => void {
    if (!this.eventListeners.has(event)) {
      this.eventListeners.set(event, new Set());
    }
    this.eventListeners.get(event)!.add(listener as Function);

    // 返回取消订阅函数
    return () => {
      this.eventListeners.get(event)?.delete(listener as Function);
    };
  }

  /**
   * 取消监听
   */
  off<K extends keyof CollaborationEvents>(event: K, listener: CollaborationEvents[K]): void {
    this.eventListeners.get(event)?.delete(listener as Function);
  }

  /**
   * 触发事件
   */
  private emit<K extends keyof CollaborationEvents>(
    event: K,
    ...args: Parameters<CollaborationEvents[K]>
  ): void {
    this.eventListeners.get(event)?.forEach((listener) => {
      try {
        listener(...args);
      } catch (error) {
        console.error(`Error in event listener for ${event}:`, error);
      }
    });
  }

  // ========== 状态获取 ==========

  getConnectionState(): ConnectionState {
    return this.connectionState;
  }

  getCurrentUser(): UserPresence | null {
    return this.currentUser;
  }

  getCurrentRoom(): CollaborationRoom | null {
    return this.currentRoom;
  }

  isConnected(): boolean {
    return this.socket?.connected ?? false;
  }

  // ========== 私有方法 ==========

  private setConnectionState(state: ConnectionState): void {
    this.connectionState = state;
  }

  private bindSocketEvents(resolve: () => void, reject: (error: Error) => void): void {
    if (!this.socket) return;

    // 连接成功
    this.socket.on('connect', () => {
      console.log('Socket connected');
      this.setConnectionState('connected');
      this.reconnectionAttempts = 0;
      resolve();
    });

    // 连接断开
    this.socket.on('disconnect', (reason: string) => {
      console.log('Socket disconnected:', reason);
      this.setConnectionState('disconnected');
      this.emit('disconnect', reason);
    });

    // 连接错误
    this.socket.on('connect_error', (error: Error) => {
      console.error('Socket connection error:', error);
      this.setConnectionState('error');
      this.emit('connect_error', error);
      reject(error);
    });

    // 重连中
    this.socket.io.on('reconnect_attempt', (attemptNumber: number) => {
      console.log('Reconnection attempt:', attemptNumber);
      this.reconnectionAttempts = attemptNumber;
      this.setConnectionState('reconnecting');
      this.emit('reconnect_attempt', attemptNumber);
    });

    // 重连成功
    this.socket.io.on('reconnect', (attemptNumber: number) => {
      console.log('Reconnected after', attemptNumber, 'attempts');
      this.setConnectionState('connected');
      this.emit('reconnect', attemptNumber);
    });

    // 重连失败
    this.socket.io.on('reconnect_failed', () => {
      console.error('Reconnection failed');
      this.setConnectionState('error');
      this.emit('reconnect_failed');
    });

    // 绑定协作相关事件
    this.bindCollaborationEvents();
  }

  private bindCollaborationEvents(): void {
    if (!this.socket) return;

    // 房间事件
    this.socket.on('room:user-joined', (user: UserPresence) => {
      this.emit('room:user-joined', user);
    });

    this.socket.on('room:user-left', (userId: string) => {
      this.emit('room:user-left', userId);
    });

    this.socket.on('room:user-updated', (user: UserPresence) => {
      this.emit('room:user-updated', user);
    });

    // 光标/选择事件
    this.socket.on('cursor:updated', (data: { userId: string; cursor: CursorPosition }) => {
      this.emit('cursor:updated', data.userId, data.cursor);
    });

    this.socket.on('selection:updated', (data: { userId: string; selection: TextSelection }) => {
      this.emit('selection:updated', data.userId, data.selection);
    });

    // 聊天事件
    this.socket.on('chat:message', (message: ChatMessage) => {
      this.emit('chat:message', message);
    });

    this.socket.on('chat:reaction', (data: { messageId: string; reaction: unknown }) => {
      this.emit('chat:reaction', data.messageId, data.reaction as { emoji: string; users: string[] });
    });

    this.socket.on('chat:typing', (data: { userId: string; isTyping: boolean }) => {
      this.emit('chat:typing', data.userId, data.isTyping);
    });

    // 评论事件
    this.socket.on('comment:created', (comment: Comment) => {
      this.emit('comment:created', comment);
    });

    this.socket.on('comment:updated', (comment: Comment) => {
      this.emit('comment:updated', comment);
    });

    this.socket.on('comment:deleted', (commentId: string) => {
      this.emit('comment:deleted', commentId);
    });

    this.socket.on('comment:resolved', (commentId: string) => {
      this.emit('comment:resolved', commentId);
    });

    // 版本事件
    this.socket.on('version:created', (version: DocumentVersion) => {
      this.emit('version:created', version);
    });

    this.socket.on('version:restored', (versionId: string) => {
      this.emit('version:restored', versionId);
    });

    // 学习路径事件
    this.socket.on('path:progress', (update: ProgressUpdate) => {
      this.emit('path:progress', update);
    });

    this.socket.on('path:node-completed', (data: { userId: string; nodeId: string }) => {
      this.emit('path:node-completed', data.userId, data.nodeId);
    });

    // 挑战事件
    this.socket.on('challenge:started', (challenge: TeamChallenge) => {
      this.emit('challenge:started', challenge);
    });

    this.socket.on('challenge:progress', (data: { challengeId: string; teamId: string; progress: number }) => {
      this.emit('challenge:progress', data.challengeId, data.teamId, data.progress);
    });

    this.socket.on('challenge:completed', (data: { challengeId: string; winnerTeamId: string }) => {
      this.emit('challenge:completed', data.challengeId, data.winnerTeamId);
    });

    this.socket.on('challenge:score-update', (data: { challengeId: string; teamId: string; score: number }) => {
      this.emit('challenge:score-update', data.challengeId, data.teamId, data.score);
    });
  }

  private startHeartbeat(): void {
    this.stopHeartbeat();
    this.heartbeatTimer = setInterval(() => {
      if (this.socket?.connected && this.currentRoom) {
        this.socket.emit('heartbeat', {
          roomId: this.currentRoom.id,
          timestamp: Date.now(),
        });
      }
    }, WS_CONFIG.HEARTBEAT_INTERVAL);
  }

  private stopHeartbeat(): void {
    if (this.heartbeatTimer) {
      clearInterval(this.heartbeatTimer);
      this.heartbeatTimer = null;
    }
  }

  private assignUserColor(userId: string): string {
    let hash = 0;
    for (let i = 0; i < userId.length; i++) {
      hash = userId.charCodeAt(i) + ((hash << 5) - hash);
    }
    const index = Math.abs(hash) % USER_COLORS.length;
    return USER_COLORS[index];
  }

  private getDocumentContent(): unknown {
    // 获取Yjs文档的当前状态
    if (!this.yDoc) return null;
    
    return {
      content: this.yDoc.getText('content').toString(),
      meta: this.yDoc.getMap('meta').toJSON(),
    };
  }
}

// 导出单例实例
export const collaborationService = new CollaborationService();

// 导出钩子函数用于React组件
export function useCollaborationService(): CollaborationService {
  return collaborationService;
}

export default collaborationService;
