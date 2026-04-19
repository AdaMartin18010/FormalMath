---
title: FormalMath-Interactive 实时协作编辑功能
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath-Interactive 实时协作编辑功能

## 功能概述

本模块实现了 FormalMath-Interactive 的实时协作编辑功能，支持多人同时编辑文档、实时聊天、评论批注、版本历史、共享学习路径和组队挑战。

## 技术栈

- **React 18 + TypeScript**: 前端框架
- **Socket.io-client**: WebSocket 连接管理
- **Yjs**: CRDT（无冲突复制数据类型）协同编辑
- **y-websocket**: Yjs WebSocket 提供者

## 目录结构

```
src/components/Collaboration/
├── CollaborativeEditor.tsx    # 协同编辑器组件
├── CollaborativeEditor.css    # 编辑器样式
├── UserPresence.tsx           # 在线用户列表和光标位置
├── UserPresence.css           # 用户presence样式
├── ChatPanel.tsx              # 实时聊天面板
├── ChatPanel.css              # 聊天面板样式
├── VersionHistory.tsx         # 版本历史组件
├── VersionHistory.css         # 版本历史样式
├── index.ts                   # 模块导出
└── README.md                  # 本文档
```

## 核心服务

```
src/services/
├── collaborationService.ts    # 协作服务（WebSocket + Yjs）
├── api/
│   └── client.ts              # HTTP API 客户端
└── index.ts                   # 服务导出
```

## 自定义 Hooks

```
src/hooks/
└── useCollaboration.ts        # 协作功能 Hooks
```

## 快速开始

### 1. 安装依赖

```bash
npm install socket.io-client yjs y-websocket y-protocols lib0
```

### 2. 环境配置

在项目根目录创建 `.env` 文件：

```env
# WebSocket 服务器地址
VITE_WS_URL=ws://localhost:3001

# API 基础地址
VITE_API_BASE_URL=/api
```

### 3. 后端配合

详见 `src/services/README-Collaboration.md`

## 使用示例

### 基础协同编辑器

```tsx
import { CollaborativeEditor } from '@components/Collaboration';

function DocumentPage({ documentId, roomId, userId, userName }) {
  return (
    <CollaborativeEditor
      documentId={documentId}
      roomId={roomId}
      userId={userId}
      userName={userName}
      userAvatar="https://example.com/avatar.jpg[需更新]"
      initialContent="# 欢迎使用协同编辑"
      showChat={true}
      showPresence={true}
      onContentChange={(content) => console.log('Content:', content)}
    />
  );
}
```

### 使用 Hooks

```tsx
import { useCollaborativeEditor, useChatMessages } from '@hooks';

function MyComponent() {
  // 协同编辑器 Hook
  const {
    isReady,
    isSynced,
    onlineUsers,
    content,
    updateContent,
    updateCursor
  } = useCollaborativeEditor(documentId, roomId, userId, userName);

  // 聊天消息 Hook
  const { messages, sendMessage, isTyping, sendTypingStatus } = useChatMessages(roomId);

  // 评论 Hook
  const { comments, createComment, resolveComment } = useComments(documentId);

  // 版本历史 Hook
  const { versions, createVersion, restoreVersion } = useVersionHistory(documentId);

  return (
    // JSX...
  );
}
```

### 独立使用聊天面板

```tsx
import { ChatPanel } from '@components/Collaboration';

function Sidebar() {
  return (
    <ChatPanel
      roomId="room-123"
      userId="user-456"
      userName="张三"
      userAvatar="https://example.com/avatar.jpg[需更新]"
      onClose={() => setShowChat(false)}
    />
  );
}
```

### 在线用户列表

```tsx
import { UserPresence, CompactUserPresence } from '@components/Collaboration';

function Header() {
  const onlineUsers = [
    { id: '1', name: '张三', color: '#FF6B6B', status: 'online', lastSeen: Date.now() },
    { id: '2', name: '李四', color: '#4ECDC4', status: 'away', lastSeen: Date.now() - 300000 },
  ];

  return (
    <>
      {/* 完整版本 */}
      <UserPresence
        users={onlineUsers}
        currentUserId="1"
        showAvatars={true}
        showStatus={true}
        maxDisplay={5}
      />

      {/* 紧凑版本 */}
      <CompactUserPresence
        users={onlineUsers}
        currentUserId="1"
        maxDisplay={3}
      />
    </>
  );
}
```

### 版本历史

```tsx
import { VersionHistory } from '@components/Collaboration';

function HistoryPanel() {
  return (
    <VersionHistory
      documentId="doc-123"
      onVersionSelect={(version) => console.log('Selected:', version)}
      onVersionRestore={(versionId) => console.log('Restored:', versionId)}
      onCompare={(v1, v2) => console.log('Compare:', v1, v2)}
    />
  );
}
```

## 功能特性

### 1. WebSocket 连接管理

- ✅ 自动连接/断线重连
- ✅ 心跳检测
- ✅ 连接状态管理（connecting/connected/disconnected/reconnecting/error）
- ✅ 房间管理（创建/加入/离开）
- ✅ 最多 5 次重连尝试

### 2. 协同编辑

- ✅ 基于 Yjs 的 CRDT 协同编辑
- ✅ 无冲突的实时同步
- ✅ 离线编辑支持
- ✅ 多人同时编辑同一文档

### 3. 用户 Presence

- ✅ 在线用户列表
- ✅ 用户状态（在线/离开/忙碌/离线）
- ✅ 实时光标位置同步
- ✅ 文本选择高亮同步
- ✅ 用户头像和颜色标识

### 4. 实时聊天

- ✅ 发送/接收文本消息
- ✅ 消息回复
- ✅ 表情反应
- ✅ 输入状态提示
- ✅ 消息历史分页加载
- ✅ URL 链接自动识别

### 5. 评论/批注

- ✅ 创建文本评论
- ✅ 评论回复
- ✅ 解决评论
- ✅ 删除评论
- ✅ 评论位置标记

### 6. 版本历史

- ✅ 创建版本快照
- ✅ 查看版本列表（列表/时间线视图）
- ✅ 版本预览
- ✅ 恢复到指定版本
- ✅ 版本对比

### 7. 协作学习

- ✅ 共享学习路径
- ✅ 实时进度同步
- ✅ 组队挑战模式
- ✅ 团队分数更新

## API 参考

### CollaborationService

```typescript
class CollaborationService {
  // 连接管理
  connect(userId: string, userName: string, avatar?: string): Promise<void>
  disconnect(): void
  reconnect(): Promise<void>
  
  // 房间管理
  createRoom(name, type, documentId, settings?): Promise<CollaborationRoom>
  joinRoom(roomId: string): Promise<CollaborationRoom>
  leaveRoom(): void
  getRooms(type?): Promise<CollaborationRoom[]>
  
  // Yjs 操作
  getYDoc(): Y.Doc | null
  getSharedText(name?): Y.Text | null
  getSharedMap<T>(name): Y.Map<T> | null
  getSharedArray<T>(name): Y.Array<T> | null
  
  // 光标/选择
  updateCursor(cursor: CursorPosition): void
  updateSelection(selection: TextSelection): void
  
  // 聊天
  sendMessage(content: string, replyTo?: string): Promise<ChatMessage>
  sendTypingStatus(isTyping: boolean): void
  addReaction(messageId: string, emoji: string): void
  getMessages(limit?, before?): Promise<ChatMessage[]>
  
  // 评论
  createComment(content, position): Promise<Comment>
  replyToComment(commentId, content): Promise<void>
  resolveComment(commentId: string): void
  deleteComment(commentId: string): void
  getComments(documentId: string): Promise<Comment[]>
  
  // 版本
  createVersion(comment?): Promise<DocumentVersion>
  restoreVersion(versionId: string): Promise<void>
  getVersions(documentId: string): Promise<DocumentVersion[]>
  
  // 学习路径
  createSharedPath(name, description, participants): Promise<SharedLearningPath>
  updateProgress(update: ProgressUpdate): void
  getSharedPaths(): Promise<SharedLearningPath[]>
  
  // 挑战
  createChallenge(challenge): Promise<TeamChallenge>
  joinChallenge(challengeId, teamId?): Promise<TeamChallenge>
  updateChallengeProgress(challengeId, teamId, progress): void
  updateChallengeScore(challengeId, teamId, points): void
  
  // 事件监听
  on<K extends keyof CollaborationEvents>(event: K, listener: CollaborationEvents[K]): () => void
  off<K extends keyof CollaborationEvents>(event: K, listener: CollaborationEvents[K]): void
  
  // 状态获取
  getConnectionState(): ConnectionState
  getCurrentUser(): UserPresence | null
  getCurrentRoom(): CollaborationRoom | null
  isConnected(): boolean
}
```

## 事件类型

```typescript
interface CollaborationEvents {
  // 连接事件
  'connect': () => void
  'disconnect': (reason: string) => void
  'connect_error': (error: Error) => void
  'reconnect': (attemptNumber: number) => void
  'reconnect_attempt': (attemptNumber: number) => void
  'reconnect_error': (error: Error) => void
  'reconnect_failed': () => void

  // 房间事件
  'room:joined': (room: CollaborationRoom) => void
  'room:left': (roomId: string) => void
  'room:user-joined': (user: UserPresence) => void
  'room:user-left': (userId: string) => void
  'room:user-updated': (user: UserPresence) => void

  // 光标/选择
  'cursor:updated': (userId: string, cursor: CursorPosition) => void
  'selection:updated': (userId: string, selection: TextSelection) => void

  // 聊天
  'chat:message': (message: ChatMessage) => void
  'chat:reaction': (messageId: string, reaction: MessageReaction) => void
  'chat:typing': (userId: string, isTyping: boolean) => void

  // 评论
  'comment:created': (comment: Comment) => void
  'comment:updated': (comment: Comment) => void
  'comment:deleted': (commentId: string) => void
  'comment:resolved': (commentId: string) => void

  // 版本
  'version:created': (version: DocumentVersion) => void
  'version:restored': (versionId: string) => void

  // 学习路径
  'path:progress': (update: ProgressUpdate) => void
  'path:node-completed': (userId: string, nodeId: string) => void
  'path:updated': (path: SharedLearningPath) => void

  // 挑战
  'challenge:started': (challenge: TeamChallenge) => void
  'challenge:progress': (challengeId: string, teamId: string, progress: number) => void
  'challenge:completed': (challengeId: string, winnerTeamId: string) => void
  'challenge:score-update': (challengeId: string, teamId: string, score: number) => void
}
```

## 注意事项

1. **环境变量**: 确保设置正确的 `VITE_WS_URL` 环境变量
2. **认证**: WebSocket 连接会自动从 localStorage 获取 `auth_token`
3. **节流**: 光标位置更新已内置节流处理
4. **清理**: 组件卸载时会自动断开连接和清理资源
5. **重连**: 断线后会自动重连，最多尝试 5 次

## 浏览器兼容性

- Chrome/Edge 88+
- Firefox 85+
- Safari 14+
- 支持 WebSocket 的现代浏览器

## 待优化项

1. [ ] 添加更多单元测试
2. [ ] 优化大文档的性能
3. [ ] 支持图片/文件上传
4. [ ] 添加语音消息支持
5. [ ] 实现更精确的光标位置计算
