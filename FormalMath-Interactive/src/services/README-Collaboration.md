---
title: FormalMath-Interactive 协作功能 API 文档
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath-Interactive 协作功能 API 文档

## 概述

本文档描述了 FormalMath-Interactive 前端协作功能与后端的配合接口。协作功能基于 WebSocket (Socket.io) 和 Yjs (CRDT) 实现。

## 技术栈

- **Socket.io**: WebSocket 连接管理、实时消息传递
- **Yjs**: CRDT 协同编辑
- **y-websocket**: Yjs WebSocket 提供者

## 后端配合要求

### 1. WebSocket 服务端配置

```javascript
// 服务器端 Socket.io 配置示例
const io = require('socket.io')(server, {
  cors: {
    origin: process.env.CLIENT_URL || "",
    methods: ["GET", "POST"]
  },
  transports: ['websocket', 'polling']
});

// 命名空间
const collaborationNs = io.of('/collaboration');
```

### 2. 认证中间件

```javascript
collaborationNs.use(async (socket, next) => {
  try {
    const token = socket.handshake.auth.token;
    const decoded = jwt.verify(token, process.env.JWT_SECRET);
    socket.userId = decoded.userId;
    socket.userName = decoded.userName;
    next();
  } catch (err) {
    next(new Error('Authentication error'));
  }
});
```

### 3. 房间管理

#### 创建房间

```javascript
// 事件: 'room:create'
// 数据: { name, type, documentId, settings }
// 响应: { success: boolean, room?: CollaborationRoom, error?: string }

socket.on('room:create', async (data, callback) => {
  try {
    const room = await createRoom({
      ...data,
      createdBy: socket.userId,
      createdAt: Date.now()
    });
    
    // 初始化 Yjs 文档存储
    await initYjsDoc(room.id, data.documentId);
    
    callback({ success: true, room });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});
```

#### 加入房间

```javascript
// 事件: 'room:join'
// 数据: { roomId, user: UserPresence }
// 响应: { success: boolean, room?: CollaborationRoom, error?: string }

socket.on('room:join', async (data, callback) => {
  try {
    const room = await getRoom(data.roomId);
    if (!room) {
      return callback({ success: false, error: 'Room not found' });
    }

    // 加入 Socket.io 房间
    socket.join(data.roomId);
    
    // 更新用户 presence
    await addUserToRoom(data.roomId, {
      ...data.user,
      socketId: socket.id
    });

    // 通知房间内其他用户
    socket.to(data.roomId).emit('room:user-joined', data.user);

    // 获取当前房间状态
    const updatedRoom = await getRoom(data.roomId);
    callback({ success: true, room: updatedRoom });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});
```

#### 离开房间

```javascript
// 事件: 'room:leave'
// 数据: { roomId }

socket.on('room:leave', async (data) => {
  socket.leave(data.roomId);
  await removeUserFromRoom(data.roomId, socket.userId);
  socket.to(data.roomId).emit('room:user-left', socket.userId);
});
```

### 4. Yjs 文档同步

后端需要提供 Yjs WebSocket 端点：

```javascript
const { setupWSConnection } = require('y-websocket/bin/utils');

// Yjs WebSocket 服务器
const yjsServer = new WebSocket.Server({ noServer: true });

yjsServer.on('connection', (ws, req) => {
  // 解析 room 名称
  const roomName = req.url.slice(1).split('?')[0];
  
  setupWSConnection(ws, req, {
    docName: roomName,
    gc: true // 启用垃圾回收
  });
});
```

### 5. 聊天消息

```javascript
// 发送消息
// 事件: 'chat:message'
// 数据: { roomId, content, replyTo?, timestamp }
// 响应: { success: boolean, message?: ChatMessage, error?: string }

socket.on('chat:message', async (data, callback) => {
  try {
    const message = await saveMessage({
      id: generateId(),
      roomId: data.roomId,
      userId: socket.userId,
      userName: socket.userName,
      content: data.content,
      type: 'text',
      timestamp: data.timestamp,
      replyTo: data.replyTo
    });

    // 广播给房间内所有用户（包括发送者）
    collaborationNs.to(data.roomId).emit('chat:message', message);
    
    callback({ success: true, message });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 获取历史消息
// 事件: 'chat:history'
// 数据: { roomId, limit?, before? }
// 响应: { success: boolean, messages?: ChatMessage[], error?: string }

socket.on('chat:history', async (data, callback) => {
  try {
    const messages = await getMessageHistory({
      roomId: data.roomId,
      limit: data.limit || 50,
      before: data.before
    });
    
    callback({ success: true, messages });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 输入状态
// 事件: 'chat:typing'
// 数据: { roomId, isTyping }

socket.on('chat:typing', (data) => {
  socket.to(data.roomId).emit('chat:typing', {
    userId: socket.userId,
    isTyping: data.isTyping
  });
});

// 消息反应
// 事件: 'chat:reaction'
// 数据: { roomId, messageId, emoji }

socket.on('chat:reaction', async (data) => {
  const reaction = await addReaction(data.messageId, socket.userId, data.emoji);
  collaborationNs.to(data.roomId).emit('chat:reaction', {
    messageId: data.messageId,
    reaction
  });
});
```

### 6. 评论/批注

```javascript
// 创建评论
// 事件: 'comment:create'
// 数据: { roomId, documentId, content, position }
// 响应: { success: boolean, comment?: Comment, error?: string }

socket.on('comment:create', async (data, callback) => {
  try {
    const comment = await createComment({
      id: generateId(),
      documentId: data.documentId,
      userId: socket.userId,
      userName: socket.userName,
      content: data.content,
      position: data.position,
      timestamp: Date.now(),
      resolved: false,
      replies: []
    });

    collaborationNs.to(data.roomId).emit('comment:created', comment);
    callback({ success: true, comment });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 回复评论
// 事件: 'comment:reply'
// 数据: { commentId, content }

socket.on('comment:reply', async (data, callback) => {
  const reply = await addReply(data.commentId, {
    id: generateId(),
    userId: socket.userId,
    userName: socket.userName,
    content: data.content,
    timestamp: Date.now()
  });

  const roomId = await getRoomIdByComment(data.commentId);
  collaborationNs.to(roomId).emit('comment:updated', await getComment(data.commentId));
  callback({ success: true });
});

// 获取评论列表
// 事件: 'comment:list'
// 数据: { documentId }
// 响应: { success: boolean, comments?: Comment[], error?: string }

socket.on('comment:list', async (data, callback) => {
  try {
    const comments = await getCommentsByDocument(data.documentId);
    callback({ success: true, comments });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 解决评论
// 事件: 'comment:resolve'
// 数据: { commentId }

socket.on('comment:resolve', async (data) => {
  await resolveComment(data.commentId);
  const roomId = await getRoomIdByComment(data.commentId);
  collaborationNs.to(roomId).emit('comment:resolved', data.commentId);
});

// 删除评论
// 事件: 'comment:delete'
// 数据: { commentId }

socket.on('comment:delete', async (data) => {
  await deleteComment(data.commentId);
  const roomId = await getRoomIdByComment(data.commentId);
  collaborationNs.to(roomId).emit('comment:deleted', data.commentId);
});
```

### 7. 版本历史

```javascript
// 创建版本
// 事件: 'version:create'
// 数据: { roomId, documentId, content, comment? }
// 响应: { success: boolean, version?: DocumentVersion, error?: string }

socket.on('version:create', async (data, callback) => {
  try {
    const versionNumber = await getNextVersionNumber(data.documentId);
    
    const version = await saveVersion({
      id: generateId(),
      documentId: data.documentId,
      version: versionNumber,
      content: data.content,
      createdBy: socket.userId,
      createdAt: Date.now(),
      comment: data.comment,
      changes: await calculateChanges(data.documentId, data.content)
    });

    collaborationNs.to(data.roomId).emit('version:created', version);
    callback({ success: true, version });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 获取版本列表
// 事件: 'version:list'
// 数据: { documentId }
// 响应: { success: boolean, versions?: DocumentVersion[], error?: string }

socket.on('version:list', async (data, callback) => {
  try {
    const versions = await getVersionsByDocument(data.documentId);
    callback({ success: true, versions });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 恢复版本
// 事件: 'version:restore'
// 数据: { versionId }
// 响应: { success: boolean, error?: string }

socket.on('version:restore', async (data, callback) => {
  try {
    const version = await getVersion(data.versionId);
    const roomId = await getRoomIdByDocument(version.documentId);
    
    // 更新 Yjs 文档
    await restoreYjsDoc(version.documentId, version.content);
    
    collaborationNs.to(roomId).emit('version:restored', data.versionId);
    callback({ success: true });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});
```

### 8. 共享学习路径

```javascript
// 创建共享路径
// 事件: 'path:create'
// 数据: { name, description, participants }
// 响应: { success: boolean, path?: SharedLearningPath, error?: string }

socket.on('path:create', async (data, callback) => {
  try {
    const path = await createSharedPath({
      id: generateId(),
      name: data.name,
      description: data.description,
      ownerId: socket.userId,
      participants: [
        { userId: socket.userId, role: 'owner', joinedAt: Date.now(), completedNodes: [] },
        ...data.participants.map((id: string) => ({
          userId: id,
          role: 'member',
          joinedAt: Date.now(),
          completedNodes: []
        }))
      ],
      nodes: [],
      progress: {},
      createdAt: Date.now(),
      updatedAt: Date.now()
    });

    // 通知所有参与者
    data.participants.forEach((userId: string) => {
      const userSocket = getUserSocket(userId);
      if (userSocket) {
        userSocket.emit('path:updated', path);
      }
    });

    callback({ success: true, path });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 更新进度
// 事件: 'path:progress'
// 数据: ProgressUpdate

socket.on('path:progress', async (data) => {
  await updatePathProgress(data);
  
  const path = await getSharedPathByConcept(data.conceptId);
  path.participants.forEach((p: PathParticipant) => {
    const userSocket = getUserSocket(p.userId);
    if (userSocket) {
      userSocket.emit('path:progress', data);
    }
  });
});
```

### 9. 组队挑战

```javascript
// 创建挑战
// 事件: 'challenge:create'
// 响应: { success: boolean, challenge?: TeamChallenge, error?: string }

socket.on('challenge:create', async (data, callback) => {
  try {
    const challenge = await createChallenge({
      ...data,
      id: generateId(),
      createdBy: socket.userId,
      createdAt: Date.now(),
      status: 'waiting'
    });

    callback({ success: true, challenge });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 加入挑战
// 事件: 'challenge:join'
// 数据: { challengeId, teamId? }

socket.on('challenge:join', async (data, callback) => {
  try {
    const challenge = await joinChallenge(
      data.challengeId,
      socket.userId,
      socket.userName,
      data.teamId
    );

    socket.join(`challenge:${data.challengeId}`);
    collaborationNs.to(`challenge:${data.challengeId}`).emit('challenge:updated', challenge);
    
    callback({ success: true, challenge });
  } catch (error) {
    callback({ success: false, error: error.message });
  }
});

// 更新进度
// 事件: 'challenge:progress'

socket.on('challenge:progress', async (data) => {
  await updateChallengeProgress(data.challengeId, data.teamId, data.progress);
  collaborationNs.to(`challenge:${data.challengeId}`).emit('challenge:progress', data);
});

// 更新分数
// 事件: 'challenge:score'

socket.on('challenge:score', async (data) => {
  const newScore = await updateChallengeScore(data.challengeId, data.teamId, data.points);
  collaborationNs.to(`challenge:${data.challengeId}`).emit('challenge:score-update', {
    challengeId: data.challengeId,
    teamId: data.teamId,
    score: newScore
  });
});
```

### 10. 心跳检测

```javascript
// 事件: 'heartbeat'
// 数据: { roomId, timestamp }

socket.on('heartbeat', async (data) => {
  await updateUserLastSeen(data.roomId, socket.userId, data.timestamp);
});

// 定期检查离线用户
setInterval(async () => {
  const offlineThreshold = Date.now() - 60000; // 1分钟
  const offlineUsers = await findOfflineUsers(offlineThreshold);
  
  offlineUsers.forEach((user) => {
    collaborationNs.to(user.roomId).emit('room:user-left', user.userId);
  });
}, 30000);
```

## 数据存储建议

### 数据库模型

```sql
-- 房间表
CREATE TABLE collaboration_rooms (
  id VARCHAR(255) PRIMARY KEY,
  name VARCHAR(255) NOT NULL,
  type VARCHAR(50) NOT NULL,
  document_id VARCHAR(255),
  created_by VARCHAR(255) NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  settings JSON
);

-- 用户Presence表
CREATE TABLE user_presence (
  id VARCHAR(255) PRIMARY KEY,
  room_id VARCHAR(255) NOT NULL,
  user_id VARCHAR(255) NOT NULL,
  user_name VARCHAR(255),
  avatar_url TEXT,
  color VARCHAR(7),
  status VARCHAR(20),
  cursor_position JSON,
  last_seen TIMESTAMP,
  socket_id VARCHAR(255)
);

-- 消息表
CREATE TABLE chat_messages (
  id VARCHAR(255) PRIMARY KEY,
  room_id VARCHAR(255) NOT NULL,
  user_id VARCHAR(255) NOT NULL,
  user_name VARCHAR(255),
  content TEXT NOT NULL,
  type VARCHAR(20),
  reply_to VARCHAR(255),
  reactions JSON,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 评论表
CREATE TABLE comments (
  id VARCHAR(255) PRIMARY KEY,
  document_id VARCHAR(255) NOT NULL,
  user_id VARCHAR(255) NOT NULL,
  user_name VARCHAR(255),
  content TEXT NOT NULL,
  position JSON,
  resolved BOOLEAN DEFAULT FALSE,
  replies JSON,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 版本表
CREATE TABLE document_versions (
  id VARCHAR(255) PRIMARY KEY,
  document_id VARCHAR(255) NOT NULL,
  version INTEGER NOT NULL,
  content JSON,
  created_by VARCHAR(255),
  comment TEXT,
  changes JSON,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
```

## 错误处理

所有 Socket.io 事件应包含回调函数用于错误处理：

```javascript
// 标准响应格式
{
  success: boolean;
  data?: T;        // 成功时返回的数据
  error?: string;  // 失败时的错误信息
}
```

## 性能优化建议

1. **消息分页**: 历史消息使用分页加载，避免一次性加载过多数据
2. **节流处理**: 光标位置和选择状态更新需要节流（建议 50-100ms）
3. **Yjs 持久化**: 定期将 Yjs 文档持久化到数据库
4. **连接复用**: 同一个用户多个标签页应复用同一个 presence 记录
5. **房间清理**: 定期清理无用户的空房间

## 安全考虑

1. **JWT 认证**: 所有 WebSocket 连接必须携带有效的 JWT Token
2. **权限检查**: 房间操作前检查用户权限（owner/editor/viewer）
3. **输入验证**: 所有用户输入内容进行 XSS 过滤
4. **速率限制**: 限制消息发送频率，防止 spam
5. **文档隔离**: 确保用户只能访问有权限的文档
