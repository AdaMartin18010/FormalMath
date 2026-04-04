// ==================== 学习社区后端 API 路由 ====================

const express = require('express');
const router = express.Router();

// 模拟数据库
const db = {
  topics: [],
  questions: [],
  groups: [],
  resources: [],
  users: [],
  points: [],
  notifications: [],
};

// ==================== 讨论区 API ====================

// 获取主题列表
router.get('/discussions', (req, res) => {
  const { category, search, sortBy, page = 1, limit = 20 } = req.query;
  
  let topics = [...db.topics];
  
  // 筛选
  if (category) {
    topics = topics.filter(t => t.category === category);
  }
  
  if (search) {
    topics = topics.filter(t => 
      t.title.toLowerCase().includes(search.toLowerCase()) ||
      t.content.toLowerCase().includes(search.toLowerCase())
    );
  }
  
  // 排序
  switch (sortBy) {
    case 'hot':
      topics.sort((a, b) => b.views - a.views);
      break;
    case 'unanswered':
      topics = topics.filter(t => t.replies.length === 0);
      break;
    case 'top':
      topics.sort((a, b) => b.likes - a.likes);
      break;
    default:
      topics.sort((a, b) => b.createdAt - a.createdAt);
  }
  
  // 分页
  const start = (page - 1) * limit;
  const end = start + parseInt(limit);
  const paginatedTopics = topics.slice(start, end);
  
  res.json({
    success: true,
    data: {
      topics: paginatedTopics,
      total: topics.length,
      hasMore: end < topics.length,
    },
  });
});

// 获取单个主题
router.get('/discussions/:id', (req, res) => {
  const topic = db.topics.find(t => t.id === req.params.id);
  if (!topic) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '主题不存在' } });
  }
  
  // 增加浏览量
  topic.views++;
  
  res.json({ success: true, data: topic });
});

// 创建主题
router.post('/discussions', (req, res) => {
  const { title, content, category, tags } = req.body;
  
  const topic = {
    id: `t${Date.now()}`,
    title,
    content,
    category,
    tags,
    author: req.user, // 假设有认证中间件
    createdAt: Date.now(),
    updatedAt: Date.now(),
    views: 0,
    replies: [],
    likes: 0,
    isPinned: false,
    isLocked: false,
  };
  
  db.topics.push(topic);
  
  // 添加积分
  addPoints(req.user.id, 20, 'post_topic', `发布主题: ${title}`);
  
  res.status(201).json({ success: true, data: topic });
});

// 点赞主题
router.post('/discussions/:id/like', (req, res) => {
  const topic = db.topics.find(t => t.id === req.params.id);
  if (!topic) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '主题不存在' } });
  }
  
  topic.likes++;
  
  // 给作者添加积分
  addPoints(topic.author.id, 5, 'receive_like', '主题获得点赞');
  
  res.json({ success: true, data: { likes: topic.likes } });
});

// 添加回复
router.post('/discussions/:id/replies', (req, res) => {
  const topic = db.topics.find(t => t.id === req.params.id);
  if (!topic) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '主题不存在' } });
  }
  
  const { content, parentReplyId } = req.body;
  
  const reply = {
    id: `r${Date.now()}`,
    topicId: topic.id,
    content,
    author: req.user,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    likes: 0,
    replies: [],
    isAccepted: false,
  };
  
  if (parentReplyId) {
    // 嵌套回复
    const parent = findReply(topic.replies, parentReplyId);
    if (parent) {
      parent.replies.push(reply);
    }
  } else {
    topic.replies.push(reply);
  }
  
  topic.updatedAt = Date.now();
  
  // 添加积分
  addPoints(req.user.id, 10, 'post_reply', '发布回复');
  
  res.status(201).json({ success: true, data: reply });
});

// ==================== 问答 API ====================

// 获取问题列表
router.get('/questions', (req, res) => {
  const { status, difficulty, search, sortBy, page = 1, limit = 20 } = req.query;
  
  let questions = [...db.questions];
  
  if (status) {
    questions = questions.filter(q => q.status === status);
  }
  
  if (difficulty) {
    questions = questions.filter(q => q.difficulty === difficulty);
  }
  
  if (search) {
    questions = questions.filter(q => 
      q.title.toLowerCase().includes(search.toLowerCase())
    );
  }
  
  switch (sortBy) {
    case 'votes':
      questions.sort((a, b) => b.votes - a.votes);
      break;
    case 'bounty':
      questions.sort((a, b) => b.bounty - a.bounty);
      break;
    default:
      questions.sort((a, b) => b.createdAt - a.createdAt);
  }
  
  const start = (page - 1) * limit;
  const end = start + parseInt(limit);
  
  res.json({
    success: true,
    data: {
      questions: questions.slice(start, end),
      total: questions.length,
      hasMore: end < questions.length,
    },
  });
});

// 创建问题
router.post('/questions', (req, res) => {
  const { title, content, difficulty, conceptId, tags, bounty = 0 } = req.body;
  
  // 检查积分是否足够
  if (bounty > 0) {
    const userPoints = getUserPoints(req.user.id);
    if (userPoints < bounty) {
      return res.status(400).json({ 
        success: false, 
        error: { code: 'INSUFFICIENT_POINTS', message: '积分不足' } 
      });
    }
    
    // 扣除悬赏积分
    addPoints(req.user.id, -bounty, 'bounty', '发布悬赏问题');
  }
  
  const question = {
    id: `q${Date.now()}`,
    title,
    content,
    author: req.user,
    tags,
    difficulty,
    conceptId,
    bounty,
    status: 'open',
    createdAt: Date.now(),
    updatedAt: Date.now(),
    views: 0,
    votes: 0,
    answers: [],
    comments: [],
  };
  
  db.questions.push(question);
  
  res.status(201).json({ success: true, data: question });
});

// 采纳答案
router.post('/questions/:id/accept-answer', (req, res) => {
  const { answerId } = req.body;
  const question = db.questions.find(q => q.id === req.params.id);
  
  if (!question) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '问题不存在' } });
  }
  
  const answer = question.answers.find(a => a.id === answerId);
  if (!answer) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '答案不存在' } });
  }
  
  // 标记答案为已采纳
  question.answers.forEach(a => a.isAccepted = false);
  answer.isAccepted = true;
  question.status = 'resolved';
  
  // 给回答者积分
  addPoints(answer.author.id, 50 + question.bounty, 'answer_accepted', '答案被采纳');
  
  res.json({ success: true, data: question });
});

// ==================== 学习小组 API ====================

// 获取小组列表
router.get('/groups', (req, res) => {
  const { category, search, page = 1, limit = 20 } = req.query;
  
  let groups = [...db.groups];
  
  if (category) {
    groups = groups.filter(g => g.category === category);
  }
  
  if (search) {
    groups = groups.filter(g => 
      g.name.toLowerCase().includes(search.toLowerCase())
    );
  }
  
  const start = (page - 1) * limit;
  const end = start + parseInt(limit);
  
  res.json({
    success: true,
    data: {
      groups: groups.slice(start, end),
      total: groups.length,
      hasMore: end < groups.length,
    },
  });
});

// 创建小组
router.post('/groups', (req, res) => {
  const { name, description, category, tags, maxMembers, isPublic } = req.body;
  
  const group = {
    id: `g${Date.now()}`,
    name,
    description,
    category,
    tags,
    owner: req.user,
    members: [{
      user: req.user,
      role: 'owner',
      joinedAt: Date.now(),
      contribution: 0,
      lastActive: Date.now(),
    }],
    maxMembers,
    isPublic,
    createdAt: Date.now(),
    activities: [],
    resources: [],
    discussionTopics: [],
    schedule: [],
  };
  
  db.groups.push(group);
  
  res.status(201).json({ success: true, data: group });
});

// 加入小组
router.post('/groups/:id/join', (req, res) => {
  const group = db.groups.find(g => g.id === req.params.id);
  if (!group) {
    return res.status(404).json({ success: false, error: { code: 'NOT_FOUND', message: '小组不存在' } });
  }
  
  if (group.members.length >= group.maxMembers) {
    return res.status(400).json({ success: false, error: { code: 'GROUP_FULL', message: '小组已满' } });
  }
  
  if (group.members.find(m => m.user.id === req.user.id)) {
    return res.status(400).json({ success: false, error: { code: 'ALREADY_MEMBER', message: '已经是成员' } });
  }
  
  group.members.push({
    user: req.user,
    role: 'member',
    joinedAt: Date.now(),
    contribution: 0,
    lastActive: Date.now(),
  });
  
  res.json({ success: true, data: group });
});

// ==================== 资源分享 API ====================

// 获取资源列表
router.get('/resources', (req, res) => {
  const { type, search, page = 1, limit = 20 } = req.query;
  
  let resources = [...db.resources];
  
  if (type) {
    resources = resources.filter(r => r.type === type);
  }
  
  if (search) {
    resources = resources.filter(r => 
      r.title.toLowerCase().includes(search.toLowerCase())
    );
  }
  
  const start = (page - 1) * limit;
  const end = start + parseInt(limit);
  
  res.json({
    success: true,
    data: {
      resources: resources.slice(start, end),
      total: resources.length,
      hasMore: end < resources.length,
    },
  });
});

// 创建资源
router.post('/resources', (req, res) => {
  const { title, description, type, url, tags, groupId } = req.body;
  
  const resource = {
    id: `res${Date.now()}`,
    title,
    description,
    type,
    url,
    author: req.user,
    groupId,
    tags,
    createdAt: Date.now(),
    likes: 0,
    downloads: 0,
    comments: [],
  };
  
  db.resources.push(resource);
  
  // 添加积分
  addPoints(req.user.id, 30, 'share_resource', `分享资源: ${title}`);
  
  res.status(201).json({ success: true, data: resource });
});

// ==================== 积分系统 API ====================

// 获取积分记录
router.get('/points/records', (req, res) => {
  const { page = 1, limit = 20 } = req.query;
  
  const records = db.points
    .filter(p => p.userId === req.user.id)
    .sort((a, b) => b.createdAt - a.createdAt);
  
  const start = (page - 1) * limit;
  const end = start + parseInt(limit);
  
  res.json({
    success: true,
    data: {
      records: records.slice(start, end),
      total: records.length,
    },
  });
});

// 签到
router.post('/points/checkin', (req, res) => {
  const today = new Date().setHours(0, 0, 0, 0);
  const lastCheckIn = db.points
    .filter(p => p.userId === req.user.id && p.type === 'daily_login')
    .sort((a, b) => b.createdAt - a.createdAt)[0];
  
  if (lastCheckIn && new Date(lastCheckIn.createdAt).setHours(0, 0, 0, 0) === today) {
    return res.status(400).json({ 
      success: false, 
      error: { code: 'ALREADY_CHECKED_IN', message: '今日已签到' } 
    });
  }
  
  addPoints(req.user.id, 10, 'daily_login', '每日签到');
  
  res.json({ success: true, data: { points: 10, message: '签到成功' } });
});

// 获取排行榜
router.get('/points/leaderboard', (req, res) => {
  const { type = 'total', limit = 10 } = req.query;
  
  // 按积分排序用户
  const leaderboard = db.users
    .map(u => ({
      userId: u.id,
      name: u.name,
      level: u.level,
      points: getUserPoints(u.id),
    }))
    .sort((a, b) => b.points - a.points)
    .slice(0, parseInt(limit));
  
  res.json({ success: true, data: leaderboard });
});

// ==================== 通知 API ====================

// 获取通知
router.get('/notifications', (req, res) => {
  const notifications = db.notifications
    .filter(n => n.userId === req.user.id)
    .sort((a, b) => b.createdAt - a.createdAt);
  
  const unreadCount = notifications.filter(n => !n.isRead).length;
  
  res.json({
    success: true,
    data: {
      notifications,
      unreadCount,
    },
  });
});

// 标记已读
router.post('/notifications/:id/read', (req, res) => {
  const notification = db.notifications.find(n => n.id === req.params.id);
  if (notification) {
    notification.isRead = true;
  }
  
  res.json({ success: true });
});

// ==================== 辅助函数 ====================

function findReply(replies, id) {
  for (const reply of replies) {
    if (reply.id === id) return reply;
    const found = findReply(reply.replies || [], id);
    if (found) return found;
  }
  return null;
}

function addPoints(userId, points, type, description) {
  const record = {
    id: `pts${Date.now()}`,
    userId,
    points,
    type,
    description,
    createdAt: Date.now(),
  };
  
  db.points.push(record);
  
  // 更新用户等级
  updateUserLevel(userId);
  
  return record;
}

function getUserPoints(userId) {
  return db.points
    .filter(p => p.userId === userId)
    .reduce((sum, p) => sum + p.points, 0);
}

function updateUserLevel(userId) {
  const points = getUserPoints(userId);
  const user = db.users.find(u => u.id === userId);
  
  if (user) {
    // 根据积分计算等级
    const levelDefinitions = [
      { level: 1, minPoints: 0 },
      { level: 2, minPoints: 100 },
      { level: 3, minPoints: 300 },
      { level: 4, minPoints: 600 },
      { level: 5, minPoints: 1000 },
      { level: 6, minPoints: 1500 },
      { level: 7, minPoints: 2200 },
      { level: 8, minPoints: 3000 },
      { level: 9, minPoints: 4000 },
      { level: 10, minPoints: 5500 },
      { level: 11, minPoints: 7500 },
      { level: 12, minPoints: 10000 },
    ];
    
    const newLevel = levelDefinitions
      .slice()
      .reverse()
      .find(l => points >= l.minPoints);
    
    if (newLevel && newLevel.level > user.level) {
      user.level = newLevel.level;
      
      // 添加升级通知
      db.notifications.push({
        id: `notif${Date.now()}`,
        userId,
        type: 'level_up',
        title: '等级提升！',
        content: `恭喜你升级到等级 ${newLevel.level}！`,
        isRead: false,
        createdAt: Date.now(),
      });
    }
  }
}

module.exports = router;
