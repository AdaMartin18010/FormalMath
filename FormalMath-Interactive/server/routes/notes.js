// ==================== 笔记系统API路由 ====================
const express = require('express');
const router = express.Router();
const { v4: uuidv4 } = require('uuid');
const { Note, Tag, Folder, Version, Comment } = require('../models/note');

// 认证中间件（简化版，实际应该使用JWT等）
const auth = (req, res, next) => {
  // 假设用户信息存储在req.user中
  req.user = { _id: 'current-user-id', name: 'Current User' };
  next();
};

// ==================== 笔记CRUD ====================

// 获取笔记列表
router.get('/', auth, async (req, res) => {
  try {
    const { folderId, type, status, sort = 'updatedAt', order = 'desc' } = req.query;
    
    const query = { author: req.user._id };
    if (folderId) query.folder = folderId;
    if (type) query.type = type;
    if (status) query.status = status;

    const sortOption = {};
    sortOption[sort] = order === 'asc' ? 1 : -1;

    const notes = await Note.find(query)
      .populate('tags', 'name color')
      .populate('author', 'name avatar')
      .populate('folder', 'name')
      .sort(sortOption)
      .lean();

    res.json({
      success: true,
      data: notes,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// 获取单篇笔记
router.get('/:id', auth, async (req, res) => {
  try {
    const note = await Note.findOne({
      _id: req.params.id,
      author: req.user._id,
    })
      .populate('tags', 'name color')
      .populate('author', 'name avatar')
      .populate('folder', 'name');

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// 创建笔记
router.post('/', auth, async (req, res) => {
  try {
    const noteData = {
      ...req.body,
      author: req.user._id,
    };

    const note = new Note(noteData);
    await note.save();

    // 创建版本记录
    const version = new Version({
      note: note._id,
      version: 1,
      title: note.title,
      content: note.content,
      createdBy: req.user._id,
      changeSummary: '创建笔记',
    });
    await version.save();

    // 更新文件夹笔记数
    if (note.folder) {
      await Folder.findByIdAndUpdate(note.folder, {
        $inc: { noteCount: 1 },
      });
    }

    await note.populate('tags author');

    res.status(201).json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'CREATE_ERROR', message: error.message },
    });
  }
});

// 更新笔记
router.patch('/:id', auth, async (req, res) => {
  try {
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      { ...req.body, $inc: { version: 1 } },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    // 创建新版本记录
    const lastVersion = await Version.findOne({ note: note._id })
      .sort({ version: -1 });
    
    const version = new Version({
      note: note._id,
      version: (lastVersion?.version || 0) + 1,
      title: note.title,
      content: note.content,
      createdBy: req.user._id,
      changeSummary: req.body.changeSummary || '更新笔记',
    });
    await version.save();

    await note.populate('tags author');

    res.json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UPDATE_ERROR', message: error.message },
    });
  }
});

// 删除笔记
router.delete('/:id', auth, async (req, res) => {
  try {
    const note = await Note.findOneAndDelete({
      _id: req.params.id,
      author: req.user._id,
    });

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    // 更新文件夹笔记数
    if (note.folder) {
      await Folder.findByIdAndUpdate(note.folder, {
        $inc: { noteCount: -1 },
      });
    }

    // 删除相关版本
    await Version.deleteMany({ note: req.params.id });

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'DELETE_ERROR', message: error.message },
    });
  }
});

// 批量删除
router.post('/batch-delete', auth, async (req, res) => {
  try {
    const { ids } = req.body;
    
    await Note.deleteMany({
      _id: { $in: ids },
      author: req.user._id,
    });

    await Version.deleteMany({
      note: { $in: ids },
    });

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'BATCH_DELETE_ERROR', message: error.message },
    });
  }
});

// ==================== 版本历史 ====================

// 获取笔记版本历史
router.get('/:id/versions', auth, async (req, res) => {
  try {
    const versions = await Version.find({ note: req.params.id })
      .populate('createdBy', 'name avatar')
      .sort({ version: -1 })
      .lean();

    res.json({
      success: true,
      data: versions,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// 恢复版本
router.post('/:id/restore', auth, async (req, res) => {
  try {
    const { versionId } = req.body;
    const version = await Version.findById(versionId);

    if (!version) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '版本不存在' },
      });
    }

    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      {
        title: version.title,
        content: version.content,
        $inc: { version: 1 },
      },
      { new: true }
    );

    res.json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'RESTORE_ERROR', message: error.message },
    });
  }
});

// ==================== 搜索 ====================

// 搜索笔记
router.get('/search', auth, async (req, res) => {
  try {
    const { q, fuzzy = 'true', limit = 50 } = req.query;
    
    const results = await Note.search(q, req.user._id, {
      fuzzy: fuzzy === 'true',
      limit: parseInt(limit),
    });

    // 高亮处理
    const highlightedResults = results.map((note) => ({
      note,
      highlights: {
        title: note.title.replace(
          new RegExp(q, 'gi'),
          (match) => `<mark>${match}</mark>`
        ),
        content: note.content
          ?.substring(0, 200)
          .replace(new RegExp(q, 'gi'), (match) => `<mark>${match}</mark>`),
      },
      relevanceScore: 1.0,
    }));

    res.json({
      success: true,
      data: highlightedResults,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'SEARCH_ERROR', message: error.message },
    });
  }
});

// 高级搜索
router.post('/search/advanced', auth, async (req, res) => {
  try {
    const { filters, sort, page = 1, pageSize = 20 } = req.body;
    
    const query = { author: req.user._id };
    
    if (filters.type) query.type = filters.type;
    if (filters.status) query.status = filters.status;
    if (filters.tags?.length > 0) query.tags = { $in: filters.tags };
    if (filters.dateRange) {
      query.updatedAt = {
        $gte: new Date(filters.dateRange.start),
        $lte: new Date(filters.dateRange.end),
      };
    }

    const sortOption = {};
    const [sortField, sortOrder] = sort.split('_');
    sortOption[sortField] = sortOrder === 'asc' ? 1 : -1;

    const skip = (page - 1) * pageSize;

    const [results, total] = await Promise.all([
      Note.find(query)
        .populate('tags', 'name color')
        .populate('author', 'name avatar')
        .sort(sortOption)
        .skip(skip)
        .limit(pageSize)
        .lean(),
      Note.countDocuments(query),
    ]);

    res.json({
      success: true,
      data: {
        results: results.map((note) => ({ note, highlights: {}, relevanceScore: 1 })),
        total,
      },
      meta: {
        page,
        pageSize,
        total,
        timestamp: new Date().toISOString(),
      },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'SEARCH_ERROR', message: error.message },
    });
  }
});

// ==================== 标签管理 ====================

// 获取标签列表
router.get('/tags', auth, async (req, res) => {
  try {
    const tags = await Tag.find({ user: req.user._id })
      .sort({ count: -1 })
      .lean();

    res.json({
      success: true,
      data: tags,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// 创建标签
router.post('/tags', auth, async (req, res) => {
  try {
    const tag = new Tag({
      ...req.body,
      user: req.user._id,
    });
    await tag.save();

    res.status(201).json({
      success: true,
      data: tag,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'CREATE_ERROR', message: error.message },
    });
  }
});

// 更新标签
router.patch('/tags/:id', auth, async (req, res) => {
  try {
    const tag = await Tag.findOneAndUpdate(
      { _id: req.params.id, user: req.user._id },
      req.body,
      { new: true }
    );

    if (!tag) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '标签不存在' },
      });
    }

    res.json({
      success: true,
      data: tag,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UPDATE_ERROR', message: error.message },
    });
  }
});

// 删除标签
router.delete('/tags/:id', auth, async (req, res) => {
  try {
    await Tag.findOneAndDelete({
      _id: req.params.id,
      user: req.user._id,
    });

    // 从笔记中移除该标签
    await Note.updateMany(
      { tags: req.params.id },
      { $pull: { tags: req.params.id } }
    );

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'DELETE_ERROR', message: error.message },
    });
  }
});

// 批量标签操作
router.post('/tags/batch', auth, async (req, res) => {
  try {
    const { noteIds, tagIds, action } = req.body;
    
    if (action === 'add') {
      await Note.updateMany(
        { _id: { $in: noteIds }, author: req.user._id },
        { $addToSet: { tags: { $each: tagIds } } }
      );
    } else {
      await Note.updateMany(
        { _id: { $in: noteIds }, author: req.user._id },
        { $pull: { tags: { $in: tagIds } } }
      );
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'BATCH_ERROR', message: error.message },
    });
  }
});

// ==================== 文件夹管理 ====================

// 获取文件夹列表
router.get('/folders', auth, async (req, res) => {
  try {
    const folders = await Folder.find({ user: req.user._id })
      .sort({ name: 1 })
      .lean();

    res.json({
      success: true,
      data: folders,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// 创建文件夹
router.post('/folders', auth, async (req, res) => {
  try {
    const folder = new Folder({
      ...req.body,
      user: req.user._id,
    });
    await folder.save();

    res.status(201).json({
      success: true,
      data: folder,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'CREATE_ERROR', message: error.message },
    });
  }
});

// 更新文件夹
router.patch('/folders/:id', auth, async (req, res) => {
  try {
    const folder = await Folder.findOneAndUpdate(
      { _id: req.params.id, user: req.user._id },
      req.body,
      { new: true }
    );

    if (!folder) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '文件夹不存在' },
      });
    }

    res.json({
      success: true,
      data: folder,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UPDATE_ERROR', message: error.message },
    });
  }
});

// 删除文件夹
router.delete('/folders/:id', auth, async (req, res) => {
  try {
    const { deleteNotes } = req.query;
    
    const folder = await Folder.findOneAndDelete({
      _id: req.params.id,
      user: req.user._id,
    });

    if (!folder) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '文件夹不存在' },
      });
    }

    if (deleteNotes === 'true') {
      await Note.deleteMany({ folder: req.params.id });
    } else {
      await Note.updateMany(
        { folder: req.params.id },
        { $set: { folder: null } }
      );
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'DELETE_ERROR', message: error.message },
    });
  }
});

// 移动笔记到文件夹
router.post('/folders/move', auth, async (req, res) => {
  try {
    const { noteIds, folderId } = req.body;
    
    // 获取原文件夹
    const notes = await Note.find({
      _id: { $in: noteIds },
      author: req.user._id,
    });

    const oldFolderIds = notes.map((n) => n.folder).filter(Boolean);

    // 更新笔记文件夹
    await Note.updateMany(
      { _id: { $in: noteIds }, author: req.user._id },
      { $set: { folder: folderId || null } }
    );

    // 更新文件夹计数
    await Folder.updateMany(
      { _id: { $in: oldFolderIds } },
      { $inc: { noteCount: -1 } }
    );
    
    if (folderId) {
      await Folder.findByIdAndUpdate(folderId, {
        $inc: { noteCount: noteIds.length },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'MOVE_ERROR', message: error.message },
    });
  }
});

// ==================== 分享功能 ====================

// 分享笔记
router.post('/:id/share', auth, async (req, res) => {
  try {
    const note = await Note.findOne({
      _id: req.params.id,
      author: req.user._id,
    });

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    const shareLink = note.shareSettings?.shareLink || uuidv4();
    
    note.shareSettings = {
      ...note.shareSettings,
      ...req.body,
      isPublic: true,
      shareLink,
    };
    
    await note.save();

    res.json({
      success: true,
      data: note.shareSettings,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'SHARE_ERROR', message: error.message },
    });
  }
});

// 取消分享
router.delete('/:id/share', auth, async (req, res) => {
  try {
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      {
        $set: {
          'shareSettings.isPublic': false,
          'shareSettings.shareLink': null,
        },
      },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UNSHARE_ERROR', message: error.message },
    });
  }
});

// 获取分享的笔记
router.get('/shared/:shareLink', async (req, res) => {
  try {
    const note = await Note.findOne({
      'shareSettings.shareLink': req.params.shareLink,
      'shareSettings.isPublic': true,
    })
      .populate('tags', 'name color')
      .populate('author', 'name avatar');

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在或已取消分享' },
      });
    }

    // 检查是否过期
    if (note.shareSettings.expiresAt && new Date(note.shareSettings.expiresAt) < new Date()) {
      return res.status(403).json({
        success: false,
        error: { code: 'EXPIRED', message: '分享链接已过期' },
      });
    }

    // 增加查看次数
    note.shareSettings.viewCount += 1;
    await note.save();

    res.json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// ==================== AI助手功能 ====================

// 分析笔记
router.post('/:id/analyze', auth, async (req, res) => {
  try {
    const note = await Note.findOne({
      _id: req.params.id,
      author: req.user._id,
    });

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    // 模拟AI分析（实际应调用AI服务）
    const analysis = {
      summary: `这是关于"${note.title}"的笔记总结...`,
      keyConcepts: ['概念A', '概念B', '概念C'],
      suggestedTags: ['标签1', '标签2'],
      difficulty: 'intermediate',
      estimatedReadTime: Math.ceil(note.wordCount / 200),
      conceptLinks: [],
      generatedAt: new Date().toISOString(),
    };

    note.aiAnalysis = analysis;
    await note.save();

    res.json({
      success: true,
      data: analysis,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'ANALYZE_ERROR', message: error.message },
    });
  }
});

// AI助手请求
router.post('/ai/assist', auth, async (req, res) => {
  try {
    const { type, content, context } = req.body;

    // 模拟AI响应（实际应调用AI服务）
    let result = '';
    switch (type) {
      case 'summarize':
        result = '根据您的笔记内容，核心要点如下：\n1. ...\n2. ...\n3. ...';
        break;
      case 'explain':
        result = '这是对选中内容的详细解释...';
        break;
      case 'expand':
        result = '建议您可以扩展以下内容：...';
        break;
      case 'relate':
        result = '相关的知识概念包括：...';
        break;
      case 'suggest':
        result = '根据您的笔记，我有以下建议：...';
        break;
      default:
        result = 'AI助手已收到您的请求。';
    }

    res.json({
      success: true,
      data: {
        result,
        followUpQuestions: ['问题1?', '问题2?', '问题3?'],
      },
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'AI_ERROR', message: error.message },
    });
  }
});

// 建议概念关联
router.get('/:id/suggest-links', auth, async (req, res) => {
  try {
    // 模拟推荐（实际应基于内容分析）
    const suggestions = [
      { conceptId: 'c1', conceptName: '群论', relationType: 'references', relevanceScore: 0.85 },
      { conceptId: 'c4', conceptName: '向量空间', relationType: 'applies', relevanceScore: 0.72 },
      { conceptId: 'c7', conceptName: '微积分', relationType: 'extends', relevanceScore: 0.68 },
    ];

    res.json({
      success: true,
      data: suggestions,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'SUGGEST_ERROR', message: error.message },
    });
  }
});

// 生成笔记总结
router.post('/:id/summarize', auth, async (req, res) => {
  try {
    const { maxLength = 200 } = req.body;
    
    const note = await Note.findById(req.params.id);
    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    // 模拟总结生成
    const summary = note.content
      ?.substring(0, maxLength)
      ?.replace(/[#*`]/g, '') + '...' || '笔记内容为空';

    res.json({
      success: true,
      data: summary,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'SUMMARIZE_ERROR', message: error.message },
    });
  }
});

// 自动标签
router.post('/:id/auto-tag', auth, async (req, res) => {
  try {
    // 模拟自动标签（实际应基于内容分析）
    const suggestedTags = ['数学', '代数', '重要'];

    res.json({
      success: true,
      data: suggestedTags,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'AUTO_TAG_ERROR', message: error.message },
    });
  }
});

// ==================== 知识图谱关联 ====================

// 关联概念
router.post('/:id/concepts', auth, async (req, res) => {
  try {
    const { conceptId, relationType } = req.body;
    
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      {
        $addToSet: {
          'aiAnalysis.conceptLinks': {
            conceptId,
            conceptName: 'Concept ' + conceptId, // 应从概念库获取
            relationType,
            relevanceScore: 1,
          },
        },
      },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'LINK_ERROR', message: error.message },
    });
  }
});

// 取消关联概念
router.delete('/:id/concepts/:conceptId', auth, async (req, res) => {
  try {
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      {
        $pull: {
          'aiAnalysis.conceptLinks': { conceptId: req.params.conceptId },
        },
      },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UNLINK_ERROR', message: error.message },
    });
  }
});

// 获取相关笔记
router.get('/:id/related', auth, async (req, res) => {
  try {
    const note = await Note.findById(req.params.id);
    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    // 基于标签和概念查找相关笔记
    const relatedNotes = await Note.find({
      _id: { $ne: req.params.id },
      author: req.user._id,
      $or: [
        { tags: { $in: note.tags } },
        { type: note.type },
      ],
    })
      .limit(5)
      .populate('tags', 'name color')
      .lean();

    res.json({
      success: true,
      data: relatedNotes,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// ==================== 统计 ====================

// 获取笔记统计
router.get('/statistics', auth, async (req, res) => {
  try {
    const stats = await Note.getStatistics(req.user._id);

    // 获取标签使用统计
    const tagStats = await Tag.find({ user: req.user._id })
      .sort({ count: -1 })
      .limit(10)
      .lean();

    // 获取最近活动
    const recentActivity = await Note.aggregate([
      { $match: { author: new mongoose.Types.ObjectId(req.user._id) } },
      {
        $group: {
          _id: {
            $dateToString: { format: '%Y-%m-%d', date: '$updatedAt' },
          },
          notesUpdated: { $sum: 1 },
          notesCreated: {
            $sum: {
              $cond: [
                { $eq: ['$createdAt', '$updatedAt'] },
                1,
                0,
              ],
            },
          },
        },
      },
      { $sort: { _id: -1 } },
      { $limit: 7 },
    ]);

    res.json({
      success: true,
      data: {
        ...stats,
        mostUsedTags: tagStats,
        recentActivity: recentActivity.map((a) => ({
          date: a._id,
          notesCreated: a.notesCreated,
          notesUpdated: a.notesUpdated,
        })),
      },
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'FETCH_ERROR', message: error.message },
    });
  }
});

// ==================== 快捷操作 ====================

// 收藏/取消收藏
router.patch('/:id/favorite', auth, async (req, res) => {
  try {
    const { isFavorite } = req.body;
    
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      { isFavorite },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UPDATE_ERROR', message: error.message },
    });
  }
});

// 置顶/取消置顶
router.patch('/:id/pinned', auth, async (req, res) => {
  try {
    const { isPinned } = req.body;
    
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      { isPinned },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: null,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'UPDATE_ERROR', message: error.message },
    });
  }
});

// 自动保存
router.post('/:id/autosave', auth, async (req, res) => {
  try {
    const { content, title } = req.body;
    
    const note = await Note.findOneAndUpdate(
      { _id: req.params.id, author: req.user._id },
      { content, title },
      { new: true }
    );

    if (!note) {
      return res.status(404).json({
        success: false,
        error: { code: 'NOT_FOUND', message: '笔记不存在' },
      });
    }

    res.json({
      success: true,
      data: note,
      meta: { timestamp: new Date().toISOString() },
    });
  } catch (error) {
    res.status(500).json({
      success: false,
      error: { code: 'AUTOSAVE_ERROR', message: error.message },
    });
  }
});

module.exports = router;
