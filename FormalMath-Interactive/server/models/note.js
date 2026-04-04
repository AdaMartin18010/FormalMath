// ==================== 笔记系统数据模型 ====================
const mongoose = require('mongoose');

// 标签Schema
const TagSchema = new mongoose.Schema({
  name: {
    type: String,
    required: true,
    trim: true,
  },
  color: {
    type: String,
    default: '#3B82F6',
  },
  user: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'User',
    required: true,
  },
  count: {
    type: Number,
    default: 0,
  },
}, {
  timestamps: true,
});

// 文件夹Schema
const FolderSchema = new mongoose.Schema({
  name: {
    type: String,
    required: true,
    trim: true,
  },
  description: {
    type: String,
    trim: true,
  },
  parent: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Folder',
    default: null,
  },
  user: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'User',
    required: true,
  },
  noteCount: {
    type: Number,
    default: 0,
  },
}, {
  timestamps: true,
});

// 笔记版本Schema
const VersionSchema = new mongoose.Schema({
  note: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Note',
    required: true,
  },
  version: {
    type: Number,
    required: true,
  },
  title: {
    type: String,
    required: true,
  },
  content: {
    type: String,
    required: true,
  },
  changeSummary: {
    type: String,
  },
  createdBy: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'User',
    required: true,
  },
}, {
  timestamps: true,
});

// AI分析结果Schema
const AIAnalysisSchema = new mongoose.Schema({
  summary: {
    type: String,
  },
  keyConcepts: [{
    type: String,
  }],
  suggestedTags: [{
    type: String,
  }],
  difficulty: {
    type: String,
    enum: ['beginner', 'intermediate', 'advanced'],
  },
  estimatedReadTime: {
    type: Number,
  },
  conceptLinks: [{
    conceptId: {
      type: String,
      required: true,
    },
    conceptName: {
      type: String,
      required: true,
    },
    relationType: {
      type: String,
      enum: ['defines', 'explains', 'applies', 'references', 'extends'],
      required: true,
    },
    relevanceScore: {
      type: Number,
      min: 0,
      max: 1,
      default: 0.5,
    },
  }],
  generatedAt: {
    type: Date,
    default: Date.now,
  },
});

// 分享设置Schema
const ShareSettingsSchema = new mongoose.Schema({
  isPublic: {
    type: Boolean,
    default: false,
  },
  shareLink: {
    type: String,
    unique: true,
    sparse: true,
  },
  password: {
    type: String,
  },
  expiresAt: {
    type: Date,
  },
  allowComments: {
    type: Boolean,
    default: true,
  },
  allowEdit: {
    type: Boolean,
    default: false,
  },
  viewCount: {
    type: Number,
    default: 0,
  },
});

// 评论Schema
const CommentSchema = new mongoose.Schema({
  note: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Note',
    required: true,
  },
  content: {
    type: String,
    required: true,
  },
  author: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'User',
    required: true,
  },
  parent: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Comment',
    default: null,
  },
}, {
  timestamps: true,
});

// 主笔记Schema
const NoteSchema = new mongoose.Schema({
  title: {
    type: String,
    required: true,
    trim: true,
    default: '未命名笔记',
  },
  content: {
    type: String,
    default: '',
  },
  type: {
    type: String,
    enum: ['concept', 'theorem', 'proof', 'example', 'exercise', 'general'],
    default: 'general',
  },
  status: {
    type: String,
    enum: ['draft', 'published', 'archived', 'shared'],
    default: 'draft',
  },
  tags: [{
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Tag',
  }],
  author: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'User',
    required: true,
  },
  folder: {
    type: mongoose.Schema.Types.ObjectId,
    ref: 'Folder',
    default: null,
  },
  version: {
    type: Number,
    default: 1,
  },
  wordCount: {
    type: Number,
    default: 0,
  },
  aiAnalysis: AIAnalysisSchema,
  shareSettings: ShareSettingsSchema,
  isPinned: {
    type: Boolean,
    default: false,
  },
  isFavorite: {
    type: Boolean,
    default: false,
  },
  lastEditedAt: {
    type: Date,
    default: Date.now,
  },
}, {
  timestamps: true,
});

// 索引
NoteSchema.index({ title: 'text', content: 'text' });
NoteSchema.index({ author: 1, createdAt: -1 });
NoteSchema.index({ folder: 1 });
NoteSchema.index({ tags: 1 });
NoteSchema.index({ isPinned: -1, updatedAt: -1 });

// 虚拟字段：计算实际字数
NoteSchema.virtual('actualWordCount').get(function() {
  if (!this.content) return 0;
  // 移除Markdown标记后计算
  const plainText = this.content
    .replace(/[#*`\[\](){}]/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
  return plainText.length;
});

// 保存前钩子
NoteSchema.pre('save', function(next) {
  // 更新字数
  this.wordCount = this.actualWordCount;
  this.lastEditedAt = new Date();
  next();
});

// 静态方法
NoteSchema.statics.search = async function(query, userId, options = {}) {
  const { fuzzy = true, limit = 50, skip = 0 } = options;
  
  const searchQuery = {
    author: userId,
    $or: [
      { title: { $regex: query, $options: 'i' } },
      { content: { $regex: query, $options: 'i' } },
    ],
  };

  if (!fuzzy) {
    searchQuery.$text = { $search: query };
    delete searchQuery.$or;
  }

  return this.find(searchQuery)
    .populate('tags', 'name color')
    .populate('author', 'name avatar')
    .sort({ updatedAt: -1 })
    .skip(skip)
    .limit(limit)
    .lean();
};

NoteSchema.statics.getStatistics = async function(userId) {
  const stats = await this.aggregate([
    { $match: { author: new mongoose.Types.ObjectId(userId) } },
    {
      $group: {
        _id: null,
        totalNotes: { $sum: 1 },
        totalWords: { $sum: '$wordCount' },
        notesByType: {
          $push: '$type',
        },
      },
    },
  ]);

  const typeCounts = await this.aggregate([
    { $match: { author: new mongoose.Types.ObjectId(userId) } },
    { $group: { _id: '$type', count: { $sum: 1 } } },
  ]);

  const notesByType = {};
  typeCounts.forEach((t) => {
    notesByType[t._id] = t.count;
  });

  return {
    totalNotes: stats[0]?.totalNotes || 0,
    totalWords: stats[0]?.totalWords || 0,
    notesByType,
  };
};

// 创建模型
const Note = mongoose.model('Note', NoteSchema);
const Tag = mongoose.model('Tag', TagSchema);
const Folder = mongoose.model('Folder', FolderSchema);
const Version = mongoose.model('Version', VersionSchema);
const Comment = mongoose.model('Comment', CommentSchema);

module.exports = {
  Note,
  Tag,
  Folder,
  Version,
  Comment,
};
