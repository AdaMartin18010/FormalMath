---
title: FormalMath 用户反馈系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 用户反馈系统

## 系统概述

FormalMath 用户反馈系统是一个完整的反馈收集、分类、处理和可视化解决方案，支持自动分类、优先级判定、情感分析和仪表板展示。

## 功能特性

### 核心功能
- ✅ **反馈提交**：支持匿名和登录用户提交反馈
- ✅ **自动分类**：基于关键词和规则的智能分类（8种类型）
- ✅ **优先级判定**：自动判定紧急、高、中、低优先级
- ✅ **情感分析**：分析反馈的情感倾向（正面/负面/中性）
- ✅ **状态管理**：完整的状态流转（待处理→分类→审核→处理→解决→关闭）
- ✅ **回复系统**：支持公开回复和内部备注
- ✅ **仪表板**：实时数据可视化和统计分析

### 高级功能
- 📊 **统计分析**：日/周/月报自动生成
- 🔍 **趋势分析**：多维度趋势数据
- 📈 **可视化图表**：支持集成图表库
- ⚡ **异步处理**：Celery任务队列
- 🔔 **通知机制**：多渠道通知（邮件/Slack/短信）

## 快速开始

### 1. 初始化系统

```bash
cd FormalMath-Enhanced/api/app

# 初始化表和数据
python scripts/init_feedback_system.py --init

# 测试分类器
python scripts/init_feedback_system.py --test

# 查看统计
python scripts/init_feedback_system.py --stats

# 执行所有操作
python scripts/init_feedback_system.py --all
```

### 2. API 使用示例

#### 提交反馈
```bash
curl -X POST "http://localhost:8000/api/v1/feedback/feedbacks" \
  -H "Content-Type: application/json" \
  -d '{
    "title": "搜索功能无法使用",
    "content": "在搜索框输入关键词后，页面一直显示加载中",
    "satisfaction_rating": 2
  }'
```

#### 获取反馈列表
```bash
curl "http://localhost:8000/api/v1/feedback/feedbacks?page=1&page_size=10"
```

#### 仪表板数据
```bash
curl "http://localhost:8000/api/v1/feedback/dashboard/summary"
```

## 项目结构

```
FormalMath-Enhanced/api/app/
├── api/
│   ├── feedback.py              # 反馈API端点
│   └── router.py                # 路由聚合（已更新）
├── models/
│   └── models.py                # 数据模型（已更新）
├── services/
│   ├── feedback_classifier.py   # 自动分类服务
│   └── feedback_service.py      # 反馈业务服务
├── tasks/
│   └── feedback_tasks.py        # Celery异步任务
├── core/
│   └── database.py              # 数据库配置（已更新）
├── scripts/
│   └── init_feedback_system.py  # 初始化脚本
├── tests/
│   └── test_feedback.py         # 单元测试
└── docs/
    ├── feedback_README.md       # 本文件
    ├── feedback_api.md          # API文档
    └── feedback_workflow.md     # 处理流程文档
```

## 数据模型

### 主要表结构

```
┌─────────────────────┐
│   user_feedbacks    │  用户反馈表
├─────────────────────┤
│ id                  │
│ user_id             │  用户ID（可选）
│ title               │  标题
│ content             │  内容
│ feedback_type       │  反馈类型
│ auto_classified_type│  自动分类类型
│ classification_confidence│ 分类置信度
│ status              │  状态
│ priority            │  优先级
│ related_concept_id  │  相关概念ID
│ satisfaction_rating │  满意度评分
│ created_at          │  创建时间
└─────────────────────┘

┌─────────────────────┐
│  feedback_responses │  反馈回复表
├─────────────────────┤
│ id                  │
│ feedback_id         │  反馈ID
│ responder_id        │  回复人ID
│ content             │  内容
│ is_internal         │  是否内部备注
└─────────────────────┘

┌─────────────────────┐
│feedback_processing_ │  处理日志表
│       logs          │
├─────────────────────┤
│ id                  │
│ feedback_id         │  反馈ID
│ action              │  操作类型
│ old/new_status      │  状态变更
│ old/new_priority    │  优先级变更
│ performed_by        │  操作人
└─────────────────────┘

┌─────────────────────┐
│ feedback_analytics  │  统计分析表
├─────────────────────┤
│ id                  │
│ period_type         │  周期类型
│ period_start/end    │  周期起止
│ total_feedbacks     │  总数
│ feedbacks_by_type   │  类型分布
│ avg_resolution_time │  平均解决时间
│ satisfaction_stats  │  满意度统计
└─────────────────────┘
```

## 分类算法

### 反馈类型
| 类型 | 说明 | 关键词示例 |
|------|------|------------|
| `bug_report` | 错误报告 | bug, 错误, 崩溃, crash |
| `feature_request` | 功能请求 | 功能, 建议, 希望, feature |
| `content_error` | 内容错误 | 错误, 不正确, 错字, wrong |
| `usability` | 可用性 | 难用, 不方便, 界面, UI |
| `performance` | 性能问题 | 慢, 卡顿, 加载, slow |
| `general` | 一般反馈 | 咨询, 问题, 疑问, question |
| `complaint` | 投诉 | 失望, 不满, 糟糕, terrible |
| `compliment` | 表扬 | 好评, 棒, 赞, great |

### 分类置信度
```
confidence = 0.5 + (最佳类型得分 / 总得分) × 0.5

> 0.8: 高可信度
0.5-0.8: 中等可信度
< 0.5: 低可信度（需要人工确认）
```

## 状态流转

```
pending ──► classified ──► under_review ──► in_progress ──► resolved ──► closed
                                              │
                                              └──► rejected
```

| 状态 | 说明 |
|------|------|
| `pending` | 待处理（用户提交后） |
| `classified` | 已分类（自动分类完成） |
| `under_review` | 审核中（管理员查看） |
| `in_progress` | 处理中（开始解决问题） |
| `resolved` | 已解决 |
| `closed` | 已关闭（自动或手动） |
| `rejected` | 已拒绝 |

## Celery 定时任务

| 任务 | 频率 | 说明 |
|------|------|------|
| `process_new_feedback` | 每小时 | 处理新提交的反馈 |
| `auto_close_resolved` | 每天 | 自动关闭已解决7天的反馈 |
| `generate_daily_analytics` | 每天 | 生成日报 |
| `generate_weekly_analytics` | 每周 | 生成周报 |
| `generate_monthly_analytics` | 每月 | 生成月报 |

启动Celery Worker：
```bash
cd FormalMath-Enhanced/api
celery -A app.tasks.celery_app worker --loglevel=info
celery -A app.tasks.celery_app beat --loglevel=info
```

## 测试

运行测试：
```bash
# 运行所有测试
pytest tests/test_feedback.py -v

# 运行特定测试类
pytest tests/test_feedback.py::TestFeedbackClassifier -v

# 运行特定测试方法
pytest tests/test_feedback.py::TestFeedbackClassifier::test_classify_bug_report -v
```

## API 文档

详细API文档请参考：
- [API文档](feedback_api.md) - 完整API参考
- [处理流程文档](feedback_workflow.md) - 业务流程说明

## 配置说明

### 环境变量
```env
# 通知配置（可选）
SMTP_HOST=smtp.example.com
SMTP_PORT=587
SMTP_USER=user@example.com
SMTP_PASSWORD=password

SLACK_WEBHOOK_URL=https://hooks.slack.com/...
```

### 分类规则自定义
编辑 `services/feedback_classifier.py` 中的 `KEYWORD_RULES` 和 `PRIORITY_RULES` 来自定义分类规则。

## 性能优化

### 数据库索引
已创建的索引：
- `idx_feedback_status_created` - 状态+创建时间
- `idx_feedback_type_priority` - 类型+优先级
- `idx_feedback_user_created` - 用户+创建时间
- `idx_feedback_assigned` - 指派人+状态

### 查询优化
- 使用数据库连接池
- 分页查询避免大数据量
- 统计信息使用缓存

## 扩展开发

### 添加新的反馈类型
1. 在 `models/models.py` 的 `FeedbackType` 中添加新类型
2. 在 `services/feedback_classifier.py` 中添加分类规则
3. 更新前端类型选择器

### 集成AI模型
1. 安装AI模型依赖（如transformers）
2. 创建 `services/feedback_ai_classifier.py`
3. 在 `services/feedback_classifier.py` 中调用

### 自定义通知渠道
1. 在 `tasks/feedback_tasks.py` 中添加通知任务
2. 实现具体的通知发送逻辑
3. 更新 `_determine_notification_channels` 方法

## 常见问题

**Q: 如何支持多语言反馈分类？**  
A: 需要扩展 `KEYWORD_RULES` 添加多语言关键词，或使用支持多语言的AI模型。

**Q: 如何提高分类准确率？**  
A: 定期分析分类结果，收集管理员修正数据，持续优化关键词规则或训练AI模型。

**Q: 如何处理大量反馈？**  
A: 使用Celery异步处理，数据库查询优化，必要时添加Elasticsearch全文搜索。

## 许可证

MIT License
