---
title: FormalMath API 变更日志
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath API 变更日志

所有重要的变更都记录在此文件中。

格式基于 [Keep a Changelog](https://keepachangelog.com/zh-CN/1.0.0/)[需更新]，版本号遵循 [Semantic Versioning](https://semver.org/lang/zh-CN/)[需更新]。

---

## [2.0.0] - 2026-04-04

### 新增

#### 核心功能
- **个性化学习引擎 2.0**
  - DNC（可微分神经计算机）知识追踪模型
  - 自适应难度调整系统
  - 间隔重复复习计划生成
  - 学习表现预测
  - 多维度学习分析

- **社交学习功能**
  - 学习伙伴匹配算法
  - 学习小组推荐系统
  - 协作学习竞赛系统

- **游戏化系统**
  - 徽章成就系统
  - 挑战任务系统
  - 学习进度可视化
  - 热力图展示
  - 里程碑管理

#### API端点
- `POST /api/v1/learning-engine/users/initialize` - 初始化用户学习档案
- `POST /api/v1/learning-engine/interactions/record` - 记录学习交互
- `GET /api/v1/learning-engine/users/{user_id}/next-steps` - 获取下一步学习建议
- `POST /api/v1/learning-engine/paths/generate` - 生成个性化学习路径
- `GET /api/v1/learning-engine/users/{user_id}/analytics` - 获取用户学习分析
- `GET /api/v1/learning-engine/users/{user_id}/predict/{concept_id}` - 预测学习表现
- `GET /api/v1/learning-engine/users/{user_id}/spaced-repetition` - 获取间隔重复计划

#### 搜索功能增强
- 公式搜索支持 LaTeX 结构匹配
- 多跳推理问答系统
- 搜索建议自动补全
- 搜索统计信息

#### 推荐系统增强
- A/B 测试支持
- 可解释推荐
- 用户画像分析
- 推荐系统评估

### 改进

#### 性能优化
- Redis 缓存策略优化
  - 知识图谱数据缓存TTL调整：1小时
  - 学习路径缓存TTL调整：30分钟
  - 用户进度缓存TTL调整：5分钟
- 数据库连接池优化
  - 连接池大小：20
  - 最大溢出连接：30
  - 连接回收时间：3600秒
- 响应压缩优化
  - 支持 gzip 和 brotli
  - 压缩阈值：1KB
  - 压缩级别：6

#### 错误处理
- 统一的错误响应格式
- 详细的错误码说明
- 错误ID追踪系统
- 调试模式支持

#### 文档
- 完整的 OpenAPI 3.1.0 规范
- API 使用指南
- 错误码说明文档
- 速率限制说明文档

### 变更

#### 破坏性变更
- 学习路径创建接口现在默认使用异步模式
- 任务状态查询接口响应格式更新
- 搜索接口响应结构优化

#### 废弃
- `GET /api/v1/concepts/{id}/cache` (将在 v2.1 中移除)
- 旧的推荐算法接口 (将在 v2.2 中移除)

### 修复

#### Bug修复
- 修复了知识图谱循环依赖检测问题
- 修复了异步任务状态同步延迟问题
- 修复了 Redis 连接池泄漏问题
- 修复了大数据集分页内存占用过高问题

#### 安全性
- 修复了 SQL 注入潜在风险点
- 增强了输入验证和过滤
- 更新了依赖包安全版本

---

## [1.5.0] - 2026-03-01

### 新增

#### 搜索功能
- **语义搜索服务**
  - 基于文本嵌入的语义搜索
  - 混合搜索（语义 + 关键词）
  - 向量检索系统
  - 公式搜索功能

#### API端点
- `POST /api/v1/search/search` - 执行搜索
- `GET /api/v1/search/search` - 执行搜索（GET方式）
- `POST /api/v1/search/formula` - 公式搜索
- `POST /api/v1/search/ask` - 数学问答
- `POST /api/v1/search/index` - 索引文档
- `POST /api/v1/search/index/batch` - 批量索引

#### 速率限制
- 搜索API独立速率限制：60 req/min
- 更细粒度的速率限制控制

### 改进

#### 性能
- 搜索查询性能优化
- 向量索引效率提升
- 缓存命中率优化

#### 监控
- 搜索统计信息接口
- 查询时间指标

### 修复
- 修复了搜索索引更新延迟问题
- 修复了大数据集搜索超时问题

---

## [1.4.0] - 2026-02-15

### 新增

#### 推荐系统
- **协同过滤**
  - 用户-项目协同过滤
  - 矩阵分解算法
  - 相似用户查找

- **内容推荐**
  - 基于知识图谱的推荐
  - 学习风格匹配
  - 难度适配推荐

- **混合推荐**
  - 多算法融合
  - 自适应权重
  - A/B测试框架

#### API端点
- `POST /api/v1/recommendations/recommend` - 获取推荐
- `POST /api/v1/recommendations/feedback` - 提交反馈
- `POST /api/v1/recommendations/similar-users` - 查找相似用户
- `GET /api/v1/recommendations/explain/{user_id}/{concept_id}` - 推荐解释

### 改进

#### 数据模型
- 用户画像模型
- 概念嵌入模型
- 推荐历史记录

#### 算法
- 推荐算法性能优化
- 冷启动问题处理

---

## [1.3.0] - 2026-01-20

### 新增

#### 异步任务系统
- **Celery 集成**
  - 分布式任务队列
  - 任务状态追踪
  - 任务撤销功能
  - Worker 状态监控

#### API端点
- `GET /api/v1/tasks/{task_id}` - 获取任务状态
- `GET /api/v1/tasks/{task_id}/result` - 获取任务结果
- `GET /api/v1/tasks/{task_id}/progress` - 获取任务进度
- `POST /api/v1/tasks/{task_id}/revoke` - 撤销任务
- `GET /api/v1/tasks` - 列出活跃任务
- `GET /api/v1/tasks/workers/status` - Worker状态

#### 学习路径
- 异步路径计算
- 路径优化功能
- 批量路径处理

### 改进

#### 性能
- 耗时操作异步化
- 任务队列优化
- 资源利用率提升

#### 可靠性
- 任务重试机制
- 失败任务处理
- 任务超时控制

---

## [1.2.0] - 2025-12-10

### 新增

#### 缓存系统
- **Redis 集成**
  - 连接池管理
  - 自动序列化
  - 缓存键管理
  - TTL 控制

#### 中间件
- 响应压缩中间件（gzip/brotli）
- ETag 缓存控制
- Cache-Control 管理
- 速率限制中间件

#### API端点
- `GET /api/v1/health/redis` - Redis健康检查
- `GET /api/v1/health/celery` - Celery健康检查
- `GET /api/v1/health/pool` - 连接池状态

### 改进

#### 性能
- 知识图谱查询缓存
- 概念信息缓存
- 学习路径缓存
- 用户进度缓存

#### 稳定性
- 数据库连接池监控
- 缓存失效策略
- 降级处理机制

---

## [1.1.0] - 2025-11-15

### 新增

#### 知识图谱
- **概念管理**
  - 概念CRUD操作
  - 概念关系查询
  - 前置依赖递归查询
  - 图谱统计分析

- **学习路径**
  - 路径创建
  - 路径查询
  - 进度更新
  - 资源推荐

#### API端点
- `GET /api/v1/concepts` - 概念列表
- `GET /api/v1/concepts/{id}` - 概念详情
- `GET /api/v1/concepts/{id}/relations` - 概念关系
- `GET /api/v1/concepts/{id}/prerequisites` - 前置依赖
- `GET /api/v1/graph/stats` - 图谱统计
- `POST /api/v1/learning-paths` - 创建路径
- `GET /api/v1/learning-paths/user/{user_id}` - 用户路径
- `GET /api/v1/learning-paths/{id}` - 路径详情

### 改进

#### 分页
- 通用分页系统
- 游标分页支持
- 大数据集优化

#### 过滤
- 多条件过滤
- 全文搜索
- 排序支持

---

## [1.0.0] - 2025-10-01

### 新增

#### 核心架构
- **FastAPI 框架**
  - 异步处理支持
  - 自动API文档生成
  - 数据验证
  - 依赖注入

- **数据库**
  - SQLAlchemy ORM
  - 连接池管理
  - 数据库迁移

- **健康检查**
  - 基础健康检查
  - 详细系统状态
  - 数据库健康检查

#### API端点
- `GET /` - 服务信息
- `GET /health` - 健康检查
- `GET /docs` - Swagger文档
- `GET /redoc` - ReDoc文档

### 特性

#### 基础功能
- RESTful API设计
- JSON数据格式
- HTTP状态码规范
- 错误处理机制

#### 开发支持
- 自动重载
- 调试模式
- 日志系统
- 配置管理

---

## 版本说明

### 版本号规则

版本格式：`MAJOR.MINOR.PATCH`

- **MAJOR**：不兼容的API更改
- **MINOR**：向后兼容的功能添加
- **PATCH**：向后兼容的问题修复

### 支持政策

| 版本 | 状态 | 支持截止日期 |
|-----|------|------------|
| 2.0.x | 活跃 | 2027-04-04 |
| 1.5.x | 维护 | 2026-10-01 |
| 1.4.x | 维护 | 2026-08-01 |
| < 1.4 | 终止 | - |

### 升级指南

#### 从 1.x 升级到 2.0

1. 更新API调用代码，处理新的响应格式
2. 迁移到异步任务模式（如果尚未使用）
3. 更新错误处理逻辑
4. 测试所有集成点

详细升级指南：UPGRADE_GUIDE.md

---

## 未发布

### 计划中的功能

#### 版本 2.1.0 (预计 2026-06)
- [ ] 多语言支持
- [ ] 实时协作功能
- [ ] 移动端API优化
- [ ] GraphQL 支持

#### 版本 2.2.0 (预计 2026-09)
- [ ] 机器学习模型自动训练
- [ ] 知识图谱可视化API
- [ ] 高级分析报告
- [ ] Webhook 支持

#### 版本 3.0.0 (预计 2027-01)
- [ ] 微服务架构迁移
- [ ] gRPC 支持
- [ ] 分布式事务
- [ ] 多租户支持

---

## 贡献

感谢所有为 FormalMath API 做出贡献的开发者！

### 贡献者
- 核心团队
- 社区贡献者
- 测试反馈者

### 提交变更

如果您想提交变更到变更日志，请遵循以下格式：

```markdown
### 新增/改进/修复/变更/废弃/移除/安全性
- 简短描述 (#PR编号)
```

---

## 参考

- [API文档](docs/API_GUIDE.md)
- [错误码说明](docs/ERROR_CODES.md)
- [速率限制说明](docs/RATE_LIMIT.md)
- 贡献指南

---

**注**：本变更日志可能不完整，对于详细的提交历史，请参考 Git 提交记录。
