---
title: FormalMath API v2.0
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API v2.0

高性能FastAPI后端服务，为FormalMath提供知识图谱查询、学习路径生成、认知诊断等功能。

## 特性

- ⚡ **高性能缓存** - Redis缓存层，自动缓存热点数据
- 🔄 **数据库连接池** - SQLAlchemy连接池，优化数据库访问
- 📬 **异步任务队列** - Celery处理耗时操作（路径计算、诊断分析）
- 🗜️ **响应压缩** - 支持gzip和brotli压缩
- 🏷️ **HTTP缓存** - ETag和Cache-Control支持
- 📄 **分页支持** - 大数据集分页查询

## 快速开始

### 安装依赖

```bash
cd FormalMath-Enhanced/api
pip install -r requirements.txt
```

### 配置环境变量

```bash
cp .env.example .env
# 编辑 .env 文件，配置Redis和数据库连接
```

### 启动服务

```bash
# 1. 启动API服务
uvicorn main:app --reload

# 2. 启动Redis（需要本地安装或Docker）
redis-server

# 3. 启动Celery Worker（另一个终端）
python celery_worker.py

# 或使用Celery命令
celery -A app.tasks.celery_app worker --loglevel=info
```

### 访问API文档

- **Swagger UI**: http://localhost:8000/docs
- **ReDoc**: http://localhost:8000/redoc
- **OpenAPI JSON**: http://localhost:8000/openapi.json

## 文档目录

- [API使用指南](docs/API_GUIDE.md) - 完整的API使用示例和最佳实践
- [错误码说明](docs/ERROR_CODES.md) - 详细的错误码参考
- [速率限制说明](docs/RATE_LIMIT.md) - 速率限制规则和限制
- [变更日志](CHANGELOG.md) - API版本变更历史

## API端点

### 健康检查

```
GET /health              # 基础健康检查
GET /health/detailed     # 详细系统状态
GET /health/database     # 数据库状态
GET /health/redis        # Redis状态
```

### 知识图谱

```
GET /api/v1/concepts                    # 概念列表（分页）
GET /api/v1/concepts/{id}               # 概念详情
GET /api/v1/concepts/{id}/relations     # 概念关系
GET /api/v1/concepts/{id}/prerequisites # 前置依赖
GET /api/v1/graph/stats                 # 图谱统计
```

### 学习路径

```
POST /api/v1/learning-paths              # 创建学习路径（异步）
GET /api/v1/learning-paths/user/{id}     # 用户路径列表
GET /api/v1/learning-paths/{id}          # 路径详情
POST /api/v1/learning-paths/{id}/optimize # 优化路径
PUT /api/v1/learning-paths/{id}/progress # 更新进度
```

### 异步任务

```
GET /api/v1/tasks/{task_id}           # 任务状态
GET /api/v1/tasks/{task_id}/result    # 任务结果
GET /api/v1/tasks/{task_id}/progress  # 任务进度
POST /api/v1/tasks/{task_id}/revoke   # 取消任务
GET /api/v1/tasks/workers/status      # Worker状态
```

## 性能测试

```bash
# 运行性能测试
python tests/test_performance.py

# 或使用pytest
pytest tests/test_performance.py -v
```

## 项目结构

```
api/
├── app/
│   ├── api/              # API路由
│   │   ├── router.py
│   │   ├── health.py
│   │   ├── knowledge_graph.py
│   │   ├── learning_path.py
│   │   └── tasks.py
│   ├── cache/            # Redis缓存层
│   │   └── redis_cache.py
│   ├── core/             # 核心配置
│   │   ├── config.py
│   │   └── database.py
│   ├── middleware/       # 中间件
│   │   ├── compression.py
│   │   └── etag.py
│   ├── models/           # 数据模型
│   │   └── models.py
│   ├── services/         # 服务层
│   │   ├── pagination.py
│   │   └── task_status.py
│   └── tasks/            # Celery任务
│       ├── celery_app.py
│       ├── path_tasks.py
│       ├── diagnosis_tasks.py
│       └── graph_tasks.py
├── tests/                # 测试
├── main.py               # 应用入口
├── celery_worker.py      # Celery Worker启动
├── celery_beat.py        # Celery Beat启动
├── requirements.txt
└── .env.example
```

## 环境变量

| 变量名 | 说明 | 默认值 |
|-------|------|-------|
| REDIS_HOST | Redis主机 | localhost |
| REDIS_PORT | Redis端口 | 6379 |
| DATABASE_URL | 数据库连接URL | sqlite:///./formalmath.db |
| CELERY_BROKER_URL | Celery Broker | redis://localhost:6379/1 |
| DATABASE_POOL_SIZE | 连接池大小 | 20 |
| CACHE_TTL_KNOWLEDGE_GRAPH | 知识图谱缓存TTL | 3600 |

## 性能优化详情

### 缓存策略

| 数据类型 | TTL | 策略 |
|---------|-----|------|
| 知识图谱 | 1小时 | 全量缓存 |
| 学习路径 | 30分钟 | 用户级别缓存 |
| 用户进度 | 5分钟 | 短TTL保证实时性 |
| 概念信息 | 2小时 | 长期缓存 |

### 数据库索引

- `idx_learning_path_user_status` - 加速用户路径查询
- `idx_kg_node_branch_difficulty` - 加速概念过滤
- `idx_user_progress_user_concept` - 加速进度查询

## 贡献

请遵循项目的代码风格和提交规范。

## 许可证

MIT License
