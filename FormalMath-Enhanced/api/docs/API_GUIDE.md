---
title: FormalMath API 使用指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API 使用指南

## 目录

- [快速开始](#快速开始)
- [认证](#认证)
- [API使用示例](#api使用示例)
  - [健康检查](#健康检查)
  - [知识图谱](#知识图谱)
  - [学习路径](#学习路径)
  - [异步任务](#异步任务)
  - [语义搜索](#语义搜索)
  - [推荐系统](#推荐系统)
  - [个性化学习引擎](#个性化学习引擎)
- [错误处理](#错误处理)
- [速率限制](#速率限制)
- [分页](#分页)
- [最佳实践](#最佳实践)

---

## 快速开始

### 基础URL

```
生产环境: https://api.formalmath.org/api/v1[需更新]
本地环境: 
```

### 请求格式

所有请求和响应均使用 JSON 格式。请确保请求头中包含：

```
Content-Type: application/json
Accept: application/json
```

### API文档端点

- **Swagger UI**: 
- **ReDoc**: 
- **OpenAPI JSON**: 

---

## 认证

### Bearer Token (JWT)

在请求头中包含认证令牌：

```bash
curl -H "Authorization: Bearer YOUR_JWT_TOKEN" \
     https://api.formalmath.org/api/v1/concepts[需更新]
```

### API Key

```bash
curl -H "X-API-Key: YOUR_API_KEY" \
     https://api.formalmath.org/api/v1/concepts[需更新]
```

---

## API使用示例

### 健康检查

#### 基础健康检查

```bash
curl 
```

响应：
```json
{
  "status": "healthy",
  "timestamp": "2026-04-04T15:30:00Z",
  "version": "2.0.0"
}
```

#### 详细系统状态

```bash
curl 
```

响应：
```json
{
  "api": {
    "status": "healthy",
    "timestamp": "2026-04-04T15:30:00Z"
  },
  "database": {
    "status": "healthy",
    "pool": {
      "size": 20,
      "checked_in": 18,
      "checked_out": 2
    }
  },
  "redis": {
    "status": "healthy",
    "version": "7.0.0",
    "used_memory_human": "1.5M",
    "connected_clients": 10
  },
  "celery": {
    "status": "healthy",
    "task_id": "abc123",
    "broker_url": "redis://localhost:6379/1"
  }
}
```

---

### 知识图谱

#### 获取概念列表

```bash
# 基础请求
curl ""

# 带过滤条件
curl ""

# 搜索
curl ""
```

响应：
```json
{
  "items": [
    {
      "id": "linear_algebra",
      "name": "线性代数",
      "branch": "algebra",
      "difficulty": "intermediate",
      "description": "研究向量空间和线性映射的数学分支",
      "prerequisites": ["matrices", "vector_spaces"]
    }
  ],
  "total": 150,
  "page": 1,
  "page_size": 10,
  "pages": 15,
  "has_next": true,
  "has_prev": false
}
```

#### 获取概念详情

```bash
curl 
```

响应：
```json
{
  "id": "linear_algebra",
  "name": "线性代数",
  "branch": "algebra",
  "difficulty": "intermediate",
  "description": "研究向量空间和线性映射的数学分支",
  "prerequisites": ["matrices", "vector_spaces"]
}
```

#### 获取概念关系

```bash
# 获取所有关系
curl 

# 仅入边
curl ""

# 按类型过滤
curl ""
```

响应：
```json
{
  "concept_id": "linear_algebra",
  "relations": [
    {
      "id": "rel_001",
      "source": "matrices",
      "target": "linear_algebra",
      "type": "prerequisite",
      "weight": 0.9
    }
  ],
  "count": 1
}
```

#### 获取前置依赖（递归）

```bash
# 获取直接前置依赖
curl 

# 获取多级前置依赖（深度为3）
curl ""
```

响应：
```json
{
  "concept_id": "linear_algebra",
  "concept_name": "线性代数",
  "prerequisites": [
    {
      "id": "matrices",
      "name": "矩阵",
      "difficulty": "basic",
      "level": 1,
      "prerequisites": [
        {
          "id": "vectors",
          "name": "向量",
          "difficulty": "basic",
          "level": 2
        }
      ]
    }
  ],
  "total_count": 2
}
```

#### 获取图谱统计

```bash
# 全部统计
curl 

# 按分支统计
curl ""
```

响应：
```json
{
  "total_nodes": 10000,
  "total_edges": 25000,
  "branches": {
    "algebra": 3000,
    "geometry": 2500,
    "analysis": 2000,
    "topology": 1500,
    "number_theory": 1000
  },
  "difficulty_distribution": {
    "basic": 3000,
    "intermediate": 4000,
    "advanced": 2500,
    "research": 500
  }
}
```

---

### 学习路径

#### 创建学习路径

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": 123,
    "target_concepts": ["linear_algebra", "matrix_theory"],
    "algorithm": "astar",
    "constraints": {
      "max_time": 3600,
      "difficulty_range": [0.3, 0.8]
    },
    "async_mode": true
  }'
```

响应：
```json
{
  "task_id": "abc123-def456-ghi789",
  "status": "queued",
  "message": "学习路径计算任务已提交，请通过任务状态接口查询结果"
}
```

#### 获取用户学习路径列表

```bash
# 全部路径
curl 

# 按状态过滤
curl ""
```

响应：
```json
[
  {
    "id": 1,
    "user_id": 123,
    "name": "线性代数学习路径",
    "status": "active",
    "nodes_count": 15,
    "estimated_duration": 3600,
    "created_at": "2026-04-04T10:00:00Z"
  }
]
```

#### 获取学习路径详情

```bash
curl 
```

响应：
```json
{
  "id": 1,
  "user_id": 123,
  "name": "线性代数学习路径",
  "status": "active",
  "nodes_count": 15,
  "estimated_duration": 3600,
  "created_at": "2026-04-04T10:00:00Z",
  "nodes": [
    {
      "concept_id": "vectors",
      "name": "向量",
      "difficulty": "basic",
      "estimated_time": 200
    }
  ],
  "difficulty_distribution": {
    "basic": 5,
    "intermediate": 8,
    "advanced": 2
  }
}
```

#### 优化学习路径

```bash
curl -X POST ""
```

响应：
```json
{
  "task_id": "xyz789-abc123-def456",
  "status": "queued",
  "message": "路径优化任务已提交"
}
```

#### 更新学习进度

```bash
curl -X PUT ""
```

响应：
```json
{
  "path_id": 1,
  "completed_nodes": 5,
  "total_nodes": 15,
  "progress_percentage": 33.33,
  "status": "active"
}
```

---

### 异步任务

#### 获取任务状态

```bash
curl 
```

响应：
```json
{
  "task_id": "abc123-def456-ghi789",
  "state": "SUCCESS",
  "status": "completed",
  "result": {
    "path_id": 1,
    "nodes_count": 15
  },
  "error": null,
  "progress": 100,
  "message": "任务完成",
  "date_done": "2026-04-04T10:05:00Z",
  "runtime": 120.5
}
```

#### 获取任务结果

```bash
curl 
```

响应：
```json
{
  "task_id": "abc123-def456-ghi789",
  "state": "SUCCESS",
  "result": {
    "path_id": 1,
    "nodes_count": 15,
    "path_data": {...}
  }
}
```

#### 获取任务进度

```bash
curl 
```

响应：
```json
{
  "task_id": "abc123-def456-ghi789",
  "state": "PROGRESS",
  "progress": 75,
  "message": "正在计算最优路径..."
}
```

#### 撤销任务

```bash
# 正常撤销
curl -X POST 

# 强制终止
curl -X POST ""
```

响应：
```json
{
  "task_id": "abc123-def456-ghi789",
  "action": "revoked",
  "terminated": false,
  "message": "任务已撤销"
}
```

#### 获取Worker状态

```bash
curl 
```

响应：
```json
{
  "workers": [
    {
      "name": "celery@worker1",
      "status": "online",
      "active_tasks": 2,
      "processed": 1000,
      "prefetch_count": 4,
      "concurrency": 4
    }
  ],
  "total_workers": 1,
  "online_workers": 1
}
```

---

### 语义搜索

#### 执行搜索

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "query": "线性代数的基本定理",
    "search_type": "hybrid",
    "k": 10,
    "rerank": true
  }'
```

响应：
```json
{
  "success": true,
  "data": {
    "results": [
      {
        "document": {
          "id": "doc_001",
          "content": "线性代数基本定理...",
          "metadata": {
            "concept": "linear_algebra",
            "difficulty": "intermediate"
          }
        },
        "score": 0.95,
        "search_type": "semantic"
      }
    ],
    "total": 25,
    "search_type": "hybrid",
    "query_time_ms": 125.5,
    "facets": {
      "difficulty": {
        "basic": 5,
        "intermediate": 15,
        "advanced": 5
      }
    }
  }
}
```

#### 公式搜索

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "latex": "E = mc^2",
    "k": 10,
    "match_type": "all"
  }'
```

响应：
```json
{
  "success": true,
  "data": {
    "query": "E = mc^2",
    "results": [
      {
        "formula_id": "formula_001",
        "latex": "E = mc^2",
        "similarity": 1.0,
        "source": "相对论基础"
      }
    ],
    "total": 1
  }
}
```

#### 数学问答

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "question": "什么是特征值？",
    "use_multi_hop": true
  }'
```

响应：
```json
{
  "success": true,
  "data": {
    "answer": "特征值是线性代数中的重要概念...",
    "sources": [
      {
        "document_id": "doc_001",
        "relevance": 0.95
      }
    ],
    "confidence": 0.92
  }
}
```

---

### 推荐系统

#### 获取个性化推荐

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": 123,
    "n_recommendations": 10,
    "recommendation_type": "hybrid"
  }'
```

响应：
```json
{
  "user_id": 123,
  "recommendations": [
    {
      "concept_id": "eigenvalues",
      "name": "特征值",
      "branch": "algebra",
      "score": 0.92,
      "explanation": "基于您的学习历史和知识掌握情况推荐",
      "confidence": 0.88,
      "component_scores": {
        "collaborative": 0.85,
        "knowledge_graph": 0.90,
        "content": 0.88
      }
    }
  ],
  "total_count": 10,
  "recommendation_type": "hybrid"
}
```

#### 提交推荐反馈

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": 123,
    "concept_id": "eigenvalues",
    "reward": 0.9,
    "action": "study",
    "metrics": {
      "time_spent": 300,
      "completion_rate": 0.95
    }
  }'
```

---

### 个性化学习引擎

#### 初始化用户

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": "user_123",
    "initial_assessment": {
      "math_level": "intermediate",
      "preferred_branches": ["algebra", "geometry"]
    }
  }'
```

#### 记录学习交互

```bash
curl -X POST  \
  -H "Content-Type: application/json" \
  -d '{
    "user_id": "user_123",
    "concept_id": "linear_algebra",
    "interaction_type": "exercise",
    "result": {
      "correct": true,
      "time_spent": 120,
      "difficulty": 0.7
    },
    "context": {
      "session_id": "session_001"
    }
  }'
```

#### 获取下一步学习建议

```bash
curl ""
```

响应：
```json
{
  "user_id": "user_123",
  "suggestions": [
    {
      "concept_id": "eigenvalues",
      "name": "特征值",
      "priority": "high",
      "reason": "基于知识追踪模型，您已准备好学习此概念",
      "estimated_time": 300
    }
  ]
}
```

#### 获取用户学习分析

```bash
curl 
```

响应：
```json
{
  "user_id": "user_123",
  "knowledge_state": {
    "mastered": ["vectors", "matrices"],
    "learning": ["linear_algebra"],
    "weak": ["determinants"]
  },
  "forgetting_curve": {
    "needs_review": ["calculus"],
    "next_review_date": "2026-04-07T10:00:00Z"
  },
  "learning_velocity": 1.2,
  "recommended_difficulty": 0.65
}
```

---

## 错误处理

### 错误响应格式

所有错误响应使用统一格式：

```json
{
  "success": false,
  "error": {
    "code": "ERROR_CODE",
    "message": "错误描述",
    "error_id": "abc123",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {...}
  }
}
```

### 常见错误码

| HTTP状态码 | 错误码 | 说明 | 处理建议 |
|-----------|-------|------|---------|
| 400 | BAD_REQUEST | 请求格式错误 | 检查请求参数 |
| 401 | AUTHENTICATION_ERROR | 认证失败 | 检查认证令牌 |
| 403 | AUTHORIZATION_ERROR | 权限不足 | 检查用户权限 |
| 404 | NOT_FOUND | 资源不存在 | 检查资源ID |
| 422 | VALIDATION_ERROR | 参数验证失败 | 检查请求体格式 |
| 429 | RATE_LIMIT_EXCEEDED | 请求过于频繁 | 稍后重试，降低请求频率 |
| 500 | INTERNAL_ERROR | 服务器内部错误 | 联系技术支持 |
| 503 | DATABASE_ERROR | 数据库错误 | 稍后重试 |
| 504 | GATEWAY_TIMEOUT | 查询超时 | 简化查询或稍后重试 |

---

## 速率限制

### 限制规则

| 端点类型 | 限制 | 窗口 |
|---------|------|-----|
| 一般API | 120 请求/分钟 | 60秒 |
| 搜索API | 60 请求/分钟 | 60秒 |
| 异步任务 | 30 请求/分钟 | 60秒 |
| 健康检查 | 无限制 | - |

### 响应头

速率限制信息包含在响应头中：

```
X-RateLimit-Limit: 120
X-RateLimit-Remaining: 119
X-RateLimit-Reset: 1649088600
```

### 超过限制

当超过速率限制时，返回 429 状态码：

```json
{
  "success": false,
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "请求过于频繁，请稍后再试",
    "error_id": "abc123",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "retry_after": 60
    }
  }
}
```

响应头：
```
Retry-After: 60
```

---

## 分页

### 分页参数

| 参数 | 类型 | 默认值 | 说明 |
|-----|------|-------|------|
| page | integer | 1 | 页码，从1开始 |
| page_size | integer | 20 | 每页数量，最大100 |

### 分页响应

```json
{
  "items": [...],
  "total": 1000,
  "page": 1,
  "page_size": 20,
  "pages": 50,
  "has_next": true,
  "has_prev": false
}
```

### 遍历所有页面

```python
import requests

all_items = []
page = 1

while True:
    response = requests.get(
        "",
        params={"page": page, "page_size": 100}
    )
    data = response.json()
    
    all_items.extend(data["items"])
    
    if not data["has_next"]:
        break
    
    page += 1
```

---

## 最佳实践

### 1. 使用异步任务处理耗时操作

对于计算密集型的操作（如学习路径生成），始终使用异步模式：

```python
# 提交异步任务
response = requests.post("/api/v1/learning-paths", json={
    "user_id": 123,
    "target_concepts": [...],
    "async_mode": True  # 始终使用异步模式
})

task_id = response.json()["task_id"]

# 轮询任务状态
while True:
    status = requests.get(f"/api/v1/tasks/{task_id}").json()
    
    if status["state"] == "SUCCESS":
        result = requests.get(f"/api/v1/tasks/{task_id}/result").json()
        break
    elif status["state"] == "FAILURE":
        raise Exception(f"任务失败: {status['error']}")
    
    time.sleep(1)
```

### 2. 合理使用缓存

知识图谱数据通常变化不频繁，可以充分利用缓存：

```python
# 使用条件请求
response = requests.get(
    "/api/v1/concepts/linear_algebra",
    headers={"If-None-Match": cached_etag}
)

if response.status_code == 304:
    # 使用缓存数据
    pass
```

### 3. 错误重试策略

实现指数退避重试：

```python
import time
from functools import wraps

def retry_with_backoff(max_retries=3, backoff_factor=1):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            retries = 0
            while retries < max_retries:
                try:
                    return func(*args, **kwargs)
                except requests.exceptions.RequestException as e:
                    retries += 1
                    if retries == max_retries:
                        raise
                    
                    wait_time = backoff_factor * (2 ** retries)
                    time.sleep(wait_time)
            return None
        return wrapper
    return decorator

@retry_with_backoff(max_retries=3)
def fetch_concept(concept_id):
    return requests.get(f"/api/v1/concepts/{concept_id}")
```

### 4. 批量操作

尽可能使用批量接口减少请求次数：

```python
# 不推荐：逐个索引
for doc in documents:
    requests.post("/api/v1/search/index", json=doc)

# 推荐：批量索引
requests.post("/api/v1/search/index/batch", json={
    "documents": documents
})
```

### 5. 连接池

使用连接池提高性能：

```python
from requests import Session

session = Session()
adapter = requests.adapters.HTTPAdapter(
    pool_connections=10,
    pool_maxsize=100
)
session.mount('https://', adapter)
session.mount('http://', adapter)

# 使用 session 发送请求
response = session.get("")
```

---

## SDK和客户端

### Python

```bash
pip install formalmath-sdk
```

```python
from formalmath import Client

client = Client(api_key="your_api_key")

# 搜索概念
concepts = client.concepts.list(branch="algebra", page_size=10)

# 创建学习路径
task = client.learning_paths.create(
    user_id=123,
    target_concepts=["linear_algebra"]
)

# 等待任务完成
path = task.wait_for_completion()
```

### JavaScript/TypeScript

```bash
npm install @formalmath/api-client
```

```typescript
import { FormalMathClient } from '@formalmath/api-client';

const client = new FormalMathClient({
  apiKey: 'your_api_key'
});

// 搜索概念
const concepts = await client.concepts.list({
  branch: 'algebra',
  pageSize: 10
});

// 创建学习路径
const task = await client.learningPaths.create({
  userId: 123,
  targetConcepts: ['linear_algebra']
});
```

---

## 支持和反馈

- **API文档**: https://docs.formalmath.org/api[需更新]
- **问题反馈**: https://github.com/formalmath/api/issues
- **技术支持**: support@formalmath.org
