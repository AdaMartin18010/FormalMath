# FormalMath API 速率限制说明

## 概述

为确保API服务的稳定性和公平性，FormalMath API 实施了速率限制策略。本文档详细说明速率限制规则、响应头信息以及处理建议。

---

## 速率限制规则

### 按端点类型分类

| 端点类型 | 限制 | 时间窗口 | 突发容量 |
|---------|------|---------|---------|
| **一般API** | 120 请求/分钟 | 60秒 | 20 |
| **搜索API** | 60 请求/分钟 | 60秒 | 10 |
| **异步任务API** | 30 请求/分钟 | 60秒 | 5 |
| **学习引擎API** | 60 请求/分钟 | 60秒 | 10 |
| **推荐API** | 60 请求/分钟 | 60秒 | 10 |
| **认证API** | 10 请求/分钟 | 60秒 | 3 |
| **健康检查** | 无限制 | - | - |
| **文档端点** | 无限制 | - | - |

### 端点分类详情

#### 一般API (120 req/min)
- `GET /api/v1/concepts`
- `GET /api/v1/concepts/{id}`
- `GET /api/v1/graph/stats`
- `GET /api/v1/learning-paths/*`
- 所有未列出的端点

#### 搜索API (60 req/min)
- `POST /api/v1/search/search`
- `GET /api/v1/search/search`
- `POST /api/v1/search/formula`
- `POST /api/v1/search/ask`
- `GET /api/v1/search/suggest`

#### 异步任务API (30 req/min)
- `POST /api/v1/learning-paths` (创建路径)
- `POST /api/v1/learning-paths/{id}/optimize`
- `POST /api/v1/search/index`
- `POST /api/v1/search/index/batch`

#### 学习引擎API (60 req/min)
- `POST /api/v1/learning-engine/interactions/record`
- `GET /api/v1/learning-engine/users/{id}/*`
- `POST /api/v1/learning-engine/paths/generate`

#### 推荐API (60 req/min)
- `POST /api/v1/recommendations/recommend`
- `POST /api/v1/recommendations/feedback`

#### 认证API (10 req/min)
- 登录/注册端点
- 令牌刷新端点

#### 无限制
- `GET /health`
- `GET /health/*`
- `GET /docs`
- `GET /redoc`
- `GET /openapi.json`

---

## 响应头信息

每个API响应都包含速率限制相关的HTTP头：

### 标准响应头

| 响应头 | 说明 | 示例 |
|-------|------|------|
| `X-RateLimit-Limit` | 当前端点的请求限制 | `120` |
| `X-RateLimit-Remaining` | 当前窗口剩余请求数 | `119` |
| `X-RateLimit-Reset` | 窗口重置时间（Unix时间戳） | `1649088600` |
| `X-RateLimit-Window` | 窗口大小（秒） | `60` |

### 超过限制时的响应头

当请求超过速率限制时，响应包含：

| 响应头 | 说明 | 示例 |
|-------|------|------|
| `Retry-After` | 建议重试等待时间（秒） | `45` |
| `X-RateLimit-Limit` | 限制数 | `120` |
| `X-RateLimit-Remaining` | 剩余数（始终为0） | `0` |
| `X-RateLimit-Reset` | 重置时间 | `1649088645` |

### 响应示例

#### 正常请求
```http
HTTP/1.1 200 OK
Content-Type: application/json
X-RateLimit-Limit: 120
X-RateLimit-Remaining: 119
X-RateLimit-Reset: 1649088600
X-RateLimit-Window: 60

{...}
```

#### 超过限制
```http
HTTP/1.1 429 Too Many Requests
Content-Type: application/json
Retry-After: 45
X-RateLimit-Limit: 120
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1649088645

{
  "success": false,
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "请求过于频繁，请稍后再试",
    "error_id": "abc123de",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "limit": 120,
      "window": "1m",
      "retry_after": 45
    }
  }
}
```

---

## 速率限制算法

### 令牌桶算法

FormalMath API 使用**令牌桶算法**实现速率限制：

```
+-----------+     匀速添加令牌     +--------+
|   令牌桶   | <------------------ | 令牌源 |
|  (容量N)  |                     +--------+
+-----+-----+
      |
      | 消耗令牌
      v
+-----------+
|   请求    |
+-----------+
```

**特点**：
- 允许短时间的突发流量（突发容量）
- 长期请求率保持恒定
- 令牌以固定速率补充

### 算法参数

| 参数 | 一般API | 搜索API | 任务API |
|-----|--------|--------|--------|
| 令牌添加速率 | 2/秒 | 1/秒 | 0.5/秒 |
| 桶容量 | 20 | 10 | 5 |
| 时间窗口 | 60秒 | 60秒 | 60秒 |

---

## 多维度限制

### 按API密钥限制

每个API密钥有独立的速率限制计数器。

### 按IP地址限制

未认证的请求按IP地址限制：
- 限制：30 请求/分钟
- 目的：防止匿名滥用

### 按用户限制

已认证的请求按用户ID限制：
- 限制：继承端点类型限制
- 目的：防止单个用户占用过多资源

### 组合规则

系统同时应用多个维度的限制：

```
总限制 = min(API密钥限制, 用户限制, IP限制)
```

---

## 客户端处理建议

### 1. 读取响应头

始终检查并记录速率限制响应头：

```python
import requests
import time

def make_request(url, **kwargs):
    response = requests.get(url, **kwargs)
    
    # 记录速率限制信息
    limit = response.headers.get('X-RateLimit-Limit')
    remaining = response.headers.get('X-RateLimit-Remaining')
    reset_time = response.headers.get('X-RateLimit-Reset')
    
    print(f"Rate limit: {remaining}/{limit}, reset at {reset_time}")
    
    return response
```

### 2. 处理 429 响应

当收到 429 状态码时，遵循 `Retry-After` 头：

```python
def make_request_with_retry(url, **kwargs):
    max_retries = 3
    retries = 0
    
    while retries < max_retries:
        response = requests.get(url, **kwargs)
        
        if response.status_code == 429:
            retry_after = int(response.headers.get('Retry-After', 60))
            print(f"Rate limited. Waiting {retry_after} seconds...")
            time.sleep(retry_after)
            retries += 1
            continue
        
        return response
    
    raise Exception("Max retries exceeded")
```

### 3. 预防性速率限制

在客户端实现预防性速率限制：

```python
import time
from collections import deque
from threading import Lock

class RateLimiter:
    def __init__(self, max_requests, window_seconds):
        self.max_requests = max_requests
        self.window_seconds = window_seconds
        self.requests = deque()
        self.lock = Lock()
    
    def acquire(self):
        with self.lock:
            now = time.time()
            
            # 移除窗口外的请求记录
            while self.requests and self.requests[0] < now - self.window_seconds:
                self.requests.popleft()
            
            # 检查是否超过限制
            if len(self.requests) >= self.max_requests:
                sleep_time = self.requests[0] + self.window_seconds - now
                if sleep_time > 0:
                    time.sleep(sleep_time)
                    return self.acquire()
            
            self.requests.append(now)

# 使用示例
limiter = RateLimiter(max_requests=100, window_seconds=60)

for url in urls:
    limiter.acquire()
    response = requests.get(url)
```

### 4. 指数退避策略

```python
def exponential_backoff_retry(func, max_retries=5):
    """指数退避重试"""
    for attempt in range(max_retries):
        try:
            return func()
        except RateLimitError as e:
            if attempt == max_retries - 1:
                raise
            
            # 计算退避时间：2^attempt 秒
            wait_time = 2 ** attempt
            print(f"Attempt {attempt + 1} failed. Waiting {wait_time}s...")
            time.sleep(wait_time)
```

### 5. 批量请求优化

使用批量接口减少请求次数：

```python
# 不推荐：逐个请求
for concept_id in concept_ids:
    response = requests.get(f"/api/v1/concepts/{concept_id}")

# 推荐：使用搜索批量获取
response = requests.get("/api/v1/concepts", params={
    "search": " ".join(concept_ids),
    "page_size": 100
})
```

### 6. 缓存响应

缓存频繁访问的数据：

```python
import functools
import requests

cache = {}

def cached_request(url, ttl=300):
    """带TTL的简单缓存"""
    if url in cache:
        result, timestamp = cache[url]
        if time.time() - timestamp < ttl:
            return result
    
    response = requests.get(url)
    cache[url] = (response, time.time())
    return response
```

---

## 特殊情况处理

### WebSocket 连接

WebSocket连接有独立的限制：
- 每API密钥最多10个并发连接
- 每连接每秒最多100条消息

### 批量操作

批量端点（如 `/search/index/batch`）的速率限制基于：
- 请求数限制：30 req/min
- 文档数限制：1000 docs/min

### 长时间运行任务

异步任务的创建受速率限制，但任务的执行不受限制。

---

## 监控和告警

### API端点

获取当前速率限制状态：

```bash
curl http://localhost:8000/api/v1/health/rate-limit
```

响应：
```json
{
  "limits": {
    "general": {
      "limit": 120,
      "window": 60,
      "current_usage": 45
    },
    "search": {
      "limit": 60,
      "window": 60,
      "current_usage": 12
    }
  },
  "reset_at": "2026-04-04T15:31:00Z"
}
```

### 最佳实践

1. **提前告警**: 当使用率达到80%时记录警告日志
2. **熔断机制**: 连续收到多个429响应时，暂停请求一段时间
3. **降级策略**: 当API不可用时，切换到备用方案或缓存数据

---

## 联系支持

如果您需要提高速率限制，请联系 support@formalmath.org，并提供以下信息：

1. API密钥或用户ID
2. 当前使用场景和预估流量
3. 需要的限制值
4. 业务需求说明

---

## 更新日志

| 日期 | 版本 | 变更 |
|-----|------|------|
| 2026-04-04 | 2.0.0 | 初始版本，实施新的速率限制策略 |
| 2026-03-01 | 1.5.0 | 添加搜索API单独限制 |
| 2026-01-15 | 1.0.0 | 基础速率限制实现 |
