---
title: FormalMath API 错误码说明
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath API 错误码说明

## 概述

本文档详细说明 FormalMath API 中使用的所有错误码，包括错误原因、处理建议和相关示例。

---

## 错误响应格式

所有API错误响应遵循统一格式：

```json
{
  "success": false,
  "error": {
    "code": "ERROR_CODE",
    "message": "用户友好的错误描述",
    "error_id": "abc123de",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      // 额外的错误详情
    }
  }
}
```

### 字段说明

| 字段 | 类型 | 说明 |
|-----|------|------|
| `success` | boolean | 始终为 `false` |
| `error.code` | string | 机器可读的错误码 |
| `error.message` | string | 用户友好的错误描述 |
| `error.error_id` | string | 唯一的错误ID，用于技术支持查询 |
| `error.timestamp` | string | 错误发生时间（ISO 8601格式） |
| `error.details` | object | 可选的额外错误详情 |

---

## HTTP状态码映射

| HTTP状态码 | 含义 | 典型场景 |
|-----------|------|---------|
| 400 | Bad Request | 请求参数错误 |
| 401 | Unauthorized | 认证失败 |
| 403 | Forbidden | 权限不足 |
| 404 | Not Found | 资源不存在 |
| 422 | Unprocessable Entity | 请求验证失败 |
| 429 | Too Many Requests | 速率限制 |
| 500 | Internal Server Error | 服务器内部错误 |
| 503 | Service Unavailable | 服务不可用 |
| 504 | Gateway Timeout | 请求超时 |

---

## 客户端错误 (4xx)

### 400 - Bad Request

#### `BAD_REQUEST`
**描述**: 请求格式错误或缺少必需参数

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "BAD_REQUEST",
    "message": "请求参数 'user_id' 是必需的",
    "error_id": "err001",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "missing_param": "user_id"
    }
  }
}
```

**处理建议**:
- 检查请求体是否包含所有必需参数
- 验证参数类型是否正确

---

#### `INVALID_JSON`
**描述**: 请求体JSON格式无效

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_JSON",
    "message": "请求体JSON格式无效",
    "error_id": "err002",
    "timestamp": "2026-04-04T15:30:00Z"
  }
}
```

---

### 401 - Unauthorized

#### `AUTHENTICATION_ERROR`
**描述**: 认证失败，缺少或无效的认证令牌

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "AUTHENTICATION_ERROR",
    "message": "缺少认证令牌",
    "error_id": "err003",
    "timestamp": "2026-04-04T15:30:00Z"
  }
}
```

**处理建议**:
- 确保请求头包含 `Authorization: Bearer <token>`
- 检查令牌是否过期，如过期请重新获取

---

#### `TOKEN_EXPIRED`
**描述**: 认证令牌已过期

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "TOKEN_EXPIRED",
    "message": "认证令牌已过期，请重新登录",
    "error_id": "err004",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "expired_at": "2026-04-04T14:00:00Z"
    }
  }
}
```

---

#### `INVALID_TOKEN`
**描述**: 认证令牌无效或格式错误

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_TOKEN",
    "message": "无效的认证令牌格式",
    "error_id": "err005",
    "timestamp": "2026-04-04T15:30:00Z"
  }
}
```

---

### 403 - Forbidden

#### `AUTHORIZATION_ERROR`
**描述**: 权限不足，无法访问请求的资源

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "AUTHORIZATION_ERROR",
    "message": "您没有权限访问此学习路径",
    "error_id": "err006",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "resource": "learning_path",
      "resource_id": "123",
      "required_permission": "owner"
    }
  }
}
```

**处理建议**:
- 确认当前用户具有访问该资源的权限
- 如需访问，请联系资源所有者或管理员

---

#### `QUOTA_EXCEEDED`
**描述**: 超出使用配额

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "QUOTA_EXCEEDED",
    "message": "您已达到今日API调用配额限制",
    "error_id": "err007",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "quota": 1000,
      "used": 1000,
      "reset_time": "2026-04-05T00:00:00Z"
    }
  }
}
```

---

### 404 - Not Found

#### `NOT_FOUND`
**描述**: 请求的资源不存在

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "NOT_FOUND",
    "message": "概念 'non_existent_concept' 未找到",
    "error_id": "err008",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "resource": "concept",
      "resource_id": "non_existent_concept"
    }
  }
}
```

**处理建议**:
- 验证资源ID是否正确
- 确认资源未被删除

---

#### `ENDPOINT_NOT_FOUND`
**描述**: API端点不存在

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "ENDPOINT_NOT_FOUND",
    "message": "请求的API端点不存在",
    "error_id": "err009",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "path": "/api/v1/invalid-endpoint",
      "method": "GET"
    }
  }
}
```

---

#### `TASK_NOT_FOUND`
**描述**: 异步任务不存在或已过期

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "TASK_NOT_FOUND",
    "message": "任务 'abc123' 不存在或已过期",
    "error_id": "err010",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "task_id": "abc123",
      "max_age": "7d"
    }
  }
}
```

---

### 422 - Unprocessable Entity

#### `VALIDATION_ERROR`
**描述**: 请求参数验证失败

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "请求参数验证失败",
    "error_id": "err011",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "errors": [
        {
          "field": "user_id",
          "message": "必须是正整数",
          "type": "type_error.integer"
        },
        {
          "field": "target_concepts",
          "message": "至少需要1个目标概念",
          "type": "value_error.list.min_items"
        }
      ]
    }
  }
}
```

**处理建议**:
- 根据 `errors` 数组中的详细信息修正请求参数
- 参考API文档中的参数类型要求

---

#### `INVALID_DIFFICULTY_RANGE`
**描述**: 难度范围设置无效

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_DIFFICULTY_RANGE",
    "message": "难度范围无效：最小值不能大于最大值",
    "error_id": "err012",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "min": 0.8,
      "max": 0.3
    }
  }
}
```

---

#### `INVALID_ALGORITHM`
**描述**: 无效的算法类型

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_ALGORITHM",
    "message": "无效的算法 'invalid_algo'",
    "error_id": "err013",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "provided": "invalid_algo",
      "allowed": ["astar", "dijkstra", "dp"]
    }
  }
}
```

---

#### `INVALID_SEARCH_TYPE`
**描述**: 无效的搜索类型

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_SEARCH_TYPE",
    "message": "无效的搜索类型 'fuzzy'",
    "error_id": "err014",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "provided": "fuzzy",
      "allowed": ["semantic", "keyword", "hybrid", "formula"]
    }
  }
}
```

---

#### `INVALID_FORMULA`
**描述**: LaTeX公式格式无效

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INVALID_FORMULA",
    "message": "LaTeX公式格式无效",
    "error_id": "err015",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "latex": "E = mc^",
      "error_position": 7
    }
  }
}
```

---

#### `PAGE_SIZE_TOO_LARGE`
**描述**: 分页大小超出限制

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "PAGE_SIZE_TOO_LARGE",
    "message": "每页数量不能超过100",
    "error_id": "err016",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "provided": 500,
      "max_allowed": 100
    }
  }
}
```

---

### 429 - Too Many Requests

#### `RATE_LIMIT_EXCEEDED`
**描述**: 请求频率超过限制

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "请求过于频繁，请稍后再试",
    "error_id": "err017",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "limit": 120,
      "window": "1m",
      "retry_after": 45
    }
  }
}
```

**响应头**:
```
Retry-After: 45
X-RateLimit-Limit: 120
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1649088645
```

**处理建议**:
- 根据 `Retry-After` 头等待指定秒数后重试
- 实施客户端速率限制
- 考虑使用指数退避策略

---

## 服务器错误 (5xx)

### 500 - Internal Server Error

#### `INTERNAL_ERROR`
**描述**: 服务器内部错误

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "INTERNAL_ERROR",
    "message": "服务器内部错误，请稍后重试",
    "error_id": "err018",
    "timestamp": "2026-04-04T15:30:00Z"
  }
}
```

**处理建议**:
- 记录 `error_id` 并联系技术支持
- 稍后重试请求
- 检查API状态页面确认服务状态

---

#### `PATH_CALCULATION_ERROR`
**描述**: 学习路径计算失败

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "PATH_CALCULATION_ERROR",
    "message": "学习路径计算失败：图中存在循环依赖",
    "error_id": "err019",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "target_concepts": ["concept_a", "concept_b"],
      "error_type": "circular_dependency"
    }
  }
}
```

---

#### `SEARCH_SERVICE_ERROR`
**描述**: 搜索服务内部错误

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "SEARCH_SERVICE_ERROR",
    "message": "搜索服务暂时不可用",
    "error_id": "err020",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "service": "semantic_search",
      "reason": "embedding_service_timeout"
    }
  }
}
```

---

### 503 - Service Unavailable

#### `DATABASE_ERROR`
**描述**: 数据库操作失败

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "DATABASE_ERROR",
    "message": "数据库连接失败，请稍后重试",
    "error_id": "err021",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "error_id": "err021"
    }
  }
}
```

**处理建议**:
- 稍后重试请求
- 检查API状态页面

---

#### `REDIS_UNAVAILABLE`
**描述**: Redis缓存服务不可用

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "REDIS_UNAVAILABLE",
    "message": "缓存服务暂时不可用",
    "error_id": "err022",
    "timestamp": "2026-04-04T15:30:00Z"
  }
}
```

---

#### `CELERY_UNAVAILABLE`
**描述**: Celery任务队列不可用

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "CELERY_UNAVAILABLE",
    "message": "异步任务服务暂时不可用",
    "error_id": "err023",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "broker_status": "disconnected"
    }
  }
}
```

---

#### `SERVICE_MAINTENANCE`
**描述**: 服务维护中

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "SERVICE_MAINTENANCE",
    "message": "API服务正在维护中，预计维护时间：2小时",
    "error_id": "err024",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "maintenance_start": "2026-04-04T14:00:00Z",
      "estimated_end": "2026-04-04T16:00:00Z"
    }
  }
}
```

---

### 504 - Gateway Timeout

#### `DATABASE_TIMEOUT`
**描述**: 数据库查询超时

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "DATABASE_TIMEOUT",
    "message": "数据库查询超时，请稍后重试",
    "error_id": "err025",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "query_time": 30.5,
      "timeout": 30
    }
  }
}
```

**处理建议**:
- 简化查询参数
- 使用更小的分页大小
- 稍后重试

---

#### `TASK_TIMEOUT`
**描述**: 异步任务执行超时

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "TASK_TIMEOUT",
    "message": "任务执行超时",
    "error_id": "err026",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "task_id": "abc123",
      "max_execution_time": 3600,
      "actual_time": 3600
    }
  }
}
```

---

## 业务逻辑错误

### 409 - Conflict

#### `RESOURCE_CONFLICT`
**描述**: 资源冲突

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "RESOURCE_CONFLICT",
    "message": "学习路径名称已存在",
    "error_id": "err027",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "field": "name",
      "value": "我的学习路径"
    }
  }
}
```

---

#### `TASK_ALREADY_REVOKED`
**描述**: 任务已被撤销

**示例**:
```json
{
  "success": false,
  "error": {
    "code": "TASK_ALREADY_REVOKED",
    "message": "任务已被撤销，无法再次撤销",
    "error_id": "err028",
    "timestamp": "2026-04-04T15:30:00Z",
    "details": {
      "task_id": "abc123",
      "revoked_at": "2026-04-04T15:25:00Z"
    }
  }
}
```

---

## 错误处理最佳实践

### 1. 错误重试策略

```python
import time
from functools import wraps

def retry_on_error(exceptions=(Exception,), max_retries=3, backoff_factor=1):
    """指数退保重试装饰器"""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            retries = 0
            while retries < max_retries:
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    retries += 1
                    if retries == max_retries:
                        raise
                    
                    # 计算等待时间（指数退避）
                    wait_time = backoff_factor * (2 ** (retries - 1))
                    time.sleep(wait_time)
            return None
        return wrapper
    return decorator

# 使用示例
@retry_on_error(exceptions=(DatabaseError, TimeoutError), max_retries=3)
def fetch_data():
    return api.get_data()
```

### 2. 速率限制处理

```python
import time

def make_request_with_rate_limit_handling(url, **kwargs):
    """处理速率限制的请求"""
    response = requests.post(url, **kwargs)
    
    if response.status_code == 429:
        # 获取Retry-After头
        retry_after = int(response.headers.get('Retry-After', 60))
        print(f"速率限制，等待 {retry_after} 秒...")
        time.sleep(retry_after)
        
        # 重试请求
        return make_request_with_rate_limit_handling(url, **kwargs)
    
    return response
```

### 3. 错误日志记录

```python
import logging

logger = logging.getLogger(__name__)

def log_api_error(response):
    """记录API错误"""
    error_data = response.json()
    error = error_data.get('error', {})
    
    logger.error(
        f"API错误: {error.get('code')} - {error.get('message')}",
        extra={
            'error_id': error.get('error_id'),
            'status_code': response.status_code,
            'endpoint': response.request.url,
            'timestamp': error.get('timestamp')
        }
    )
```

---

## 错误码速查表

| 错误码 | HTTP状态码 | 类别 | 说明 |
|--------|-----------|------|------|
| `BAD_REQUEST` | 400 | 客户端 | 请求格式错误 |
| `INVALID_JSON` | 400 | 客户端 | JSON格式无效 |
| `AUTHENTICATION_ERROR` | 401 | 认证 | 认证失败 |
| `TOKEN_EXPIRED` | 401 | 认证 | 令牌过期 |
| `INVALID_TOKEN` | 401 | 认证 | 令牌无效 |
| `AUTHORIZATION_ERROR` | 403 | 授权 | 权限不足 |
| `QUOTA_EXCEEDED` | 403 | 配额 | 超出配额 |
| `NOT_FOUND` | 404 | 资源 | 资源不存在 |
| `ENDPOINT_NOT_FOUND` | 404 | 资源 | 端点不存在 |
| `TASK_NOT_FOUND` | 404 | 资源 | 任务不存在 |
| `VALIDATION_ERROR` | 422 | 验证 | 参数验证失败 |
| `INVALID_DIFFICULTY_RANGE` | 422 | 验证 | 难度范围无效 |
| `INVALID_ALGORITHM` | 422 | 验证 | 算法无效 |
| `INVALID_SEARCH_TYPE` | 422 | 验证 | 搜索类型无效 |
| `INVALID_FORMULA` | 422 | 验证 | 公式格式无效 |
| `PAGE_SIZE_TOO_LARGE` | 422 | 验证 | 分页过大 |
| `RATE_LIMIT_EXCEEDED` | 429 | 限流 | 请求过于频繁 |
| `INTERNAL_ERROR` | 500 | 服务器 | 内部错误 |
| `PATH_CALCULATION_ERROR` | 500 | 服务器 | 路径计算失败 |
| `SEARCH_SERVICE_ERROR` | 500 | 服务器 | 搜索服务错误 |
| `DATABASE_ERROR` | 503 | 服务 | 数据库错误 |
| `REDIS_UNAVAILABLE` | 503 | 服务 | Redis不可用 |
| `CELERY_UNAVAILABLE` | 503 | 服务 | Celery不可用 |
| `SERVICE_MAINTENANCE` | 503 | 服务 | 维护中 |
| `DATABASE_TIMEOUT` | 504 | 超时 | 数据库超时 |
| `TASK_TIMEOUT` | 504 | 超时 | 任务超时 |
| `RESOURCE_CONFLICT` | 409 | 冲突 | 资源冲突 |
| `TASK_ALREADY_REVOKED` | 409 | 冲突 | 任务已撤销 |
