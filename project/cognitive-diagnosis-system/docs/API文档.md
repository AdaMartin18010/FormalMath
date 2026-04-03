# FormalMath认知诊断系统 - API文档

## 基础信息

- **Base URL**: `/api/v1`
- **Content-Type**: `application/json`
- **认证方式**: Bearer Token

## 接口列表

### 1. 诊断接口

#### 1.1 开始诊断测试
```http
POST /diagnosis/start
```

**请求体**:
```json
{
  "student_id": "string",
  "target_level": 0,
  "focus_areas": ["代数"],
  "question_count": 30
}
```

**响应**:
```json
{
  "success": true,
  "message": "诊断测试已创建",
  "data": {
    "test_id": "uuid",
    "questions": [...],
    "time_limit": 3600
  }
}
```

#### 1.2 提交答案
```http
POST /diagnosis/submit
```

**请求体**:
```json
{
  "test_id": "uuid",
  "responses": [
    {
      "question_id": "string",
      "answer": "string",
      "time_spent": 120
    }
  ]
}
```

#### 1.3 获取诊断结果
```http
GET /diagnosis/{test_id}/result
```

**响应**:
```json
{
  "success": true,
  "data": {
    "test_id": "uuid",
    "student_id": "string",
    "knowledge_state": {...},
    "ability_level": {...},
    "weak_areas": [...],
    "strong_areas": [...],
    "suggestions": [...]
  }
}
```

### 2. 学生接口

#### 2.1 获取学生档案
```http
GET /students/{student_id}/profile
```

#### 2.2 获取学习路径
```http
GET /students/{student_id}/learning-path
```

#### 2.3 获取诊断历史
```http
GET /students/{student_id}/history?limit=10
```

### 3. 题目接口

#### 3.1 获取题目列表
```http
GET /questions?level=1&branch=代数学&limit=20
```

## 数据模型

### Question (题目)
```json
{
  "id": "string",
  "content": "string",
  "type": "SC|MC|FB|SA|PR",
  "level": 0,
  "difficulty": 1,
  "branch": "string",
  "concepts": ["string"],
  "skills": ["string"],
  "options": {"A": "string"},
  "time_estimate": 60,
  "score": 5
}
```

### DiagnosisResult (诊断结果)
```json
{
  "test_id": "string",
  "student_id": "string",
  "knowledge_state": {
    "concept_id": {
      "level": 0.8,
      "confidence": 0.9
    }
  },
  "ability_level": {
    "L0": {"score": 0.9, "level": "advanced"},
    "L1": {"score": 0.7, "level": "intermediate"},
    "L2": {"score": 0.6, "level": "developing"},
    "L3": {"score": 0.3, "level": "beginner"}
  },
  "weak_areas": [...],
  "strong_areas": [...],
  "suggestions": [...],
  "overall_confidence": 0.85
}
```

## 错误码

| 状态码 | 说明 |
|--------|------|
| 200 | 成功 |
| 400 | 请求参数错误 |
| 401 | 未认证 |
| 403 | 无权限 |
| 404 | 资源不存在 |
| 500 | 服务器内部错误 |

## 示例代码

### Python
```python
import requests

# 开始诊断
response = requests.post(
    "http://localhost:8000/api/v1/diagnosis/start",
    json={"question_count": 30}
)
data = response.json()

# 获取结果
result = requests.get(
    f"http://localhost:8000/api/v1/diagnosis/{test_id}/result"
)
```

### JavaScript
```javascript
// 开始诊断
const response = await fetch('/api/v1/diagnosis/start', {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify({ question_count: 30 })
});
const data = await response.json();
```
