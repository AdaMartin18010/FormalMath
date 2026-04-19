---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# AI学习助手 API文档

## 基础信息

- **Base URL**: `/api/v1/ai-assistant`
- **Content-Type**: `application/json`

## 端点概览

| 端点 | 方法 | 描述 |
|------|------|------|
| `/ask` | POST | 通用问答 |
| `/explain` | POST | 概念解释 |
| `/proof-hint` | POST | 证明提示 |
| `/learning-advice` | POST | 学习建议 |
| `/solve` | POST | 问题解答 |
| `/lean-help` | POST | Lean 4帮助 |
| `/conversations` | POST/GET | 对话管理 |
| `/suggest-questions` | GET | 获取建议问题 |

---

## 详细接口

### 1. 通用问答

**POST** `/ask`

自动识别问题类型并给出回答。

#### 请求体

```json
{
  "question": "什么是群论？",
  "context_id": "可选，对话上下文ID",
  "user_id": "可选，用户ID",
  "stream": false
}
```

#### 响应

```json
{
  "answer": "群论是代数学的一个分支...",
  "answer_type": "concept",
  "confidence": 0.92,
  "context_id": "session_xxx",
  "suggestions": ["群论有哪些应用？", "如何学习群论？"],
  "references": [...],
  "latex_formulas": ["G = (S, \\cdot)"],
  "proof_steps": [],
  "timestamp": "2026-04-08T13:00:00"
}
```

---

### 2. 概念解释

**POST** `/explain`

解释数学概念，支持不同难度级别。

#### 请求体

```json
{
  "concept": "群论",
  "level": "intermediate",
  "context_id": "可选"
}
```

#### 难度级别

- `beginner`: 入门级，使用通俗语言和类比
- `intermediate`: 中级，标准技术解释
- `advanced`: 高级，严格数学定义和深度讨论

---

### 3. 证明提示

**POST** `/proof-hint`

提供证明的启发式指导。

#### 请求体

```json
{
  "theorem": "证明：任何有限群都有合成列",
  "user_attempt": "可选，用户的证明尝试",
  "context_id": "可选"
}
```

#### 响应特点

- 不直接给出完整证明
- 提供证明策略建议
- 指出关键引理
- 引导用户自己完成

---

### 4. 学习建议

**POST** `/learning-advice`

提供个性化学习路径建议。

#### 请求体

```json
{
  "goal": "我想学习代数几何",
  "user_id": "可选，用于个性化",
  "context_id": "可选"
}
```

---

### 5. 问题解答

**POST** `/solve`

解答数学问题。

#### 请求体

```json
{
  "problem": "计算积分 ∫x² dx",
  "show_steps": true,
  "context_id": "可选"
}
```

---

### 6. Lean 4帮助

**POST** `/lean-help`

Lean 4形式化帮助。

#### 请求体

```json
{
  "statement": "证明：对于任意自然数n，n + 0 = n",
  "context_id": "可选"
}
```

---

### 7. 对话管理

#### 创建对话

**POST** `/conversations`

```json
{
  "user_id": "可选",
  "topic": "可选，对话主题",
  "system_prompt": "可选，自定义系统提示词"
}
```

#### 获取对话

**GET** `/conversations/{session_id}`

#### 列出用户对话

**GET** `/conversations?user_id=xxx`

#### 删除对话

**DELETE** `/conversations/{session_id}`

---

### 8. 获取建议问题

**GET** `/suggest-questions?topic=群论&k=5`

---

## 响应字段说明

| 字段 | 类型 | 说明 |
|------|------|------|
| `answer` | string | AI回答内容 |
| `answer_type` | string | 回答类型：concept/proof/advice/problem/lean/general |
| `confidence` | float | 置信度 0-1 |
| `context_id` | string | 对话上下文ID |
| `suggestions` | array | 建议的后续问题 |
| `references` | array | 参考来源 |
| `latex_formulas` | array | 提取的LaTeX公式 |
| `proof_steps` | array | 证明步骤（如适用） |
| `timestamp` | string | 响应时间戳 |

---

## 错误码

| 状态码 | 说明 |
|--------|------|
| 200 | 成功 |
| 400 | 请求参数错误 |
| 404 | 资源不存在 |
| 500 | 服务器内部错误 |

---

## 使用示例

### Python示例

```python
import requests

API_BASE = "http://localhost:8001/api/v1/ai-assistant"

# 概念解释
response = requests.post(f"{API_BASE}/explain", json={
    "concept": "群论",
    "level": "beginner"
})
print(response.json()["answer"])

# 通用问答
response = requests.post(f"{API_BASE}/ask", json={
    "question": "什么是正规子群？"
})
data = response.json()
print(f"回答: {data['answer']}")
print(f"建议问题: {data['suggestions']}")
```

### JavaScript示例

```javascript
const API_BASE = 'http://localhost:8001/api/v1/ai-assistant';

// 获取证明提示
const response = await fetch(`${API_BASE}/proof-hint`, {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify({
    theorem: '证明拉格朗日定理'
  })
});

const data = await response.json();
console.log(data.answer);
```
