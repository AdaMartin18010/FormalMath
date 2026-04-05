---
msc_primary: 68N99
title: FormalMath API 开发指南
created_date: 2026-04-04
version: 1.0.0
author: FormalMath 开发团队
processed_at: '2026-04-05'
---
# FormalMath API 开发指南

> 本文档描述 FormalMath 项目各系统的 API 接口规范、使用方法和开发实践。

---

## 目录

- [概述](#概述)
- [API 设计原则](#api-设计原则)
- [核心 API 模块](#核心-api-模块)
- [认证与授权](#认证与授权)
- [请求/响应格式](#请求响应格式)
- [错误处理](#错误处理)
- [速率限制](#速率限制)
- [SDK 与客户端](#sdk-与客户端)

---

## 概述

FormalMath 提供多层次的 API 接口：

| API 类型 | 用途 | 协议 |
|----------|------|------|
| Python API | 工具系统集成 | Python 函数/类 |
| REST API | Web 服务 | HTTP/JSON |
| CLI API | 命令行工具 | Shell 命令 |
| 文件 API | 文档操作 | 文件系统 |

---

## API 设计原则

### 1. RESTful 设计

```
GET    /api/v1/concepts          # 获取概念列表
GET    /api/v1/concepts/{id}     # 获取单个概念
POST   /api/v1/concepts          # 创建概念
PUT    /api/v1/concepts/{id}     # 更新概念
DELETE /api/v1/concepts/{id}     # 删除概念
```

### 2. 版本控制

- URL 版本: `/api/v1/...`, `/api/v2/...`
- 向后兼容: 主版本保持兼容
- 弃用通知: 提前 3 个月通知

### 3. 统一响应格式

```json
{
  "success": true,
  "data": { ... },
  "meta": {
    "timestamp": "2026-04-04T15:30:00Z",
    "request_id": "req_123456"
  }
}
```

错误响应：

```json
{
  "success": false,
  "error": {
    "code": "CONCEPT_NOT_FOUND",
    "message": "Concept with id 'xyz' not found",
    "details": { ... }
  },
  "meta": { ... }
}
```

---

## 核心 API 模块

### 1. 元数据管理 API

#### Python API

```python
from tools.metadata_system.metadata_extractor import MetadataExtractor
from tools.metadata_system.metadata_query import MetadataQuery

# 提取元数据
extractor = MetadataExtractor('.')
records = extractor.scan_directory('**/*.md')

# 查询文档
query = MetadataQuery('metadata.json')
results = query.query(
    category='代数结构',
    difficulty='L2',
    has_proofs=True
)
```

#### REST API

```http
GET /api/v1/documents?category=代数结构&difficulty=L2&has_proofs=true
```

响应：

```json
{
  "success": true,
  "data": {
    "documents": [
      {
        "id": "group-theory-basics",
        "title": "群论基础",
        "path": "docs/02-代数结构/群论.md",
        "metadata": {
          "msc_primary": "20-01",
          "difficulty": "L2",
          "has_proofs": true
        }
      }
    ],
    "total": 45,
    "page": 1,
    "per_page": 20
  }
}
```

### 2. 评估系统 API

#### Python API

```python
from tools.assessment_system.assessment_system import FormalMathAssessmentSystem
from tools.assessment_system.evaluation_criteria import MathematicalAbilityProfile

# 初始化系统
assessment_system = FormalMathAssessmentSystem()

# 注册学习者
profile = assessment_system.register_learner("student_001", "张三")

# 进行形成性评价
result = assessment_system.conduct_formative_assessment("student_001")

# 生成报告
report = assessment_system.generate_report(
    ReportType.ABILITY,
    "student_001",
    detailed=True
)
```

#### REST API

```http
POST /api/v1/assessments/formative
Content-Type: application/json

{
  "learner_id": "student_001",
  "assessment_type": "formative"
}
```

响应：

```json
{
  "success": true,
  "data": {
    "assessment_id": "asm_123",
    "learner_id": "student_001",
    "overall_score": 78.5,
    "level": "PROFICIENT",
    "dimensions": {
      "conceptual_understanding": 82.0,
      "procedural_fluency": 75.0,
      "strategic_competence": 80.0,
      "adaptive_reasoning": 76.0,
      "productive_disposition": 79.0
    },
    "recommendations": [
      "建议加强代数基础概念的理解",
      "推荐学习路径：群论 -> 环论"
    ]
  }
}
```

### 3. 学习路径推荐 API

#### Python API

```python
from tools.personalized_recommendation.recommendation_engine import RecommendationEngine
from tools.personalized_recommendation.user_profile import UserProfile

# 创建用户画像
user = UserProfile(name="张三", email="zhangsan@example.com")
user.update_mastery("set_theory", 0.85)
user.update_mastery("functions", 0.75)

# 生成推荐
engine = RecommendationEngine(graph)
paths = engine.recommend(
    user_profile=user,
    strategy=PathStrategy.BALANCED,
    target_concepts=["algebraic_topology"]
)
```

#### REST API

```http
POST /api/v1/learning-paths/recommend
Content-Type: application/json

{
  "user_id": "student_001",
  "strategy": "balanced",
  "target_concepts": ["algebraic_topology"],
  "constraints": {
    "max_daily_hours": 3,
    "deadline": "2026-06-01"
  }
}
```

响应：

```json
{
  "success": true,
  "data": {
    "paths": [
      {
        "id": "path_001",
        "name": "代数拓扑学习路径",
        "total_estimated_hours": 120,
        "nodes": [
          {
            "concept_id": "group_theory",
            "estimated_hours": 20,
            "difficulty": "L2"
          },
          {
            "concept_id": "topological_spaces",
            "estimated_hours": 25,
            "difficulty": "L2"
          }
        ],
        "parallel_groups": [
          ["group_theory", "topological_spaces"]
        ]
      }
    ]
  }
}
```

### 4. 质量评估 API

#### Python API

```python
from tools.content_quality_assessment.quality_assessor import ContentQualityAssessor

# 创建评估器
assessor = ContentQualityAssessor()

# 评估单个文件
result = assessor.assess_file("docs/02-代数结构/群论.md")

# 批量评估
results = assessor.assess_directory("docs/02-代数结构")
summary = assessor.get_summary()
```

#### REST API

```http
POST /api/v1/quality/assess
Content-Type: application/json

{
  "path": "docs/02-代数结构/群论.md",
  "options": {
    "check_completeness": true,
    "check_accuracy": true,
    "check_readability": true
  }
}
```

响应：

```json
{
  "success": true,
  "data": {
    "file_name": "群论.md",
    "overall_score": 85.2,
    "quality_level": "GOOD",
    "scores": {
      "completeness": 90.0,
      "accuracy": 88.0,
      "readability": 82.0,
      "internationalization": 80.0,
      "learning_effect": 86.0
    },
    "issues": [
      {
        "type": "missing_example",
        "severity": "medium",
        "message": "建议添加更多应用示例"
      }
    ]
  }
}
```

### 5. 概念图谱 API

#### Python API

```python
from tools.doc_generator.concept_graph_generator import ConceptGraphGenerator

# 创建生成器
generator = ConceptGraphGenerator('.')

# 生成概念图谱
graph_data = generator.build_concept_graph()

# 查找学习路径
path = generator.find_learning_path("集合论", "代数拓扑")

# 获取前置知识
prerequisites = generator.get_prerequisites("群论")
```

#### REST API

```http
GET /api/v1/concepts/graph

GET /api/v1/concepts/{id}/prerequisites

GET /api/v1/concepts/path?from=集合论&to=代数拓扑
```

### 6. 文档生成 API

#### Python API

```python
from tools.doc_generator.doc_generator import FormalMathDocGenerator

# 创建生成器
generator = FormalMathDocGenerator('.')

# 生成所有文档
generator.generate_all()

# 生成特定类型
generator.generate_api_docs()
generator.generate_concept_graphs()
generator.generate_lean4_docs()
```

#### CLI API

```bash
# 生成所有文档
python tools/doc-generator/generate_docs.py

# 仅生成 API 文档
python tools/doc-generator/generate_docs.py --api-only

# 指定输出格式
python tools/doc-generator/generate_docs.py -f markdown html json
```

---

## 认证与授权

### API 密钥认证

```http
GET /api/v1/documents
Authorization: Bearer YOUR_API_KEY
```

### 权限级别

| 级别 | 权限 | 说明 |
|------|------|------|
| read | 只读访问 | 获取文档、查询元数据 |
| write | 写入访问 | 创建/更新文档 |
| admin | 管理权限 | 删除、批量操作 |

---

## 请求/响应格式

### 分页

```http
GET /api/v1/documents?page=2&per_page=20
```

响应：

```json
{
  "data": [...],
  "meta": {
    "pagination": {
      "page": 2,
      "per_page": 20,
      "total": 150,
      "total_pages": 8
    }
  }
}
```

### 过滤

```http
GET /api/v1/documents?filter[difficulty]=L2&filter[category]=代数结构
```

### 排序

```http
GET /api/v1/documents?sort=-created_at,+title
```

### 字段选择

```http
GET /api/v1/documents?fields=id,title,metadata.difficulty
```

---

## 错误处理

### 错误代码

| 代码 | HTTP 状态 | 说明 |
|------|-----------|------|
| INVALID_REQUEST | 400 | 请求参数错误 |
| UNAUTHORIZED | 401 | 未授权 |
| FORBIDDEN | 403 | 权限不足 |
| NOT_FOUND | 404 | 资源不存在 |
| RATE_LIMITED | 429 | 请求过于频繁 |
| INTERNAL_ERROR | 500 | 服务器内部错误 |

### 错误响应示例

```json
{
  "success": false,
  "error": {
    "code": "VALIDATION_ERROR",
    "message": "Request validation failed",
    "details": [
      {
        "field": "difficulty",
        "message": "Invalid difficulty level. Allowed: L0, L1, L2, L3, L4"
      }
    ]
  }
}
```

---

## 速率限制

| 端点类型 | 限制 | 窗口 |
|----------|------|------|
| 读取 | 1000 请求 | 1 小时 |
| 写入 | 100 请求 | 1 小时 |
| 批量操作 | 10 请求 | 1 小时 |

响应头：

```http
X-RateLimit-Limit: 1000
X-RateLimit-Remaining: 999
X-RateLimit-Reset: 1712232000
```

---

## SDK 与客户端

### Python SDK

```python
from formalmath import Client

# 初始化客户端
client = Client(api_key="your_key")

# 使用高级 API
docs = client.documents.list(category="代数结构")
assessment = client.assessments.create(learner_id="stu_001")
path = client.learning_paths.recommend(user_id="stu_001")
```

### JavaScript SDK

```javascript
import { FormalMathClient } from '@formalmath/sdk';

const client = new FormalMathClient({ apiKey: 'your_key' });

// 获取文档
const docs = await client.documents.list({ category: '代数结构' });

// 创建评估
const assessment = await client.assessments.create({ learnerId: 'stu_001' });
```

---

## API 版本历史

| 版本 | 发布日期 | 主要变更 |
|------|----------|----------|
| v1.0 | 2026-04-04 | 初始版本 |

---

**最后更新**: 2026年4月4日
**维护者**: FormalMath 开发团队
