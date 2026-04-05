---
title: 用户反馈系统 API 文档
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 用户反馈系统 API 文档

## 概述

用户反馈系统提供完整的反馈收集、分类、处理和可视化功能，支持自动分类、优先级判定、情感分析和仪表板展示。

## 基础信息

- **API前缀**: `/api/v1/feedback`
- **Content-Type**: `application/json`

## 反馈类型

| 值 | 说明 |
|-----|------|
| `bug_report` | 错误报告 |
| `feature_request` | 功能请求 |
| `content_error` | 内容错误 |
| `usability` | 可用性问题 |
| `performance` | 性能问题 |
| `general` | 一般反馈 |
| `complaint` | 投诉 |
| `compliment` | 表扬 |

## 反馈状态

| 值 | 说明 |
|-----|------|
| `pending` | 待处理 |
| `classified` | 已分类 |
| `under_review` | 审核中 |
| `in_progress` | 处理中 |
| `resolved` | 已解决 |
| `closed` | 已关闭 |
| `rejected` | 已拒绝 |

## 优先级

| 值 | 说明 |
|-----|------|
| `critical` | 紧急 |
| `high` | 高 |
| `medium` | 中 |
| `low` | 低 |

---

## API 端点

### 1. 提交反馈

**POST** `/api/v1/feedback/feedbacks`

提交新的用户反馈。如果未指定`feedback_type`，系统将自动进行分类。

#### 请求体

```json
{
  "title": "搜索功能无法使用",
  "content": "在搜索框输入关键词后，页面显示加载中但没有任何结果返回",
  "feedback_type": "bug_report",
  "related_page": "/search",
  "satisfaction_rating": 2,
  "browser_info": {
    "browser": "Chrome",
    "version": "120.0",
    "os": "Windows 10"
  },
  "device_info": {
    "type": "desktop",
    "screen": "1920x1080"
  }
}
```

#### 响应

```json
{
  "success": true,
  "data": {
    "id": 123,
    "feedback_type": "bug_report",
    "status": "pending",
    "priority": "high",
    "message": "反馈提交成功"
  }
}
```

---

### 2. 获取反馈列表

**GET** `/api/v1/feedback/feedbacks`

查询反馈列表，支持多种筛选条件。

#### 查询参数

| 参数 | 类型 | 说明 |
|------|------|------|
| `status` | string | 状态筛选 |
| `feedback_type` | string | 类型筛选 |
| `priority` | string | 优先级筛选 |
| `keyword` | string | 关键词搜索 |
| `page` | integer | 页码（默认1） |
| `page_size` | integer | 每页数量（默认20，最大100） |

#### 响应

```json
{
  "success": true,
  "data": {
    "items": [
      {
        "id": 123,
        "title": "搜索功能无法使用",
        "feedback_type": "bug_report",
        "status": "pending",
        "priority": "high",
        "created_at": "2026-04-04T10:30:00"
      }
    ],
    "total": 50,
    "page": 1,
    "page_size": 20,
    "total_pages": 3
  }
}
```

---

### 3. 获取反馈详情

**GET** `/api/v1/feedback/feedbacks/{feedback_id}`

获取单个反馈的详细信息，包括回复列表。

#### 响应

```json
{
  "success": true,
  "data": {
    "id": 123,
    "title": "搜索功能无法使用",
    "content": "在搜索框输入关键词后...",
    "feedback_type": "bug_report",
    "auto_classified_type": "bug_report",
    "classification_confidence": 0.95,
    "status": "under_review",
    "priority": "high",
    "related_page": "/search",
    "satisfaction_rating": 2,
    "resolution_notes": null,
    "created_at": "2026-04-04T10:30:00",
    "updated_at": "2026-04-04T11:00:00",
    "resolved_at": null,
    "responses": [
      {
        "id": 1,
        "content": "感谢您的反馈，我们正在调查中...",
        "responder_id": 5,
        "is_internal": false,
        "created_at": "2026-04-04T11:00:00"
      }
    ]
  }
}
```

---

### 4. 更新反馈

**PUT** `/api/v1/feedback/feedbacks/{feedback_id}`

更新反馈的状态、优先级等信息。

#### 请求体

```json
{
  "status": "in_progress",
  "priority": "high",
  "assigned_to": 5,
  "resolution_notes": "已定位问题，正在修复"
}
```

#### 响应

```json
{
  "success": true,
  "data": {
    "id": 123,
    "status": "in_progress",
    "priority": "high",
    "message": "反馈更新成功"
  }
}
```

---

### 5. 删除反馈

**DELETE** `/api/v1/feedback/feedbacks/{feedback_id}`

删除指定反馈。

#### 响应

```json
{
  "success": true,
  "data": {
    "message": "反馈删除成功"
  }
}
```

---

### 6. 添加回复

**POST** `/api/v1/feedback/feedbacks/{feedback_id}/responses`

为反馈添加回复或内部备注。

#### 请求体

```json
{
  "content": "感谢您的反馈，问题已修复，请刷新页面重试",
  "responder_id": 5,
  "is_internal": false
}
```

#### 响应

```json
{
  "success": true,
  "data": {
    "id": 2,
    "feedback_id": 123,
    "created_at": "2026-04-04T14:00:00",
    "message": "回复添加成功"
  }
}
```

---

### 7. 预分类

**POST** `/api/v1/feedback/classify`

在不提交反馈的情况下，预览系统的分类建议。

#### 请求体

```json
{
  "title": "搜索功能无法使用",
  "content": "在搜索框输入关键词后，页面显示加载中但没有任何结果返回"
}
```

#### 响应

```json
{
  "success": true,
  "data": {
    "feedback_type": "bug_report",
    "confidence": 0.95,
    "priority": "high",
    "keywords": ["搜索", "功能", "无法", "加载"],
    "sentiment": {
      "sentiment": "negative",
      "positive_score": 0.0,
      "negative_score": 1.0,
      "confidence": 0.2
    }
  }
}
```

---

### 8. 获取反馈类型列表

**GET** `/api/v1/feedback/types`

获取所有可用的反馈类型。

#### 响应

```json
{
  "success": true,
  "data": {
    "types": [
      {"value": "bug_report", "label": "错误报告"},
      {"value": "feature_request", "label": "功能请求"},
      ...
    ]
  }
}
```

---

### 9. 获取反馈状态列表

**GET** `/api/v1/feedback/statuses`

获取所有可用的反馈状态。

#### 响应

```json
{
  "success": true,
  "data": {
    "statuses": [
      {"value": "pending", "label": "待处理"},
      {"value": "resolved", "label": "已解决"},
      ...
    ]
  }
}
```

---

### 10. 获取反馈优先级列表

**GET** `/api/v1/feedback/priorities`

获取所有可用的反馈优先级。

#### 响应

```json
{
  "success": true,
  "data": {
    "priorities": [
      {"value": "critical", "label": "紧急"},
      {"value": "high", "label": "高"},
      {"value": "medium", "label": "中"},
      {"value": "low", "label": "低"}
    ]
  }
}
```

---

### 11. 获取反馈统计

**GET** `/api/v1/feedback/statistics`

获取反馈统计数据。

#### 查询参数

| 参数 | 类型 | 说明 |
|------|------|------|
| `days` | integer | 统计天数（默认30） |

#### 响应

```json
{
  "success": true,
  "data": {
    "total_feedbacks": 150,
    "by_type": {
      "bug_report": 45,
      "feature_request": 30,
      "general": 25,
      ...
    },
    "by_status": {
      "pending": 10,
      "resolved": 100,
      "closed": 40
    },
    "by_priority": {
      "critical": 5,
      "high": 20,
      "medium": 80,
      "low": 45
    },
    "avg_resolution_hours": 48.5,
    "resolved_count": 100,
    "satisfaction_distribution": {
      "5": 60,
      "4": 30,
      "3": 8,
      "2": 2
    }
  }
}
```

---

### 12. 获取反馈趋势

**GET** `/api/v1/feedback/trends`

获取反馈趋势数据。

#### 查询参数

| 参数 | 类型 | 说明 |
|------|------|------|
| `days` | integer | 天数（默认30，范围7-365） |
| `group_by` | string | 分组方式：`day`, `week`, `month` |

#### 响应

```json
{
  "success": true,
  "data": {
    "trends": [
      {"period": "2026-04-01", "count": 5},
      {"period": "2026-04-02", "count": 8},
      {"period": "2026-04-03", "count": 3}
    ],
    "days": 30,
    "group_by": "day"
  }
}
```

---

### 13. 仪表板摘要

**GET** `/api/v1/feedback/dashboard/summary`

获取反馈仪表板摘要数据。

#### 响应

```json
{
  "success": true,
  "data": {
    "today_count": 5,
    "pending_count": 15,
    "critical_count": 2,
    "week_stats": { ... },
    "recent_feedbacks": [
      {
        "id": 123,
        "title": "搜索功能无法使用",
        "type": "bug_report",
        "priority": "high",
        "status": "under_review",
        "created_at": "2026-04-04T10:30:00"
      }
    ]
  }
}
```

---

### 14. 仪表板概览

**GET** `/api/v1/feedback/dashboard/overview`

获取反馈系统的完整仪表板概览。

#### 响应

```json
{
  "success": true,
  "data": {
    "summary": { ... },
    "month_stats": { ... },
    "week_trends": [ ... ],
    "last_updated": "2026-04-04T15:30:00"
  }
}
```

---

## 错误处理

### 错误响应格式

```json
{
  "detail": "错误描述信息"
}
```

### 常见错误码

| HTTP状态码 | 说明 |
|------------|------|
| 400 | 请求参数错误 |
| 404 | 反馈不存在 |
| 500 | 服务器内部错误 |

---

## 使用示例

### 示例1：提交反馈并获取自动分类

```bash
# 提交反馈
curl -X POST "" \
  -H "Content-Type: application/json" \
  -d '{
    "title": "建议增加公式导出功能",
    "content": "希望能够将搜索结果中的数学公式导出为LaTeX或MathML格式"
  }'

# 响应将包含自动分类结果
# feedback_type 会是 "feature_request"
```

### 示例2：查询待处理的紧急反馈

```bash
curl ""
```

### 示例3：获取近7天趋势

```bash
curl ""
```

---

## 注意事项

1. **匿名反馈**：`user_id` 参数可为空，支持匿名反馈
2. **自动分类**：未指定类型时系统自动分类，分类结果保存在 `auto_classified_type`
3. **置信度**：`classification_confidence` 表示自动分类的可信度（0-1）
4. **分页**：列表接口默认返回20条，最大支持100条
5. **时区**：所有时间均为 UTC 格式
