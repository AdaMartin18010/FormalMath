---
title: FormalMath 邮件通知系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath 邮件通知系统

## 概述

邮件通知系统提供完整的邮件发送、模板管理、队列处理和统计追踪功能。支持 SendGrid、AWS SES 和 SMTP 三种邮件服务提供商。

## 功能特性

- **多提供商支持**: SendGrid、AWS SES、SMTP
- **模板系统**: 内置多语言模板，支持自定义模板
- **队列处理**: 基于 Celery 的异步邮件发送
- **统计追踪**: 实时发送统计、打开率、点击率
- **用户偏好**: 个性化通知设置
- **防重复发送**: 冷却时间机制
- **速率限制**: 防止滥用

## 目录结构

```
notifications/
├── __init__.py              # 模块导出
├── email_service.py         # 邮件服务核心
├── template_manager.py      # 模板管理系统
├── notification_triggers.py # 通知触发逻辑
├── email_tasks.py           # Celery 任务
├── email_stats.py           # 统计追踪
├── templates/               # 模板文件目录
└── README.md                # 使用文档
```

## 快速开始

### 1. 配置环境变量

```bash
# 选择邮件提供商
EMAIL_PROVIDER=sendgrid

# SendGrid 配置
SENDGRID_API_KEY=your_api_key

# 发件人配置
EMAIL_FROM_NAME=FormalMath
EMAIL_FROM_ADDRESS=noreply@formalmath.edu
```

### 2. 启动 Celery Worker

```bash
celery -A app.tasks.celery_app worker -Q email_notifications -l info
```

### 3. 发送邮件

```python
from app.notifications import get_email_service

email_service = get_email_service()
result = await email_service.send_email(
    to_addresses=["user@example.com"],
    subject="欢迎加入 FormalMath",
    html_content="<h1>欢迎！</h1>",
)
```

## 内置模板

| 模板名称 | 描述 | 变量 |
|---------|------|------|
| welcome | 欢迎邮件 | username, verification_link |
| verification | 邮箱验证 | username, verification_code, expires_minutes |
| password_reset | 密码重置 | username, reset_link, expires_hours |
| learning_reminder | 学习提醒 | username, streak_days, recommended_concepts |
| achievement_unlocked | 成就解锁 | username, achievement_name, achievement_description |
| learning_path_complete | 路径完成 | username, path_name, completed_nodes, total_nodes |
| weekly_report | 周报 | username, week_start, week_end, study_hours... |
| new_follower | 新关注者 | username, follower_name, follower_profile_link |
| challenge_invitation | 挑战邀请 | username, challenger_name, challenge_name... |
| system_maintenance | 系统维护 | maintenance_time, expected_duration, affected_services |
| security_alert | 安全警报 | username, login_time, login_location, device_info |

## API 端点

### 发送邮件

```http
POST /api/v1/notifications/send
Content-Type: application/json

{
  "to_addresses": ["user@example.com"],
  "subject": "主题",
  "html_content": "<h1>HTML 内容</h1>",
  "use_queue": false
}
```

### 使用模板发送

```http
POST /api/v1/notifications/send-template
Content-Type: application/json

{
  "to_addresses": ["user@example.com"],
  "template_name": "welcome",
  "template_variables": {
    "username": "张三",
    "verification_link": "https://...[需更新]"
  },
  "language": "zh_CN"
}
```

### 触发特定通知

```http
POST /api/v1/notifications/trigger/welcome
?user_email=user@example.com
&username=张三
&verification_link=https://...[需更新]
```

### 查看统计

```http
# 实时统计
GET /api/v1/notifications/stats/realtime

# 汇总统计
GET /api/v1/notifications/stats/summary?days=30

# 每日统计
GET /api/v1/notifications/stats/daily/2024-01-01
```

### 管理用户偏好

```http
# 获取偏好
GET /api/v1/notifications/preferences/123

# 更新偏好
PUT /api/v1/notifications/preferences/123
Content-Type: application/json

{
  "welcome": true,
  "learning_reminder": false,
  "marketing": false
}
```

## 通知触发器使用

```python
from app.notifications import get_notification_trigger

trigger = get_notification_trigger()

# 发送欢迎邮件
await trigger.send_welcome_email(
    user_email="user@example.com",
    username="张三",
    verification_link="https://...[需更新]",
    language="zh_CN",
)

# 发送学习提醒
await trigger.send_learning_reminder(
    user_id=123,
    user_email="user@example.com",
    username="张三",
    streak_days=7,
    recommended_concepts=["微积分", "线性代数"],
)

# 发送成就解锁通知
await trigger.send_achievement_unlocked(
    user_id=123,
    user_email="user@example.com",
    username="张三",
    achievement_name="初学有成",
    achievement_description="连续学习7天",
    badge_icon="🏆",
)
```

## 队列管理

```python
from app.notifications.email_tasks import (
    enqueue_email,
    enqueue_template_email,
    get_queue_status,
)

# 添加邮件到队列
tracking_id = await enqueue_email(
    to_addresses=["user@example.com"],
    subject="主题",
    html_content="<h1>内容</h1>",
)

# 添加模板邮件到队列
tracking_id = await enqueue_template_email(
    to_addresses=["user@example.com"],
    template_name="welcome",
    template_variables={"username": "张三"},
)

# 查看队列状态
status = await get_queue_status()
```

## 统计追踪

```python
from app.notifications import get_email_stats_manager

stats_manager = get_email_stats_manager()

# 获取每日统计
daily_stats = await stats_manager.get_daily_stats("2024-01-01")

# 获取汇总统计
summary = await stats_manager.get_summary_stats(days=30)

# 获取实时统计
realtime = await stats_manager.get_realtime_stats()

# 获取发送记录
record = await stats_manager.get_send_record(tracking_id)

# 记录打开事件
await stats_manager.record_open_event(tracking_id)

# 记录点击事件
await stats_manager.record_click_event(tracking_id, "https://...[需更新]")
```

## 邮件追踪

在 HTML 模板中添加追踪像素：

```html
<img src="https://api.formalmath.edu/api/v1/notifications/track/open/{tracking_id}[需更新]" 
     width="1" height="1" alt="" />
```

添加点击追踪：

```html
<a href="https://api.formalmath.edu/api/v1/notifications/track/click/{tracking_id}?url=https://...[需更新]">
  点击这里
</a>
```

## 定时任务

```python
# settings.py 或 celery beat 配置
from celery.schedules import crontab

celery_app.conf.beat_schedule = {
    # 每小时处理邮件队列
    'process-email-queue': {
        'task': 'app.notifications.email_tasks.process_email_queue_task',
        'schedule': 300.0,  # 每5分钟
    },
    # 每周发送学习报告
    'send-weekly-reports': {
        'task': 'app.notifications.tasks.send_weekly_reports',
        'schedule': crontab(hour=9, minute=0, day_of_week=1),  # 每周一上午9点
    },
    # 每日发送学习提醒
    'send-daily-reminders': {
        'task': 'app.notifications.tasks.send_daily_reminders',
        'schedule': crontab(hour=9, minute=0),  # 每天上午9点
    },
    # 清理过期统计数据
    'cleanup-email-stats': {
        'task': 'app.notifications.email_tasks.cleanup_old_email_stats_task',
        'schedule': crontab(hour=2, minute=0),  # 每天凌晨2点
    },
}
```

## 最佳实践

1. **使用队列**: 对于批量发送或不需要即时送达的邮件，使用队列处理
2. **设置冷却时间**: 防止重复发送相同类型的通知
3. **尊重用户偏好**: 检查用户的通知设置后再发送
4. **监控统计**: 定期检查发送成功率和打开率
5. **处理退信**: 及时处理退信和垃圾邮件投诉

## 故障排查

### 邮件发送失败

1. 检查邮件提供商配置是否正确
2. 查看 Celery Worker 日志
3. 检查速率限制是否超出
4. 验证收件人地址是否有效

### 模板渲染失败

1. 检查模板名称是否正确
2. 确保提供了所有必需的变量
3. 查看模板变量类型是否匹配

### 统计不更新

1. 检查 Redis 连接
2. 确认 Celery 任务正常执行
3. 查看任务结果和错误日志

## 扩展开发

### 添加新模板

1. 在 `TemplateManager.BUILTIN_TEMPLATES` 中定义模板信息
2. 在 `_get_template_content_map` 中添加内容映射
3. 在 `NotificationTrigger` 中添加触发方法

### 添加新提供商

1. 继承 `EmailProvider` 基类
2. 实现 `send_email` 方法
3. 在 `EmailService._init_provider` 中添加初始化逻辑

## 许可证

MIT License
