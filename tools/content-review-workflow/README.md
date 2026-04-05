---
title: 内容审核工作流系统
msc_primary: 00A99
processed_at: '2026-04-05'
---
# 内容审核工作流系统

Content Review Workflow System

## 概述

内容审核工作流系统提供完整的自动化内容质量审核流程，包括自动质量检查、人工审核流程、状态追踪和报告生成等功能。

## 系统组件

```
content-review-workflow/
├── review_workflow.py      # 主工作流控制模块
├── quality_checker.py      # 内容质量检查器
├── review_tracker.py       # 审核状态追踪系统
├── manual_review.py        # 人工审核流程
├── report_generator.py     # 审核报告生成器
├── review_rules.yaml       # 审核规则配置
├── README.md               # 本文件
└── WORKFLOW.md             # 工作流详细文档
```

## 快速开始

### 1. 安装依赖

系统依赖 Python 3.8+，无需额外安装第三方库（使用标准库）。

### 2. 提交文档审核

```bash
python review_workflow.py submit <文档路径> --submitter <用户名>
```

示例：
```bash
python review_workflow.py submit docs/algebra/group.md --submitter alice
```

### 3. 查看审核状态

```bash
python review_workflow.py status <文档ID>
```

### 4. 人工审核

```bash
python review_workflow.py review <文档ID> --reviewer <审核员> --decision <approve/revise/reject>
```

示例：
```bash
python review_workflow.py review abc123 --reviewer bob --decision approve --comment "内容准确，格式规范"
```

### 5. 查看待审核列表

```bash
python review_workflow.py pending
```

### 6. 生成报告

```bash
# 汇总报告
python review_workflow.py report summary --output report.html --format html

# 趋势报告
python review_workflow.py report trend --output trend.json --days 30
```

## 审核流程

### 三级审核体系

1. **一级自动审核 (level_1_auto)**
   - 全自动质量检查
   - 质量得分 ≥ 90 且无误自动通过
   - 质量得分 < 30 或错误过多自动拒绝
   - 其余情况进入人工审核

2. **二级半自动审核 (level_2_semi)**
   - 必须人工审核
   - 需要1名审核员确认
   - 适合重要内容更新

3. **三级人工审核 (level_3_manual)**
   - 完全人工审核
   - 需要2名审核员确认
   - 适合关键内容或新分类

### 审核状态流转

```
待审核 (pending) → 审核中 (in_review) → 已通过 (approved) → 已发布 (published)
       ↓                ↓
   已拒绝 (rejected)  需修改 (needs_revision) → 待审核 (pending)
```

## 质量检查规则

### 结构检查
- YAML frontmatter 完整性
- 必需字段检查 (concept_id, concept_name, category, created_date)
- 章节完整性检查

### 内容检查
- 最小内容长度 (200字符)
- 术语一致性
- 数学公式语法

### 格式检查
- Markdown 格式规范
- 代码块语言标记
- 链接有效性

## 配置文件

创建 `config.json` 自定义系统行为：

```json
{
  "auto_approve_threshold": 90,
  "auto_reject_threshold": 30,
  "notification_enabled": true,
  "review_levels": {
    "level_1_auto": {"auto": true, "min_score": 80},
    "level_2_semi": {"auto": false, "min_approvers": 1},
    "level_3_manual": {"auto": false, "min_approvers": 2}
  }
}
```

## API 使用

### 在 Python 代码中使用

```python
from review_workflow import ContentReviewWorkflow

# 初始化工作流
workflow = ContentReviewWorkflow()

# 提交文档
result = workflow.submit_document("docs/test.md", "alice")
print(f"文档ID: {result['document_id']}")

# 审核文档
review_result = workflow.review_document(
    result['document_id'],
    "bob",
    "approve",
    "审核通过"
)

# 生成报告
workflow.generate_report("summary", "report.html", format="html", days=7)
```

## 报告类型

### 汇总报告 (summary)
展示整体审核统计信息，包括：
- 文档总数和各状态分布
- 近期活动统计
- 积压项目
- 审核员工作量

### 文档报告 (document)
单个文档的详细审核记录，包括：
- 文档基本信息
- 审核时间线
- 所有审核事件

### 审核员报告 (reviewer)
审核员工作统计，包括：
- 审核数量统计
- 通过率
- 最近活动

### 趋势报告 (trend)
时间趋势分析，包括：
- 每日提交数量
- 每日完成数量
- 审核效率趋势

## 批量处理

批量审核目录中的所有文档：

```bash
python review_workflow.py batch <目录> --reviewer <审核员>
```

示例：
```bash
python review_workflow.py batch docs/algebra/ --reviewer bob
```

## 数据存储

审核记录默认存储在工作流目录下的 `data/review_records.json` 中。可以通过修改 `ReviewTracker` 的初始化参数更改存储位置。

## 故障排除

### 文档提交失败
- 检查文档路径是否正确
- 确认文档存在且可读
- 检查 YAML frontmatter 格式

### 状态更新失败
- 确认文档ID存在
- 检查状态转换是否有效
- 查看日志获取详细信息

### 质量检查问题
- 检查文档编码（应为UTF-8）
- 验证 Markdown 语法
- 确认 YAML frontmatter 格式正确

## 贡献指南

1. 遵循现有代码风格
2. 添加适当的日志记录
3. 更新文档和示例
4. 测试所有功能路径

## 许可证

MIT License
