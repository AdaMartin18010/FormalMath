---
title: Phase 1 Sprint 2 — MIT 18.06 银层标准范例完成报告
level: meta
msc_primary: 00A99
processed_at: '2026-06-16'
review_status: draft
---

# Phase 1 Sprint 2 — MIT 18.06 银层标准范例完成报告

**日期**: 2026年06月16日  
**目标**: 将 `MIT 18.06 线性代数` 的 15 章全部提升为银层标准范例，建立可复制模板。

---

## 已完成工作

### 1. 为 15 章注入精确外部对齐

每章 frontmatter 现在包含：

- `external_ids.ocw_url`：课程主页
- `external_ids.ocw_lectures`：具体 OCW Lecture 页面（如 Lecture 1 ~ Lecture 34）
- `external_ids.ocw_problem_sets`：对应 Problem Set PDF
- `references.textbooks`：Strang 教材精确到章节 + ISBN
- `references.lectures`：MIT OCW 讲座元数据
- `references.exams`：Exam 1/2/3 试卷与解答链接
- `prerequisites`：前置章节或课程

### 2. 为每章追加「参考与延伸阅读」正文节

在文末统一追加：
- 教材引用
- MIT OCW 讲座链接
- 对应 Problem Set 与 Exam 链接

### 3. 生成银层文档标准模板

- 文件: `docs/00-贡献者指南/银层文档标准模板.md`
- 包含：frontmatter 模板、正文结构、质量自测清单、参考范例

### 4. 更新对齐矩阵

- `project/00-项目进度报告/Phase1-Sprint2-五门核心课程对齐矩阵/MIT-18.06-线性代数-L1-L6-对齐矩阵.md`
- 15/16 篇文档状态为「完整」，剩余 1 篇为学习诊断手册（可单独处理）。

---

## 关键数据

| 指标 | MIT 18.06 15 章现状 |
|---|---|
| 定义/定理/证明/例题/习题/解答/参考 | 全部 ✅ |
| 含具体 OCW Lecture URL | 15/15 |
| 含 Problem Set 链接 | 15/15 |
| 含 Exam 链接 | 15/15 |
| 含教材 ISBN + 精确章节 | 15/15 |
| 状态「完整」 | 15/16 |

---

## 新增/修改文件

```
docs/00-贡献者指南/银层文档标准模板.md
scripts/enrich_mit1806_alignment.py
scripts/dedup_mit1806_references.py
project/00-项目进度报告/Phase1-Sprint2-五门核心课程对齐矩阵/MIT-18.06-线性代数-L1-L6-对齐矩阵.md
docs/00-银层核心课程/MIT-18.06-线性代数/Ch01.md ~ Ch15.md (frontmatter + 参考节更新)
```

---

## 下一步建议

### 选项 A：推广到 MIT 18.100A / 18.701（推荐）

使用同样脚本范式，为这两门 MIT 核心课程：
1. 建立 Lecture / Problem Set / Exam 映射
2. 注入精确教材引用（Rudin / Artin）
3. 补全缺失 `chapter` 字段并重新分类专题文档

### 选项 B：继续 Harvard 232br / Stanford FOAG

难度更高，但可借助 Stacks Project Tag 和 Vakil FOAG 章节进行语义对齐。

### 选项 C：回到全库治理

在推广前，先完成：
- 清理 89 组重复文档
- 修复 6 篇 frontmatter 解析错误
- 为全库非银层文档补齐 `title`

### 选项 D：启动缺失学科课程

按照 Phase 1 计划，开始建设概率统计、数值分析、离散数学/组合数学、ODE/PDE 等银层核心课程。
