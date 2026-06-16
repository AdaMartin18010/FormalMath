---
title: Phase 1 Sprint 2 启动报告
level: meta
msc_primary: 00A99
processed_at: '2026-06-16'
review_status: draft
---

# Phase 1 Sprint 2 启动报告

**日期**: 2026年06月16日  
**目标**: 对 5 门银层核心课程建立 L1-L6 语义对齐矩阵，并完成 frontmatter / 参考文献的基线规范化。

---

## 已完成工作

### 1. 内容质量评估标准 v2

- 文件: `docs/00-贡献者指南/内容质量评估标准-v2.md`
- 确立了 5 项可验证质量指标：定理-证明覆盖率、定义严格性得分、习题-解答对数量、原始文献引用密度、形式化-自然语言桥梁度。
- 建立了六级语义对齐验证清单（L1-L6）。

### 2. 全库抽样审计脚本与报告

- 脚本: `scripts/phase1_content_audit.py`
- 报告: `project/00-项目进度报告/Phase1-内容质量审计报告.md`
- 抽样 300 篇文档，覆盖银层课程、concept、数学家体系、其他 docs。

**关键基线数据**:

| 指标 | 初始值 | 规范化后 |
|------|-------|---------|
| 含 external_ids 文档比例 | 0.0% | 18.3% |
| 缺少必要 frontmatter 字段 | 83/300 | 54/300 |
| 平均精确引用标识符密度 | 0.09 条/千字 | - |
| 定义/定理/证明覆盖率 | 74.7% / 72.3% / 72.0% | - |
| 习题解答覆盖率 | 39.3% | - |

### 3. 五门核心课程 L1-L6 对齐矩阵

- 目录: `project/00-项目进度报告/Phase1-Sprint2-五门核心课程对齐矩阵/`
- 生成文件:
  - `MIT-18.06-线性代数-L1-L6-对齐矩阵.md`
  - `MIT-18.100A-实分析-L1-L6-对齐矩阵.md`
  - `MIT-18.701-抽象代数-L1-L6-对齐矩阵.md`
  - `Harvard-232br-代数几何-L1-L6-对齐矩阵.md`
  - `Stanford-FOAG-基础代数几何-L1-L6-对齐矩阵.md`
- 每份矩阵包含：
  - 课程元数据（OCW 链接、教材 ISBN、MSC 分类）
  - 现有文档的 L1-L2 映射与结构要素检查
  - 缺口汇总
  - L3-L6 待办清单
  - 外部资源 frontmatter 模板

### 4. 银层课程 frontmatter 规范化

- 脚本: `scripts/normalize_silver_frontmatter.py`
- 更新了 79 篇银层核心课程文档，补充：
  - `level: silver`
  - `course` 名称
  - `chapter`（从文件名推断）
  - `msc_primary`
  - `external_ids.ocw_url` / `external_ids.ocw_ps_url`
  - `references.textbooks`（含 ISBN）
- 涉及课程：MIT 18.06 / 18.100A / 18.701 / 18.02、Harvard 232br、Stanford FOAG、Princeton 复分析、Oxford 表示论、UCLA 微分几何。

---

## 主要发现

1. **MIT 18.06 线性代数** 文档结构最完整：15/16 篇达到「完整」状态，主要缺口是缺少精确引用和外部对齐标识。
2. **MIT 18.100A 实分析**、**18.701 抽象代数**、**Harvard 232br**、**Stanford FOAG** 存在较多以定理/概念命名但缺少 `chapter` 字段的文档，需要进一步分类为「章节主体」或「专题补充」。
3. **全库精确引用密度极低**（0.09 条/千字），距离 2~3 条/千字的目标差距大。
4. **重复文档** 89 组 / 178 篇，集中在 `Stanford-FOAG` 的章节变体与 `00-工作示例库` 的平铺目录。
5. **外部对齐标识** 仍需大量人工补全：目前仅注入课程级 OCW 链接，具体到每章的 Lecture / Problem Set / Stacks Tag / nLab URL 仍需按矩阵逐项填充。

---

## 下一步建议

### 选项 A：继续深化 MIT 18.06（推荐作为模板）

把 MIT 18.06 的 15 章全部做到：
- 每章 frontmatter 注入具体 OCW Lecture URL 和对应 Problem Set
- 每章正文补充精确到章节/页码的 Strang 教材引用
- 每章补充 5+ 道带解答的习题（可映射 MIT OCW Problem Sets）
- 输出一份「银层文档标准范例」，复制到其他课程

### 选项 B：并行补齐五门课程的结构化元数据

使用已生成的对齐矩阵，为五门课程批量注入：
- 具体章节 → OCW Lecture / Problem Set / Exam 链接
- 定义/定理 → Wikipedia / nLab / Stacks Project / MathWorld 链接
- 缺失 `chapter` 字段的文档重新分类

### 选项 C：先清理重复与空壳文档

在大量新增内容前，先合并/归档 89 组重复文档，避免资源浪费。

### 选项 D：启动缺失学科课程建设

按照 Phase 1 计划，开始建设概率统计、数值分析、离散数学/组合数学、ODE/PDE 等银层核心课程。

---

## 新增/修改文件清单

```
docs/00-贡献者指南/内容质量评估标准-v2.md
scripts/phase1_content_audit.py
scripts/generate_course_alignment_matrix.py
scripts/normalize_silver_frontmatter.py
project/00-项目进度报告/Phase1-内容质量审计报告.md
project/00-项目进度报告/Phase1-Sprint2-启动报告.md
project/00-项目进度报告/Phase1-Sprint2-五门核心课程对齐矩阵/*.md
docs/00-银层核心课程/*/*.md  (79 篇 frontmatter 更新)
```
