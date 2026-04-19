---
title: FormalMath 元数据标准规范 v1.0
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 元数据标准规范 v1.0

## 1. 概述

本文档定义 FormalMath 项目中所有 Markdown 文件的元数据标准，旨在建立统一的文档管理体系，支持自动化处理、查询和分析。

## 2. 元数据格式

元数据使用 YAML Front Matter 格式，位于文档开头，由三个短横线 `---` 包围：

```yaml
---
key1: value1
key2: value2
---
```

## 3. 核心元数据字段

### 3.1 必需字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `title` | string | 文档标题 | 群论基础 |
| `created_date` | date | 创建日期 | 2025-01-15 |
| `version` | string | 版本号 | 1.0.0 |

### 3.2 分类字段

| 字段 | 类型 | 说明 | 可选值 |
|------|------|------|--------|
| `msc_primary` | string | MSC主分类 | 00A99, 20-01, 54-XX |
| `msc_secondary` | array | MSC次分类 | [20D20, 20E99] |
| `category` | string | 内容分类 | 基础数学, 代数结构, 分析学, 几何学, 拓扑学, 数论, 逻辑学, 计算数学, 形式化证明, 语义模型, 高级数学, 应用数学 |
| `difficulty` | string | 难度等级 | L0, L1, L2, L3, L4 |
| `depth_level` | string | 深度等级 | 基础版, 增强版, 深度扩展版, 国际标准版 |

### 3.3 作者与贡献字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `author` | string | 主要作者 | AI Assistant |
| `reviewers` | array | 审核人员 | [Reviewer A, Reviewer B] |
| `contributors` | array | 贡献者 | [Contributor X] |

### 3.4 状态字段

| 字段 | 类型 | 说明 | 可选值 |
|------|------|------|--------|
| `status` | string | 文档状态 | draft, review, published, deprecated, archived |
| `quality_score` | number | 质量评分 | 0-100 |
| `completeness` | string | 完整度 | complete, partial, stub, template |

### 3.5 关联字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `related_concepts` | array | 相关概念 | [群, 环, 域] |
| `prerequisites` | array | 前置知识 | [集合论, 逻辑基础] |
| `next_topics` | array | 后续主题 | [群作用, Sylow定理] |
| `related_mathematicians` | array | 相关数学家 | [伽罗瓦, 阿贝尔] |
| `courses_mapped` | array | 映射课程 | [MIT 18.701, Harvard Math 122] |

### 3.6 内容字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `word_count` | number | 字数统计 | 3500 |
| `reading_time` | number | 预计阅读时间(分钟) | 15 |
| `has_proofs` | boolean | 是否包含证明 | true |
| `has_examples` | boolean | 是否包含例子 | true |
| `has_exercises` | boolean | 是否包含习题 | false |
| `has_lean4` | boolean | 是否含Lean4形式化 | false |
| `has_visualization` | boolean | 是否有可视化内容 | false |

### 3.7 版本控制字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `last_modified` | datetime | 最后修改时间 | 2025-04-03T10:30:00Z |
| `modification_history` | array | 修改历史 | 见下文格式 |
| `git_commit` | string | Git提交哈希 | a1b2c3d |

### 3.8 质量检查字段

| 字段 | 类型 | 说明 | 示例 |
|------|------|------|------|
| `quality_checks` | object | 质量检查项 | 见下文格式 |
| `validated_by` | string | 验证人员 | Validator Name |
| `validated_date` | date | 验证日期 | 2025-04-01 |

## 4. 完整示例

```yaml
---
title: 群论基础
created_date: 2025-01-15
version: 1.2.0
msc_primary: 20-01
msc_secondary: [20A05, 20B30]
category: 代数结构
difficulty: L2
depth_level: 深度扩展版
author: AI Assistant
reviewers: [Math Expert A]
status: published
quality_score: 95
completeness: complete
related_concepts: [群, 子群, 同态, 同构]
prerequisites: [集合论, 二元运算]
next_topics: [正规子群, 商群, Sylow定理]
related_mathematicians: [伽罗瓦, 阿贝尔, 凯莱]
courses_mapped: [MIT 18.701, Harvard Math 122]
word_count: 5200
reading_time: 25
has_proofs: true
has_examples: true
has_exercises: true
has_lean4: true
has_visualization: false
last_modified: 2025-04-03T10:30:00Z
modification_history:
  - date: 2025-01-15
    version: 1.0.0
    changes: 初始创建
  - date: 2025-03-10
    version: 1.1.0
    changes: 添加Lean4形式化
  - date: 2025-04-03
    version: 1.2.0
    changes: 补充证明细节
git_commit: a1b2c3d
quality_checks:
  content_completeness: true
  proof_correctness: true
  notation_consistency: true
  reference_validity: true
  msc_accuracy: true
validated_by: Senior Reviewer
validated_date: 2025-04-01
---
```

## 5. 修改历史格式

```yaml
modification_history:
  - date: YYYY-MM-DD
    version: x.y.z
    changes: 变更描述
    author: 修改人
  - date: YYYY-MM-DD
    version: x.y.z
    changes: 变更描述
    author: 修改人
```

## 6. 质量检查项格式

```yaml
quality_checks:
  content_completeness: boolean      # 内容完整性
  proof_correctness: boolean         # 证明正确性
  notation_consistency: boolean      # 符号一致性
  reference_validity: boolean        # 引用有效性
  msc_accuracy: boolean              # MSC分类准确性
  format_compliance: boolean         # 格式合规性
  link_integrity: boolean            # 链接完整性
  image_accessibility: boolean       # 图片可访问性
  terminology_standard: boolean      # 术语标准化
  accessibility_wcag: boolean        # WCAG无障碍标准
```

## 7. 版本号规范

使用语义化版本控制 (SemVer):

- **MAJOR** (x.0.0): 重大结构变更，不向后兼容
- **MINOR** (x.y.0): 功能新增，向后兼容
- **PATCH** (x.y.z): Bug修复或小幅更新，向后兼容

## 8. 难度等级定义

| 等级 | 名称 | 描述 | 适用对象 |
|------|------|------|----------|
| L0 | 直观经验层 | 基于直觉和经验的数学概念 | 初学者 |
| L1 | 形式化定义层 | 严格的数学定义 | 大学低年级 |
| L2 | 定理证明层 | 定理及其证明 | 大学高年级 |
| L3 | 理论建构层 | 理论体系构建 | 研究生 |
| L4 | 前沿研究层 | 前沿研究主题 | 研究者 |

## 9. 深度等级定义

| 等级 | 后缀 | 描述 |
|------|------|------|
| 基础版 | -基础版.md | 概念介绍，适合初学者 |
| 增强版 | -增强版.md | 包含定理和例子，适合中级学习者 |
| 深度扩展版 | -深度扩展版.md | 完整证明，适合高级学习者 |
| 国际标准版 | -国际标准版.md | 对齐国际标准，适合所有学习者 |

## 10. 状态定义

| 状态 | 说明 |
|------|------|
| draft | 草稿，尚未完成 |
| review | 审核中，等待审核 |
| published | 已发布，正式使用 |
| deprecated | 已弃用，不再推荐 |
| archived | 已归档，仅作历史参考 |

## 11. 校验规则

1. **必需字段校验**: title, created_date, version 必须存在
2. **日期格式校验**: 使用 ISO 8601 格式 (YYYY-MM-DD)
3. **MSC格式校验**: 符合 Mathematics Subject Classification 标准
4. **版本格式校验**: 符合 SemVer 规范 (x.y.z)
5. **难度等级校验**: 必须是 L0, L1, L2, L3, L4 之一
6. **状态校验**: 必须是定义的五种状态之一

## 12. 扩展字段

项目可根据需要添加自定义字段，但应遵循以下原则：

1. 使用小写字母和下划线命名
2. 添加注释说明字段用途
3. 避免与标准字段冲突
4. 在团队内保持一致性
