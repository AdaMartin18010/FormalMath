---
title: FormalMath Internationalization (i18n)
msc_primary: 00

  - 00A99
processed_at: '2026-04-05'
---
# FormalMath Internationalization (i18n)

FormalMath 多语言支持系统

---

## 📁 目录结构

```
docs/i18n/
├── README.md                 # 本文件
├── de/                       # 德文文档
│   └── core/                 # 核心概念
│       ├── Gruppe.md
│       ├── Ring.md
│       └── Körper.md
├── en/                       # 英文文档
│   └── core/
│       ├── Group.md
│       ├── Ring.md
│       └── Field.md
├── fr/                       # 法文文档
│   └── core/
│       ├── Groupe.md
│       ├── Anneau.md
│       └── Corps.md
├── ja/                       # 日文文档
│   └── core/
│       ├── 群.md
│       ├── 環.md
│       └── 体.md
├── tools/                    # 翻译工具
│   ├── lang_switcher.py      # 语言切换工具
│   └── translation_checker.py # 质量检查工具
└── qa/                       # 质量报告
    └── translation_quality_report.md
```

---

## 🌐 支持的语言

| 代码 | 语言 | 状态 | 覆盖率 |
|------|------|------|--------|
| zh | 中文 | ✅ 完整 | 100% |
| en | English | 🔄 进行中 | 30% |
| de | Deutsch | 🔄 进行中 | 15% |
| fr | Français | 🔄 进行中 | 15% |
| ja | 日本語 | 🔄 进行中 | 15% |
| ru | Русский | 📋 计划 | 0% |
| it | Italiano | 📋 计划 | 0% |
| es | Español | 📋 计划 | 0% |

---

## 🛠️ 使用工具

### 语言切换工具

```bash
# 显示文档的所有语言版本
python tools/lang_switcher.py docs/i18n/en/core/Group.md

# 切换到特定语言版本
python tools/lang_switcher.py docs/i18n/en/core/Group.md de
```

### 翻译质量检查

```bash
# 检查单个文件
python tools/translation_checker.py docs/i18n/de/core/Gruppe.md

# 检查整个目录并生成报告
python tools/translation_checker.py docs/i18n/
```

---

## 📝 翻译规范

### 文档头部格式

每个翻译文档必须包含以下YAML frontmatter：

```yaml
---
msc_primary: 20-00
msc_secondary: ['20A05']
lang: de
original: docs/02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md
translation_status: completed|in_progress|review_needed
translator: Your Name
date: 2026-04-04
---
```

### 语言切换链接

每篇文档末尾必须包含语言切换链接：

```markdown
---

**Sprachversionen**: [English](./en/core/Group.md) | [Français](./fr/core/Groupe.md) | [日本語](./ja/core/群.md) | [中文](./../02-代数结构/02-核心理论/群论/01-群论-国际标准深度扩展版.md)
```

---

## 🤝 贡献指南

### 翻译流程

1. **认领任务**: 在issues中认领翻译任务
2. **准备术语**: 查阅标准术语表
3. **翻译文档**: 遵循翻译规范
4. **质量检查**: 运行checker工具
5. **提交审核**: 创建Pull Request

### 翻译优先级

1. **核心概念** (P0): 群、环、域、向量空间
2. **基础定理** (P1): Lagrange定理、同构定理等
3. **扩展内容** (P2): 应用案例、历史背景

---

## 📊 质量指标

| 指标 | 目标值 | 当前值 |
|------|--------|--------|
| 术语一致性 | >95% | 92% |
| 格式规范率 | >98% | 95% |
| 链接有效性 | >99% | 100% |
| 文档完整度 | >90% | 25% |

---

## 📚 相关文档

- [翻译贡献指南](../00-贡献者指南/翻译贡献指南.md)
- [标准术语表](../../00-标准术语表-8语言.md)
- [多语言概念表](../../multilang_concept_table.json)

---

**Maintainers**: FormalMath i18n Team  
**Last Updated**: 2026-04-04
