# FormalMath Translation Workflow

翻译协作流程指南

---

## 🔄 翻译工作流程

### 阶段一：任务认领

1. **查看待办任务**
   ```bash
   # 查看待翻译文档列表
   python tools/translation_checker.py --todo
   ```

2. **创建任务Issue**
   - 标题格式: `[翻译] 概念名 - 目标语言`
   - 示例: `[翻译] 连续性 - 德文`

3. **分配任务**
   - 在Issue中 @自己 认领
   - 设置截止日期

### 阶段二：翻译准备

1. **查阅术语标准**
   - 参考 [00-标准术语表-8语言.md](../../00-标准术语表-8语言.md)
   - 确认专业术语译法

2. **准备工作环境**
   ```bash
   # 创建翻译分支
   git checkout -b translation/limit-de
   
   # 复制模板
   cp templates/concept_template.md i18n/de/core/Grenzwert.md
   ```

### 阶段三：翻译执行

#### 文档结构模板

```markdown
---
msc_primary: XX-XX
msc_secondary: ['XX-XXX']
lang: [语言代码]
original: [原文档路径]
translation_status: in_progress
translator: [你的名字]
date: YYYY-MM-DD
---

# [标题]

## 定义
[数学定义]

## 性质/定理
[重要性质]

## 应用
[实际应用]

## 相关概念
[链接到其他概念]

---

**语言版本**: [语言链接列表]
```

#### 翻译检查清单

- [ ] 术语使用正确
- [ ] 数学公式格式正确
- [ ] 包含语言切换链接
- [ ] YAML frontmatter 完整
- [ ] 代码块格式正确

### 阶段四：质量检查

```bash
# 运行质量检查
python tools/translation_checker.py docs/i18n/de/core/Grenzwert.md

# 查看检查结果
# 确保没有 Error 级别的问题
```

#### 自动检查项目

| 检查项 | 级别 | 说明 |
|--------|------|------|
| Frontmatter 完整 | Error | 必须包含 lang, original, translation_status |
| 语言一致性 | Error | 声明语言与路径一致 |
| 数学公式格式 | Warning | 检查未闭合的 $ |
| 内部链接有效性 | Warning | 检查相对链接 |
| 语言切换链接 | Warning | 检查多语言链接 |

### 阶段五：提交审核

1. **提交Pull Request**
   ```bash
   git add docs/i18n/de/core/Grenzwert.md
   git commit -m "[翻译] 添加德文版极限概念文档"
   git push origin translation/limit-de
   ```

2. **PR 描述模板**
   ```markdown
   ## 翻译内容
   - 概念: 极限 (Limit)
   - 目标语言: 德文 (de)
   - 原文档: docs/.../极限.md

   ## 质量检查
   - [x] 已通过 translation_checker.py
   - [x] 术语一致性检查
   - [x] 链接有效性检查

   ## 备注
   [任何需要审阅者注意的事项]
   ```

3. **审核流程**
   - 机器检查: 自动运行 checker
   - 同行评审: 至少1位审阅者
   - 专家审核: 数学内容准确性

### 阶段六：合并发布

1. **通过审核后**
   - 更新 `translation_status` 为 `completed`
   - 更新多语言索引 `multilang_index.json`
   - 合并到主分支

2. **更新质量报告**
   ```bash
   python tools/translation_checker.py docs/i18n/ --report
   ```

---

## 📋 翻译任务看板

### 当前进行中的任务

| 概念 | 德文 | 法文 | 日文 | 英文 | 负责人 |
|------|------|------|------|------|--------|
| 群 | ✅ | ✅ | ✅ | ✅ | - |
| 环 | ✅ | ✅ | ✅ | ✅ | - |
| 域 | ✅ | ✅ | ✅ | ✅ | - |
| 极限 | ✅ | ✅ | ✅ | ✅ | - |
| 连续性 | 📋 | 📋 | 📋 | 📋 | 待认领 |
| 导数 | 📋 | 📋 | 📋 | 📋 | 待认领 |

### 优先级说明

- **P0 (紧急)**: 核心代数结构 - 已完成
- **P1 (高)**: 分析学基础概念
- **P2 (中)**: 拓扑学、几何学概念
- **P3 (低)**: 应用案例、历史背景

---

## 🛠️ 工具使用指南

### 语言切换工具

```bash
# 查看文档的所有语言版本
python tools/lang_switcher.py docs/i18n/en/core/Group.md

# 输出示例:
# Current document: docs/i18n/en/core/Group.md
# Current language: en (English)
# 
# Available language versions:
#   [✓] de (Deutsch): docs/i18n/de/core/Gruppe.md
#   [✓] fr (Français): docs/i18n/fr/core/Groupe.md
#   [✓] ja (日本語): docs/i18n/ja/core/群.md
```

### 批量检查

```bash
# 检查整个i18n目录
python tools/translation_checker.py docs/i18n/

# 生成详细报告
python tools/translation_checker.py docs/i18n/ --verbose
```

---

## 📊 质量标准

### 术语一致性要求

- 核心术语必须与标准术语表一致
- 人名使用标准译名
- 定理名称统一

### 格式规范

- 使用标准Markdown格式
- 数学公式使用LaTeX语法
- 表格对齐正确

### 内容准确性

- 数学定义准确无误
- 定理陈述完整
- 符号使用一致

---

## 🆘 常见问题

### Q: 如何处理多义词？
A: 根据上下文选择合适译法，在术语表中记录。

### Q: 发现术语表错误？
A: 提交Issue标记为 `[术语]`，讨论后统一修改。

### Q: 数学公式如何翻译？
A: 数学符号不翻译，仅翻译说明文字。

### Q: 链接到未翻译的文档？
A: 暂时链接到中文原文，待翻译完成后再更新。

---

**Maintainers**: FormalMath i18n Team  
**Last Updated**: 2026-04-04
