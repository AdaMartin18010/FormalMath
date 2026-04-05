---
msc_primary: 00A99
---

# FormalMath 项目贡献指南

> 🎯 **愿景**：建立全球最大的开源数学教育知识库

欢迎来到 FormalMath 项目！感谢您对开源数学教育事业的贡献。本指南将帮助您快速了解如何参与项目贡献。

---

## 📋 目录

- [快速开始](#快速开始)
- [贡献类型](#贡献类型)
- [贡献流程](#贡献流程)
- [代码规范](#代码规范)
- [内容规范](#内容规范)
- [质量控制](#质量控制)
- [奖励机制](#奖励机制)
- [社区准则](#社区准则)

---

## 🚀 快速开始

### 1. Fork 项目

```bash
# 1. 点击 GitHub 上的 Fork 按钮
# 2. 克隆您的 Fork

git clone https://github.com/YOUR_USERNAME/FormalMath.git
cd FormalMath
```

### 2. 设置上游仓库

```bash
# 添加上游仓库
git remote add upstream https://github.com/original/FormalMath.git

# 验证远程仓库
git remote -v
```

### 3. 创建分支

```bash
# 从 main 分支创建新分支
git checkout main
git pull upstream main

# 创建功能分支
git checkout -b feature/your-feature-name
# 或
git checkout -b fix/issue-description
```

---

## 📝 贡献类型

### 📚 内容贡献

| 类型 | 说明 | 示例 |
|------|------|------|
| **新文档** | 创建新的数学概念文档 | 新增「范畴论」深度扩展版 |
| **文档完善** | 补充证明、示例、图表 | 为「群论」添加更多证明细节 |
| **错误修正** | 修正数学错误、错别字 | 修正定理编号错误 |
| **翻译工作** | 中英文互译 | 将英文教材内容翻译为中文 |
| **课程对齐** | 添加国际课程对应关系 | 添加 MIT 18.705 课程映射 |

### 💻 代码贡献

| 类型 | 说明 | 技能要求 |
|------|------|----------|
| **Lean4 形式化** | 将数学定理形式化 | Lean4 基础 |
| **Python 工具** | 开发自动化工具 | Python 3.8+ |
| **Web 开发** | 学习系统前端/后端 | React/FastAPI |
| **数据可视化** | 创建知识图谱可视化 | D3.js/NetworkX |

### 🔧 维护贡献

| 类型 | 说明 | 频率 |
|------|------|------|
| **Issue 分类** | 标记、分类 Issue | 每日 |
| **PR 审核** | 代码/内容审核 | 每日 |
| **文档审查** | 质量检查 | 每周 |
| **自动化维护** | CI/CD 改进 | 按需 |

---

## 🔄 贡献流程

### 标准贡献流程

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   发现需求   │ -> │   创建 Issue │ -> │  等待反馈   │
└─────────────┘    └─────────────┘    └─────────────┘
                                              │
                                              v
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   合并上线   │ <- │  PR 审核通过 │ <- │  提交 PR    │
└─────────────┘    └─────────────┘    └─────────────┘
```

### 详细步骤

#### 1. 创建 Issue（推荐）

在开始工作前，建议先创建 Issue 讨论您的想法：

- **内容贡献**：使用「内容请求」模板
- **Bug 报告**：使用「错误报告」模板
- **功能请求**：使用「功能请求」模板

#### 2. 本地开发

```bash
# 安装依赖（如有）
pip install -r requirements.txt

# 运行本地检查
python tools/contributor-workflow/pre_commit_check.py

# 提交更改
git add .
git commit -m "type(scope): description"
```

#### 3. 提交 PR

```bash
# 推送到您的 Fork
git push origin feature/your-feature-name

# 在 GitHub 上创建 Pull Request
```

**PR 标题格式**：
```
type(scope): description

# 示例：
docs(algebra): 添加群论第三同构定理证明
fix(sets): 修正基数运算中的错别字
feat(lean): 添加拉格朗日定理形式化证明
```

#### 4. 审核流程

- **自动检查**：CI 运行质量检查
- **人工审核**：维护者审核内容准确性
- **修改反馈**：根据反馈进行修改
- **合并上线**：审核通过后合并

---

## 💻 代码规范

### Lean4 代码规范

```lean4
-- 文件头注释
/-
# 定理名称：拉格朗日定理

## 作者：您的名字
## 创建日期：YYYY-MM-DD
## 关联 Issue：#123

## 数学背景
简要说明定理的数学意义

## 实现说明
说明实现的关键技术点
-/

import Mathlib

-- 定理陈述使用清晰命名
namespace FormalMath

/-- 拉格朗日定理：有限群中子群的阶整除群的阶 -/
theorem lagrange_theorem {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  -- 证明步骤注释
  -- 1. 考虑左陪集分解
  have h1 : Fintype.card G = Fintype.card H * Fintype.card (G ⧸ H) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (quotientGroupEquivQuotient H)
  -- 2. 整除关系直接得出
  exact Dvd.intro _ (Eq.symm h1)

end FormalMath
```

### Python 代码规范

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
模块简要说明

详细功能描述...

作者: 您的名字
创建日期: YYYY-MM-DD
关联 Issue: #123

使用示例:
    >>> from module import function
    >>> result = function()
"""

from typing import List, Optional
from pathlib import Path


def example_function(param1: str, param2: int = 0) -> bool:
    """
    函数功能说明
    
    Args:
        param1: 参数1说明
        param2: 参数2说明，默认为0
    
    Returns:
        返回值说明
    
    Raises:
        ValueError: 错误条件说明
    
    Example:
        >>> example_function("test", 1)
        True
    """
    if not param1:
        raise ValueError("param1 cannot be empty")
    return len(param1) > param2
```

### 提交信息规范

```
类型(范围): 简短描述（50字符以内）

详细描述（如有必要，每行72字符以内）

- 说明变更动机
- 与之前行为的对比
- 关联 Issue 编号

Fixes #123
Related to #456
```

**类型说明**：

| 类型 | 含义 | 示例 |
|------|------|------|
| `feat` | 新功能 | `feat(lean): 添加新定理证明` |
| `fix` | 错误修复 | `fix(docs): 修正数学公式` |
| `docs` | 文档更新 | `docs(readme): 更新使用说明` |
| `style` | 格式调整 | `style(markdown): 统一标题格式` |
| `refactor` | 重构 | `refactor(tools): 优化检查脚本` |
| `test` | 测试相关 | `test(lean): 添加单元测试` |
| `chore` | 构建/工具 | `chore(ci): 更新工作流` |

---

## 📄 内容规范

### Markdown 文档结构

```markdown
---
msc_primary: 20-XX  # MSC2020 主分类
msc_secondary:      # MSC2020 次分类
  - 20Gxx
  - 20Kxx
tags:
  - 群论
  - 抽象代数
level: L2           # L0-L4 知识层次
course_alignment:
  - MIT 18.705
  - Harvard Math 122
---

# 文档标题

> 一句话概括本文档核心内容

---

## 目录

- [概念定义](#概念定义)
- [定理证明](#定理证明)
- [应用示例](#应用示例)
- [参考文献](#参考文献)

---

## 概念定义

### 定义 1.1（示例定义）

**定义内容**...

**直观解释**...

### 命题 1.2（示例命题）

**陈述**...

**证明概要**：...

<details>
<summary>完整证明</summary>

```
详细证明步骤...
```

</details>

---

## 定理证明

### 定理 2.1（主要定理）

**定理陈述**...

**证明思路**：...

**完整证明**：...

**形式化实现**（如有）：
- Lean4: `path/to/lean/file.lean`

---

## 应用示例

### 示例 3.1

**问题**：...

**解答**：...

---

## 参考文献

1. Author, Title, Journal/Book, Year
2. ...

---

**最后更新**: YYYY-MM-DD  
**维护者**: @username
```

### 数学内容标准

1. **术语一致性**：使用项目术语标准词典
2. **符号规范**：遵循国际数学符号标准
3. **证明完整性**：重要定理需给出完整证明或引用
4. **难度标注**：使用 L0-L4 知识层次标注
5. **课程对齐**：标注相关的国际课程

---

## ✅ 质量控制

### 自动化检查

提交前请运行本地检查：

```bash
# 运行所有检查
python tools/contributor-workflow/pre_commit_check.py --all

# 仅检查 Markdown 格式
python tools/contributor-workflow/pre_commit_check.py --markdown

# 仅检查 MSC 编码
python tools/contributor-workflow/pre_commit_check.py --msc

# 仅检查 Lean4 代码
python tools/contributor-workflow/pre_commit_check.py --lean
```

### 检查清单

#### 内容贡献检查清单

- [ ] 文档包含正确的 YAML Frontmatter
- [ ] MSC 分类准确
- [ ] 知识层次标注正确
- [ ] 数学公式使用 LaTeX 格式
- [ ] 引用来源正确标注
- [ ] 无拼写/语法错误
- [ ] 链接可正常访问

#### 代码贡献检查清单

- [ ] 代码通过编译/运行
- [ ] 包含适当的注释
- [ ] 包含单元测试（如适用）
- [ ] 遵循项目代码规范
- [ ] 无警告/错误信息

---

## 🏆 奖励机制

### 贡献积分系统

| 贡献类型 | 基础积分 | 额外奖励 |
|----------|----------|----------|
| 新文档（基础版） | 50 | +20（含完整证明） |
| 新文档（增强版） | 100 | +30（含应用案例） |
| 新文档（深度版） | 200 | +50（含形式化） |
| Lean4 形式化证明 | 300 | +100（通过验证） |
| 错误修正 | 20 | +10（含测试用例） |
| 翻译工作（每千字） | 50 | +20（专业领域） |
| PR 审核 | 10 | - |-
| Issue 分类 | 5 | - |-

### 贡献者等级

| 等级 | 积分要求 | 特权 |
|------|----------|------|
| ⭐ 新成员 | 0-99 | 基础贡献权限 |
| ⭐⭐ 贡献者 | 100-499 | 直接提交小修正 |
| ⭐⭐⭐ 活跃贡献者 | 500-1999 | 审核 PR 权限 |
| ⭐⭐⭐⭐ 核心贡献者 | 2000-4999 | 维护者提名资格 |
| ⭐⭐⭐⭐⭐ 项目维护者 | 5000+ | 合并权限 |

### 特别奖励

- **月度之星**：每月评选贡献最多的成员
- **领域专家**：特定数学分支的深度贡献者
- **质量先锋**：零错误贡献记录保持者
- **社区大使**：积极帮助其他贡献者

### 徽章系统

贡献者可获得数字徽章展示在个人资料中：

- 🏅 首次贡献
- 📚 文档大师（50+ 文档）
- 🔬 形式化专家（10+ Lean4 证明）
- 🌐 翻译专家（5+ 万字翻译）
- 🐛 捉虫能手（20+ 错误修正）
- 👁️ 审核专家（50+ PR 审核）

---

## 🤝 社区准则

### 行为准则

请阅读并遵守我们的 **[社区行为准则 (CODE_OF_CONDUCT.md)](./CODE_OF_CONDUCT.md)**。

核心原则：

1. **尊重**：尊重所有社区成员，无论经验水平
2. **包容**：欢迎多样性观点和背景
3. **建设性**：提供建设性的反馈和建议
4. **耐心**：理解学习和贡献需要时间
5. **协作**：乐于帮助他人，共同进步

### 沟通渠道

| 渠道 | 用途 | 链接 |
|------|------|------|
| GitHub Issues | Bug 报告、功能请求 | [Issues](../../issues) |
| GitHub Discussions | 一般讨论、问答 | [Discussions](../../discussions) |
| Pull Requests | 代码/内容审核 | [PRs](../../pulls) |
| 邮件列表 | 重要公告 | formalmath@example.com |

### 冲突解决

1. 在 PR 评论中友好讨论
2. 如无法达成一致，@mention 维护者
3. 维护者将基于项目最佳利益做出决定

---

## 📚 学习资源

### 新贡献者推荐

1. [项目使用指南](docs/00-项目使用指南.md)
2. [内容创作指南](docs/00-贡献者指南/内容创作指南.md)
3. [Lean4 入门教程](docs/09-形式化证明/Lean4/README.md)
4. [术语标准词典](docs/01-基础数学/术语标准化词典-国际标准版.md)

### 进阶资源

1. [质量控制手册](docs/00-贡献者指南/质量控制手册.md)
2. [自动化工具使用](tools/contributor-workflow/README.md)
3. [API 文档](docs/00-贡献者指南/api文档.md)

---

## ❓ 常见问题

**Q: 我没有数学背景，可以贡献吗？**

A: 当然可以！您可以贡献：
- 文档格式修正
- 拼写错误修正
- 翻译工作（如果您擅长其他语言）
- 可视化设计
- 工具开发

**Q: 如何找到适合我的任务？**

A: 查看带有以下标签的 Issue：
- `good first issue`：适合新手的简单任务
- `help wanted`：需要社区帮助的任务
- `documentation`：文档相关任务

**Q: 我的 PR 为什么还没有被审核？**

A: 维护者都是志愿者，请耐心等待。如果超过 7 天未响应，可以 @mention 维护者。

**Q: 我可以同时处理多个 Issue 吗？**

A: 建议新手先完成一个再开始下一个。对于有经验的贡献者，可以同时处理 2-3 个不相关的 Issue。

---

## 📞 联系我们

如有任何问题，请通过以下方式联系：

- 📧 邮件：formalmath@example.com
- 💬 GitHub Discussions：[参与讨论](../../discussions)
- 🐛 Issue 报告：[提交 Issue](../../issues/new/choose)

---

## 🔍 审核流程详解

### 提交前准备

#### 1. 自检查清单

在提交 PR 之前，请确保：

**内容贡献**:
- [ ] 文档包含正确的 YAML Frontmatter
- [ ] MSC 分类准确（参考 [MSC2020](https://mathscinet.ams.org/mathscinet/msc/msc2020.html)）
- [ ] 知识层次标注正确（L0-L4）
- [ ] 数学公式使用 LaTeX 格式（`$...$` 或 `$$...$$`）
- [ ] 术语使用符合 [多语言术语对照表](./docs/多语言术语对照表.md)
- [ ] 引用来源正确标注
- [ ] 无拼写/语法错误
- [ ] 链接可正常访问

**代码贡献**:
- [ ] 代码通过编译/运行
- [ ] 包含适当的注释
- [ ] 包含单元测试（如适用）
- [ ] 遵循项目代码规范
- [ ] 无警告/错误信息
- [ ] 通过 CI 检查

#### 2. 本地检查

```bash
# 运行所有检查
python tools/contributor-workflow/pre_commit_check.py --all

# 仅检查 Markdown 格式
python tools/contributor-workflow/pre_commit_check.py --markdown

# 仅检查 MSC 编码
python tools/contributor-workflow/pre_commit_check.py --msc

# 仅检查 Lean4 代码
python tools/contributor-workflow/pre_commit_check.py --lean
```

### PR 审核流程

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  提交 PR    │ -> │  自动化检查  │ -> │  初步审核   │
└─────────────┘    └─────────────┘    └──────┬──────┘
       │                                     │
       │ 失败                                │ 通过
       ▼                                     ▼
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  修正问题   │ <- │  请求修改   │ <- │  详细审核   │
└─────────────┘    └─────────────┘    └──────┬──────┘
                                             │
                                    ┌────────┴────────┐
                                    │                 │
                              需要修改              通过
                                    │                 │
                                    ▼                 ▼
                            ┌─────────────┐    ┌─────────────┐
                            │  请求修改   │    │  维护者批准  │
                            └─────────────┘    └──────┬──────┘
                                                      │
                                                      ▼
                                               ┌─────────────┐
                                               │   合并到    │
                                               │   main     │
                                               └─────────────┘
```

### 审核标准

#### 内容审核检查项

| 检查项 | 重要性 | 审核者 |
|:-------|:------:|:-------|
| 数学准确性 | ⭐⭐⭐ | 领域专家 |
| 术语规范性 | ⭐⭐⭐ | 维护者 |
| 格式规范 | ⭐⭐ | 自动化/维护者 |
| 引用完整性 | ⭐⭐ | 维护者 |
| 语言表达 | ⭐⭐ | 社区成员 |

#### 代码审核检查项

| 检查项 | 重要性 | 审核者 |
|:-------|:------:|:-------|
| 功能正确性 | ⭐⭐⭐ | 维护者 |
| 代码规范 | ⭐⭐⭐ | 自动化/维护者 |
| 测试覆盖 | ⭐⭐ | 维护者 |
| 文档完整性 | ⭐⭐ | 维护者 |
| 性能影响 | ⭐ | 维护者 |

### 审核响应时间

| PR 类型 | 首次响应 | 完整审核 |
|:--------|:---------|:---------|
| 简单修复 | 1-2 天 | 2-3 天 |
| 文档更新 | 2-3 天 | 3-5 天 |
| 新功能 | 3-5 天 | 5-10 天 |
| 重大变更 | 5-7 天 | 10-14 天 |

> **注意**: 审核者都是志愿者，请耐心等待。如果超过上述时间未响应，可以 @mention 维护者或联系社区。

### 处理反馈

当审核者提出修改意见时：

1. **保持开放心态**: 审核是为了提高质量
2. **及时响应**: 尽量在 7 天内响应
3. **逐条处理**: 对每条建议进行回复或修改
4. **说明原因**: 如果不采纳建议，说明理由
5. **保持尊重**: 保持专业和友好的态度

```
# 回复示例
@reviewer 感谢审核！

- [x] 已修正第 3 行的错别字
- [x] 已补充缺失的引用
- [ ] 关于公式格式，我认为...（说明理由）
```

---

## 📝 提交规范详解

### Git 分支命名规范

```
# 功能分支
feature/<描述>
示例: feature/add-group-theory-advanced

# 修复分支
fix/<描述>
示例: fix/typo-in-algebra-basics

# 文档分支
docs/<描述>
示例: docs/update-contributing-guide

# 重构分支
refactor/<描述>
示例: refactor/simplify-validation-script
```

### 提交信息规范

#### 格式

```
<类型>(<范围>): <简短描述>

<详细描述>

<页脚>
```

#### 各部分组成

**1. 标题行（必填）**
- 格式: `类型(范围): 描述`
- 长度: 不超过 50 个字符
- 使用祈使语气（"添加" 而非 "添加了"）

**2. 正文（可选）**
- 空一行后开始
- 每行不超过 72 个字符
- 说明变更的动机和对比

**3. 页脚（可选）**
- 引用相关 Issue: `Fixes #123`
- 破坏性变更说明: `BREAKING CHANGE: ...`

#### 完整示例

```
feat(algebra): 添加群论第三同构定理

添加群论第三同构定理的完整证明，包括：
- 定理陈述
- 详细证明
- 应用示例
- 关联的 Lean4 形式化证明

参考教材: Dummit & Foote, Abstract Algebra, Chap. 3

Fixes #456
Closes #789
```

#### 类型说明

| 类型 | 含义 | 示例 |
|:-----|:-----|:-----|
| `feat` | 新功能 | `feat(lean): 添加新定理证明` |
| `fix` | 错误修复 | `fix(docs): 修正数学公式` |
| `docs` | 文档更新 | `docs(readme): 更新使用说明` |
| `style` | 格式调整 | `style(markdown): 统一标题格式` |
| `refactor` | 重构 | `refactor(tools): 优化检查脚本` |
| `test` | 测试相关 | `test(lean): 添加单元测试` |
| `chore` | 构建/工具 | `chore(ci): 更新工作流` |
| `perf` | 性能优化 | `perf(search): 优化索引速度` |

#### 范围说明

| 范围 | 说明 |
|:-----|:-----|
| `docs` | 文档内容 |
| `lean` | Lean4 形式化代码 |
| `tools` | 工具脚本 |
| `ci` | CI/CD 配置 |
| `deps` | 依赖更新 |
| `config` | 配置文件 |
| `<分支名>` | 具体数学分支 |

---

## 🔒 安全规范

### 敏感信息

**不要提交以下内容**:
- API 密钥、密码、令牌
- 个人身份信息（PII）
- 内部系统信息
- 未公开的漏洞信息

### 漏洞报告

如果发现安全漏洞，请：
1. **不要** 在公开 Issue 中报告
2. 发送邮件至: security@formalmath.org
3. 使用 [安全建议模板](.github/SECURITY.md)

---

## 📚 资源链接

### 项目文档

| 文档 | 说明 |
|:-----|:-----|
| [新手入门指南](./docs/新手入门指南.md) | 新贡献者必读 |
| [社区治理模式](./docs/社区治理模式.md) | 项目治理说明 |
| [行为准则](./CODE_OF_CONDUCT.md) | 社区行为规范 |
| [多语言术语对照表](./docs/多语言术语对照表.md) | 术语标准化参考 |

### 外部资源

| 资源 | 链接 |
|:-----|:-----|
| MSC2020 分类 | https://mathscinet.ams.org/mathscinet/msc/msc2020.html |
| Lean4 文档 | https://lean-lang.org/theorem_proving_in_lean4/ |
| Markdown 指南 | https://www.markdownguide.org/ |
| GitHub 文档 | https://docs.github.com/ |

---

## ❓ 常见问题

**Q: 我没有数学背景，可以贡献吗？**

A: 当然可以！您可以贡献：
- 文档格式修正
- 拼写错误修正
- 翻译工作
- 可视化设计
- 工具开发

**Q: 如何找到适合我的任务？**

A: 查看带有以下标签的 Issue：
- `good first issue`：适合新手的简单任务
- `help wanted`：需要社区帮助的任务
- `documentation`：文档相关任务

**Q: 我的 PR 为什么还没有被审核？**

A: 维护者都是志愿者，请耐心等待。如果超过 7 天未响应，可以 @mention 维护者。

**Q: 我可以同时处理多个 Issue 吗？**

A: 建议新手先完成一个再开始下一个。对于有经验的贡献者，可以同时处理 2-3 个不相关的 Issue。

**Q: 如何成为维护者？**

A: 持续高质量贡献，参与社区活动，现有维护者会定期评估并邀请活跃的贡献者加入。

---

## 📞 联系我们

如有任何问题，请通过以下方式联系：

- 📧 邮件：formalmath@example.com
- 💬 GitHub Discussions：[参与讨论](../../discussions)
- 🐛 Issue 报告：[提交 Issue](../../issues/new/choose)

---

**感谢您对 FormalMath 项目的贡献！** 🙏

*最后更新: 2026年4月*
