---
msc_primary: 68N99
---

# FormalMath 贡献者工作流工具

本目录包含用于支持贡献者工作流的自动化工具。

## 工具列表

### 1. 预提交检查 (pre_commit_check.py)

在提交前检查文档质量。

**用法：**
```bash
# 检查所有暂存文件
python pre_commit_check.py

# 检查特定文件
python pre_commit_check.py docs/example.md

# 运行所有检查
python pre_commit_check.py --all

# 仅检查 Markdown
python pre_commit_check.py --markdown-only

# 仅检查 Lean
python pre_commit_check.py --lean-only
```

**检查内容：**
- YAML Frontmatter 格式
- MSC 编码有效性
- Markdown 格式规范
- 数学公式语法
- 内部链接有效性

### 2. CI 内容检查 (ci_content_check.py)

用于 CI/CD 流水线的内容质量检查。

**用法：**
```bash
# 检查指定路径
python ci_content_check.py --paths docs/ 数学家理念体系/

# GitHub Actions 格式输出
python ci_content_check.py --paths docs/ --format github

# 发现错误时失败
python ci_content_check.py --paths docs/ --fail-on-error
```

### 3. MSC 编码验证 (validate_msc.py)

验证文档的 MSC2020 分类编码。

**用法：**
```bash
# 验证所有文档
python validate_msc.py --check-all --path .

# GitHub Actions 格式
python validate_msc.py --check-all --report-format github
```

**MSC2020 分类：**
- 主分类格式：`XX-XX`（如 `20-XX`）
- 次分类一级：`XXAxx`（如 `20Gxx`）
- 次分类二级：`XXA00`（如 `20G05`）

### 4. 链接检查 (check_links.py)

检查 Markdown 文档中的链接有效性。

**用法：**
```bash
# 检查内部链接
python check_links.py --paths docs/ 数学家理念体系/ --check-internal

# 检查所有链接
python check_links.py --paths docs/ --check-internal --check-external

# 发现失效链接时失败
python check_links.py --paths docs/ --check-internal --fail-on-broken
```

### 5. 积分计算 (calculate_rewards.py)

根据 PR 内容计算贡献积分。

**用法：**
```bash
python calculate_rewards.py \
    --pr-number 123 \
    --pr-author "username" \
    --pr-title "docs: add new theorem" \
    --output reward.json
```

**积分规则：**
| 贡献类型 | 基础积分 | 说明 |
|----------|----------|------|
| 新文档（基础版） | 50 | |
| 新文档（增强版） | 100 | |
| 新文档（深度版） | 200 | |
| 错误修正（小） | 20 | < 50 行变更 |
| 错误修正（大） | 50 | ≥ 50 行变更 |
| Lean4 定理 | 300 | |
| Lean4 证明 | 150 | |
| 翻译（每千字） | 50-60 | |

### 6. 排行榜更新 (update_leaderboard.py)

生成贡献者排行榜。

**用法：**
```bash
# 生成 CONTRIBUTORS.md
python update_leaderboard.py --output CONTRIBUTORS.md
```

## 集成到 Git Hooks

### 预提交钩子

创建 `.git/hooks/pre-commit`：

```bash
#!/bin/bash
# FormalMath 预提交钩子

echo "Running pre-commit checks..."

# 运行检查
python tools/contributor-workflow/pre_commit_check.py

# 检查退出码
if [ $? -ne 0 ]; then
    echo "Pre-commit checks failed. Please fix the issues before committing."
    exit 1
fi

echo "Pre-commit checks passed!"
```

赋予执行权限：
```bash
chmod +x .git/hooks/pre-commit
```

## CI/CD 集成

这些工具设计用于 GitHub Actions 工作流。详见 `.github/workflows/` 目录。

## 开发新工具

### 工具模板

```python
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
工具描述

用法:
    python tool_name.py [options]
"""

import argparse
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description='工具描述')
    parser.add_argument('--option', help='选项说明')
    
    args = parser.parse_args()
    
    # 实现工具逻辑
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
```

### 测试

```bash
# 运行单元测试
python -m pytest tests/

# 测试特定工具
python -m pytest tests/test_pre_commit_check.py
```

## 常见问题

**Q: 预提交检查太慢？**

A: 只检查暂存文件：
```bash
python pre_commit_check.py
```

**Q: 如何跳过检查？**

A: 紧急情况可使用 `--no-verify`：
```bash
git commit --no-verify -m "紧急修复"
```

但不推荐常规使用。

**Q: 发现误报？**

A: 请提交 Issue 报告，包含：
- 工具名称
- 误报内容
- 预期行为

---

**维护者**: FormalMath 项目组
