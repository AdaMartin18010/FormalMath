---
title: FormalMath 项目 CI/CD 指南
msc_primary: 00

  - 00A99
processed_at: '2026-04-05'
---
# FormalMath 项目 CI/CD 指南

本文档详细介绍FormalMath项目的持续集成/持续部署(CI/CD)流程，帮助贡献者理解和使用自动化工作流。

---

## 目录

1. [概述](#概述)
2. [CI工作流](#ci工作流)
3. [发布工作流](#发布工作流)
4. [本地CI检查](#本地ci检查)
5. [故障排除](#故障排除)
6. [最佳实践](#最佳实践)

---

## 概述

FormalMath项目使用GitHub Actions实现CI/CD自动化，主要包括：

| 工作流 | 文件 | 用途 |
|--------|------|------|
| CI检查 | `formalmath-ci.yml` | 代码质量检查、测试验证 |
| 发布 | `formalmath-release.yml` | 版本发布、构建打包 |

### 触发条件

- **CI工作流**: Push到main分支、Pull Request、手动触发
- **发布工作流**: 推送版本标签(如`v1.0.0`)、手动触发

---

## CI工作流

### 作业概览

`.github/workflows/formalmath-ci.yml` 包含5个并行作业：

```
┌─────────────────────────────────────────────────────────────┐
│                      CI工作流                                │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│ 1. Markdown │ 2. Python   │ 3. Lean4    │ 4. 链接检查       │
│    格式检查 │    脚本测试 │    编译     │                   │
└─────────────┴─────────────┴─────────────┴───────────────────┘
                              │
                              ▼
                    ┌───────────────────┐
                    │ 5. 质量报告生成   │
                    └───────────────────┘
                              │
                              ▼
                    ┌───────────────────┐
                    │ 6. CI汇总         │
                    └───────────────────┘
```

### 作业1: Markdown格式检查

**目的**: 确保所有Markdown文档符合格式规范

**工具**: [markdownlint-cli](https://github.com/igorshubovych/markdownlint-cli)

**配置**: `.markdownlint.json`

**检查内容**:
- 标题格式 (ATX风格)
- 列表缩进 (2空格)
- 行尾空格
- 代码块格式
- 链接格式

**本地运行**:
```bash
# 安装工具
npm install -g markdownlint-cli

# 运行检查
markdownlint '**/*.md' --ignore 'node_modules/**' --config .markdownlint.json

# 自动修复
markdownlint '**/*.md' --fix --ignore 'node_modules/**' --config .markdownlint.json
```

### 作业2: Python脚本测试

**目的**: 验证Python脚本质量和功能

**检查内容**:
- 语法检查 (`compileall`)
- 代码风格 (flake8)
- 代码格式 (Black)
- 单元测试 (pytest)
- 关键脚本可运行性

**测试矩阵**:
| Python版本 | 状态 |
|------------|------|
| 3.10 | ✅ 测试通过 |
| 3.11 | ✅ 测试通过 |
| 3.12 | ✅ 测试通过 |

**本地运行**:
```bash
# 语法检查
python -m compileall tools/ -q

# 代码风格
flake8 tools/ --count --select=E9,F63,F7,F82 --show-source --statistics

# 代码格式化
black tools/

# 单元测试
pytest tests/ -v --cov=tools
```

### 作业3: Lean4代码编译

**目的**: 确保形式化证明代码可编译

**工具**: Elan (Lean工具链管理器) + Lean 4

**检查内容**:
- 所有`.lean`文件编译
- 语法正确性
- 依赖完整性

**本地运行**:
```bash
# 安装Lean (首次)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh[需更新[需更新]] -sSf | sh

# 编译Lean文件
lean PiL2.lean
```

### 作业4: 链接有效性检查

**目的**: 检测文档中的无效链接

**检查范围**:
- **内部链接**: 相对路径链接 (`./path/to/file.md`)
- **外部链接**: HTTP/HTTPS链接 (抽样检查)

**本地运行**:
```bash
# 使用项目脚本
python tools/link_checker.py --internal-only

# 或使用本地CI脚本
./scripts/ci-check.sh --links
```

### 作业5: 生成质量报告

**目的**: 生成项目质量统计报告

**报告内容**:
| 指标 | 说明 |
|------|------|
| 文件统计 | Markdown/Python/Lean/JSON/YAML文件数量 |
| 代码行数 | 各类型文件的总行数 |
| Frontmatter覆盖率 | 文档元数据覆盖情况 |
| CI执行状态 | 本次CI各作业执行结果 |

**报告位置**: CI构建产物 → `quality-report`

---

## 发布工作流

### 触发方式

1. **自动触发**: 推送版本标签
   ```bash
   git tag -a v1.0.0 -m "版本1.0.0发布"
   git push origin v1.0.0
   ```

2. **手动触发**: GitHub Actions界面 → `Run workflow`

### 发布流程

```
┌──────────────────────────────────────────────────────────────┐
│                     发布工作流                                │
├──────────────────────────────────────────────────────────────┤
│ 1. 验证与准备                                                 │
│    └─ 版本号格式验证                                          │
│    └─ 标签冲突检查                                            │
├──────────────────────────────────────────────────────────────┤
│ 2. 运行完整测试                                               │
│    └─ 关键文件存在性检查                                      │
│    └─ Python语法检查                                          │
├──────────────────────────────────────────────────────────────┤
│ 3. 构建发布包                                                 │
│    ├─ 完整版 (.zip) - 包含所有内容                           │
│    ├─ 轻量版 (-lite.zip) - 仅核心文档                        │
│    ├─ 源码包 (.tar.gz)                                       │
│    └─ 生成校验和 (SHA256)                                    │
├──────────────────────────────────────────────────────────────┤
│ 4. 更新CHANGELOG                                              │
│    └─ 自动生成版本变更记录                                    │
├──────────────────────────────────────────────────────────────┤
│ 5. 创建GitHub Release                                         │
│    └─ 上传构建产物                                            │
├──────────────────────────────────────────────────────────────┤
│ 6. 发布通知                                                   │
└──────────────────────────────────────────────────────────────┘
```

### 版本号规范

使用[语义化版本](https://semver.org/lang/zh-CN/)[需更新][需更新](SemVer):

```
版本格式: 主版本号.次版本号.修订号[-预发布标识]
示例:     1.2.3, 2.0.0-alpha, 1.0.0-rc.1
```

| 类型 | 说明 |
|------|------|
| 主版本号 | 不兼容的API修改 |
| 次版本号 | 向下兼容的功能新增 |
| 修订号 | 向下兼容的问题修复 |
| 预发布标识 | alpha, beta, rc等 |

### 发布包说明

| 包名 | 内容 | 大小 | 用途 |
|------|------|------|------|
| `formalmath-vX.Y.Z.zip` | 完整项目 | ~50MB | 完整部署 |
| `formalmath-vX.Y.Z-lite.zip` | 仅核心文档 | ~20MB | 快速查阅 |
| `formalmath-vX.Y.Z.tar.gz` | 源码压缩 | ~50MB | 源码分发 |

---

## 本地CI检查

### 脚本位置

- **Linux/Mac**: `scripts/ci-check.sh`
- **Windows**: `scripts/ci-check.ps1`

### 快速开始

#### Linux/Mac

```bash
# 赋予执行权限
chmod +x scripts/ci-check.sh

# 运行默认检查 (Markdown + Python)
./scripts/ci-check.sh

# 运行所有检查
./scripts/ci-check.sh --all

# 自动修复格式问题
./scripts/ci-check.sh --fix

# 仅检查特定项目
./scripts/ci-check.sh --markdown --python
```

#### Windows

```powershell
# 运行默认检查
.\scripts\ci-check.ps1

# 运行所有检查
.\scripts\ci-check.ps1 -All

# 自动修复
.\scripts\ci-check.ps1 -Fix

# 快速模式
.\scripts\ci-check.ps1 -Quick
```

### 脚本选项

| 选项 | Linux/Mac | Windows | 说明 |
|------|-----------|---------|------|
| 帮助 | `-h, --help` | `-Help` | 显示帮助信息 |
| Markdown | `-m, --markdown` | `-Markdown` | 仅检查Markdown |
| Python | `-p, --python` | `-Python` | 仅检查Python |
| 链接 | `-l, --links` | `-Links` | 检查链接 |
| Lean | `-L, --lean` | `-Lean` | 检查Lean4 |
| 全部 | `-a, --all` | `-All` | 运行所有检查 |
| 修复 | `-f, --fix` | `-Fix` | 自动修复问题 |
| 详细 | `-v, --verbose` | `-Verbose` | 详细输出 |
| 快速 | `-q, --quick` | `-Quick` | 快速模式 |

### 推荐工作流

```bash
# 1. 开发完成后，运行本地检查
./scripts/ci-check.sh

# 2. 如果有格式问题，自动修复
./scripts/ci-check.sh --fix

# 3. 再次检查确认
./scripts/ci-check.sh

# 4. 提交代码
git add .
git commit -m "feat: 新增功能描述"
git push
```

---

## 故障排除

### 常见问题

#### Q1: markdownlint 未安装

**错误信息**:
```
⚠️  markdownlint 未安装，使用基础检查...
```

**解决方案**:
```bash
# 安装 markdownlint-cli
npm install -g markdownlint-cli

# 验证安装
markdownlint --version
```

#### Q2: Python语法检查失败

**错误信息**:
```
❌ 发现Python语法错误
```

**排查步骤**:
1. 查看具体错误文件
2. 使用 `python -m py_compile <file>` 检查单个文件
3. 修复语法错误后重新运行

#### Q3: 链接检查大量失败

**可能原因**:
- 文件被移动或重命名
- 相对路径错误
- 网络连接问题(外部链接)

**解决方案**:
```bash
# 使用本地脚本详细检查
python tools/link_checker.py --internal-only --verbose

# 或使用修复工具
python tools/link_fixer.py
```

#### Q4: CI在Lean编译时超时

**解决方案**:
- 确保 `.lake` 目录已缓存
- 本地预编译Lean文件
- 检查是否有循环导入

### CI失败处理流程

```
CI失败
   │
   ├─── 查看Actions日志 ───┐
   │                       │
   ├─── 定位失败作业       │
   │                       │
   ├─── 下载检查报告       │
   │   (quality-report)    │
   │                       │
   └─── 本地复现问题       │
       ./scripts/ci-check.sh   │
                               │
   ┌───────────────────────────┘
   │
   ▼
修复问题 → 本地验证 → 重新提交
```

### 获取帮助

- 📚 [GitHub Actions文档](https://docs.github.com/cn/actions)
- 🐛 [提交Issue](https://github.com/FormalMath/issues/new)
- 💬 [Discussions讨论区](https://github.com/FormalMath/discussions)

---

## 最佳实践

### 提交前检查清单

- [ ] 本地CI检查通过 (`./scripts/ci-check.sh`)
- [ ] 相关测试已更新并通过
- [ ] 文档已更新 (如需要)
- [ ] 提交信息符合规范

### 提交信息规范

使用[Conventional Commits](https://www.conventionalcommits.org/zh-hans/v1.0.0/)[需更新][需更新]:

```
<type>(<scope>): <subject>

[可选的正文]

[可选的脚注]
```

**类型说明**:

| 类型 | 用途 |
|------|------|
| `feat` | 新功能 |
| `fix` | 修复问题 |
| `docs` | 文档更新 |
| `style` | 代码格式调整 |
| `refactor` | 重构 |
| `test` | 测试相关 |
| `chore` | 构建/工具更新 |

**示例**:
```
feat(lean): 新增Brouwer不动点定理证明

docs: 更新README中的安装说明

fix(tools): 修复link_checker的路径解析问题
```

### 性能优化建议

1. **使用缓存**
   - CI中启用了pip和npm缓存
   - 确保依赖文件不频繁变更

2. **增量检查**
   - 仅修改的文件需要严格检查
   - 使用 `paths-ignore` 跳过多余检查

3. **并行作业**
   - 各检查作业并行运行
   - 充分利用GitHub Actions并发

### 安全建议

1. **Secrets管理**
   - 不要在代码中硬编码密钥
   - 使用GitHub Secrets存储敏感信息

2. **依赖安全**
   - 定期更新依赖
   - 使用Dependabot监控漏洞

3. **权限最小化**
   - 工作流使用最小必要权限
   - 审查第三方Action

---

## 附录

### CI/CD配置文件索引

| 文件 | 用途 |
|------|------|
| `.github/workflows/formalmath-ci.yml` | 持续集成工作流 |
| `.github/workflows/formalmath-release.yml` | 发布工作流 |
| `scripts/ci-check.sh` | Linux/Mac本地检查脚本 |
| `scripts/ci-check.ps1` | Windows本地检查脚本 |
| `.markdownlint.json` | Markdown检查规则 |
| `docs/CI_CD指南.md` | 本文档 |

### 相关资源

- [GitHub Actions入门](https://docs.github.com/cn/actions/quickstart)
- [语义化版本规范](https://semver.org/lang/zh-CN/)[需更新][需更新]
- [Conventional Commits](https://www.conventionalcommits.org/zh-hans/v1.0.0/)[需更新][需更新]
- [markdownlint规则](https://github.com/DavidAnson/markdownlint/blob/main/doc/Rules.md)

---

**最后更新**: 2026年4月  
**维护者**: FormalMath CI/CD团队
