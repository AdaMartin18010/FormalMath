---
title: FormalMath CI/CD 指南
msc_primary: 00A99
processed_at: '2026-04-05'
---
# FormalMath CI/CD 指南

本文档详细介绍了 FormalMath 项目的持续集成和持续部署（CI/CD）流程。

## 📋 目录

- [概述](#概述)
- [工作流说明](#工作流说明)
- [环境配置](#环境配置)
- [触发条件](#触发条件)
- [部署流程](#部署流程)
- [故障排除](#故障排除)

## 概述

FormalMath 项目使用 GitHub Actions 实现完整的 CI/CD 自动化流程，包括：

- **持续集成（CI）**: 自动构建、测试、代码质量检查
- **持续部署（CD）**: 自动部署到测试和生产环境
- **安全扫描**: 漏洞检测、密钥扫描、许可证合规
- **发布管理**: 自动化版本发布和文档部署

## 工作流说明

### 1. Build (build.yml)

构建工作流负责编译和打包项目组件。

| 任务 | 说明 | 触发条件 |
|------|------|----------|
| `changes` | 检测代码变更 | 每次触发 |
| `build-frontend` | 构建前端应用 | 前端代码变更 |
| `build-tools` | 构建 Python 工具 | 工具代码变更 |
| `build-lean4` | 构建 Lean4 项目 | Lean 代码变更 |
| `build-docker` | 构建 Docker 镜像 | main 分支或 tag |
| `build-docs` | 构建文档 | 文档变更 |

**环境变量：**

- `NODE_VERSION`: 18
- `PYTHON_VERSION`: 3.11
- `LEAN_VERSION`: v4.6.0

### 2. Test (test.yml)

测试工作流执行全面的测试套件。

| 测试类型 | 说明 | 工具 |
|----------|------|------|
| Python 单元测试 | 测试 Python 工具 | pytest |
| Python 集成测试 | 测试组件集成 | pytest |
| 前端单元测试 | 测试 React 组件 | Jest |
| E2E 测试 | 端到端测试 | Cypress |
| Lean4 测试 | 形式化证明测试 | lake |
| 内容质量测试 | 文档质量检查 | 自定义脚本 |
| 性能测试 | 性能基准测试 | 自定义脚本 |

**手动触发参数：**

```bash
# 运行所有测试
workflow_dispatch: test_type=all

# 仅运行单元测试
workflow_dispatch: test_type=unit

# 仅运行集成测试
workflow_dispatch: test_type=integration

# 仅运行 E2E 测试
workflow_dispatch: test_type=e2e
```

### 3. Deploy (deploy.yml)

部署工作流管理应用的发布和部署。

| 环境 | URL | 部署条件 |
|------|-----|----------|
| Staging | https://staging.formalmath.io | main 分支或手动触发 |
| Production | https://formalmath.io | tag 推送或手动指定 |

**部署流程：**

1. 准备部署（版本、环境确定）
2. 预部署测试
3. 构建生产镜像
4. 部署到目标环境
5. 运行冒烟测试
6. 健康检查
7. 创建 GitHub Release（仅生产环境）

**手动部署：**

```bash
# 部署到测试环境
workflow_dispatch: environment=staging

# 部署指定版本到生产环境
workflow_dispatch: environment=production, version=1.0.0

# 回滚到之前版本
workflow_dispatch: environment=production, version=1.0.0-previous
```

### 4. Release (release.yml)

发布工作流处理版本发布流程。

| 任务 | 说明 |
|------|------|
| `validate` | 验证版本格式 |
| `build-artifacts` | 构建发布产物 |
| `generate-notes` | 生成发布说明 |
| `create-release` | 创建 GitHub Release |
| `publish-packages` | 发布到包管理器 |
| `update-documentation` | 更新文档 |

**发布产物：**

- `formalmath-docs-*.tar.gz` - 文档包
- `formalmath-tools-*.tar.gz` - 工具包
- Docker 镜像: `ghcr.io/formalmath/formalmath:*`

### 5. Security (security.yml)

安全工作流执行全面的安全扫描。

| 扫描类型 | 工具 | 频率 |
|----------|------|------|
| 依赖漏洞扫描 | npm audit, Safety | 每次提交 + 每周 |
| 代码安全扫描 | CodeQL | 每次提交 |
| Python 安全扫描 | Bandit, Semgrep | 每次提交 |
| 密钥扫描 | GitLeaks, TruffleHog | 每次提交 |
| 容器安全扫描 | Trivy | main 分支 |
| 许可证合规 | license-checker | 每次提交 |

### 6. Quality Assurance (quality-assurance.yml)

质量保障工作流执行定期质量检查。

| 任务 | 说明 | 频率 |
|------|------|------|
| MSC 验证 | 验证 MSC 编码 | 每周 |
| 链接检查 | 检查文档链接 | 每周 |
| 生成质量报告 | 生成详细报告 | 每周 |
| 过时内容检查 | 检查长期未更新内容 | 每周 |
| 性能指标 | 统计项目数据 | 每周 |

## 环境配置

### 必需的 Secrets

| Secret | 用途 | 必需 |
|--------|------|------|
| `GITHUB_TOKEN` | GitHub API 访问 | 是（自动提供） |
| `NPM_TOKEN` | 发布到 npm | 否 |
| `PYPI_API_TOKEN` | 发布到 PyPI | 否 |
| `CODECOV_TOKEN` | 代码覆盖率上传 | 否 |
| `GITLEAKS_LICENSE` | GitLeaks 密钥扫描 | 否 |

### 环境保护规则

- **staging**: 无保护，可直接部署
- **production**: 需要人工审批，只能从 tag 部署

### 并发控制

- Build/Test: 同一分支的重复运行会取消之前的运行
- Deploy: 部署不会并发执行，确保顺序部署

## 触发条件

### 自动触发

```yaml
# 推送到 main/develop 分支
push:
  branches: [main, develop]

# 创建 Pull Request
pull_request:
  branches: [main, develop]

# 推送 tag
push:
  tags: ['v*']

# 定时触发（每周日）
schedule:
  - cron: '0 0 * * 0'
```

### 手动触发

所有工作流都支持 `workflow_dispatch` 手动触发，可通过以下方式：

1. GitHub Web 界面: Actions → 选择工作流 → Run workflow
2. GitHub CLI:

   ```bash
   gh workflow run test.yml -f test_type=e2e
   ```

3. REST API:

   ```bash
   curl -X POST \
     -H "Authorization: token $GITHUB_TOKEN" \
     -d '{"ref":"main","inputs":{"test_type":"e2e"}}' \
     https://api.github.com/repos/formalmath/formalmath/actions/workflows/test.yml/dispatches
   ```

## 部署流程

### 标准发布流程

1. **开发阶段**

   ```bash
   git checkout -b feature/new-feature
   # 开发代码
   git commit -m "feat: add new feature"
   git push origin feature/new-feature
   ```

2. **创建 PR**
   - CI 自动运行测试
   - Code Review
   - 合并到 develop

3. **发布准备**

   ```bash
   git checkout main
   git merge develop
   git tag -a v1.0.0 -m "Release v1.0.0"
   git push origin main --tags
   ```

4. **自动部署**
   - Build 工作流触发
   - Test 工作流运行
   - Deploy 工作流部署到生产环境

### 热修复流程

1. **从 main 创建修复分支**

   ```bash
   git checkout -b hotfix/critical-fix main
   ```

2. **修复并提交**

   ```bash
   git commit -m "fix: critical bug fix"
   git push origin hotfix/critical-fix
   ```

3. **合并并发布**

   ```bash
   git checkout main
   git merge hotfix/critical-fix
   git tag -a v1.0.1 -m "Hotfix v1.0.1"
   git push origin main --tags
   ```

### 回滚流程

1. **手动触发回滚**

   ```bash
   gh workflow run deploy.yml -f environment=production -f version=1.0.0
   ```

2. **紧急回滚**

   ```bash
   # 通过 kubectl 直接回滚
   kubectl rollout undo deployment/formalmath -n production
   ```

## 故障排除

### 常见问题

#### 1. 构建失败

**症状**: Build 工作流失败

**解决**:

```bash
# 本地验证构建
npm ci
npm run build

# 检查依赖
npm audit
```

#### 2. 测试失败

**症状**: Test 工作流失败

**解决**:

```bash
# 本地运行测试
npm run test:unit
pytest backend/unit

# 检查测试覆盖
pytest --cov
```

#### 3. 部署失败

**症状**: Deploy 工作流失败

**解决**:

1. 检查环境配置
2. 查看部署日志
3. 验证镜像标签
4. 检查目标环境状态

#### 4. 安全扫描失败

**症状**: Security 工作流失败

**解决**:

```bash
# 运行本地安全扫描
npm audit
bandit -r tools/
gitleaks detect
```

### 调试技巧

1. **启用调试日志**

   ```yaml
   env:
     ACTIONS_STEP_DEBUG: true
     ACTIONS_RUNNER_DEBUG: true
   ```

2. **使用 tmate 调试**

   ```yaml
   - name: Setup tmate session
     uses: mxschmitt/action-tmate@v3
     if: failure()
   ```

3. **下载 artifacts**

   ```bash
   gh run download <run-id>
   ```

### 联系支持

- GitHub Issues: https://github.com/formalmath/formalmath/issues
- 邮件: maintainers@formalmath.io

## 最佳实践

1. **分支策略**
   - main: 生产代码
   - develop: 开发集成
   - feature/*: 功能分支
   - hotfix/*: 紧急修复

2. **提交规范**
   - `feat:` 新功能
   - `fix:` 修复
   - `docs:` 文档
   - `test:` 测试
   - `refactor:` 重构

3. **版本号规范**
   - 遵循语义化版本: MAJOR.MINOR.PATCH
   - 预发布版本: v1.0.0-alpha.1
   - 标记: git tag -a v1.0.0 -m "Release v1.0.0"

4. **安全检查**
   - 定期更新依赖
   - 审查安全扫描报告
   - 及时修复漏洞

---

**最后更新**: 2026年4月
**维护者**: FormalMath 团队
