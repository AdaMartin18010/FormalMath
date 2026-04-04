# CI/CD 工作流状态

## 工作流状态徽章

| 工作流 | 状态 | 说明 |
|--------|------|------|
| Build | ![Build](https://github.com/formalmath/formalmath/workflows/Build/badge.svg) | 构建流程 |
| Test | ![Test](https://github.com/formalmath/formalmath/workflows/Test/badge.svg) | 测试流程 |
| Deploy | ![Deploy](https://github.com/formalmath/formalmath/workflows/Deploy/badge.svg) | 部署流程 |
| Release | ![Release](https://github.com/formalmath/formalmath/workflows/Release/badge.svg) | 发布流程 |
| Security | ![Security](https://github.com/formalmath/formalmath/workflows/Security/badge.svg) | 安全扫描 |
| Quality Assurance | ![Quality Assurance](https://github.com/formalmath/formalmath/workflows/Quality%20Assurance/badge.svg) | 质量保障 |

## 代码质量徽章

![Codecov](https://codecov.io/gh/formalmath/formalmath/branch/main/graph/badge.svg)
![CodeQL](https://github.com/formalmath/formalmath/workflows/CodeQL/badge.svg)

## 环境状态

| 环境 | 状态 | 版本 | 最后部署 |
|------|------|------|----------|
| Staging | 🟢 Healthy | v1.0.0 | 2026-04-04 |
| Production | 🟢 Healthy | v1.0.0 | 2026-04-04 |

## 工作流触发频率

| 工作流 | 触发条件 | 平均运行时间 |
|--------|----------|-------------|
| Build | 每次 Push/PR | ~5 分钟 |
| Test | 每次 Push/PR | ~10 分钟 |
| Deploy | Tag 推送/手动 | ~8 分钟 |
| Release | Tag 推送 | ~3 分钟 |
| Security | 每次 Push/PR + 每周 | ~15 分钟 |
| Quality Assurance | 每周日 | ~20 分钟 |

## 快速链接

- [Actions Dashboard](https://github.com/formalmath/formalmath/actions)
- [Deployment History](https://github.com/formalmath/formalmath/deployments)
- [Releases](https://github.com/formalmath/formalmath/releases)
- [Security Advisories](https://github.com/formalmath/formalmath/security/advisories)

## 手动触发命令

```bash
# 运行测试
gh workflow run test.yml

# 部署到测试环境
gh workflow run deploy.yml -f environment=staging

# 部署到生产环境
gh workflow run deploy.yml -f environment=production

# 运行安全扫描
gh workflow run security.yml
```
