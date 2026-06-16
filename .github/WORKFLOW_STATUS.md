---
title: CI/CD 工作流状态
msc_primary: 00A99
processed_at: '2026-04-05'
references:
  textbooks:
  - title: The Princeton Companion to Mathematics
    author: Timothy Gowers (ed.)
    edition: 1st
    publisher: Princeton University Press
    year: 2008
    isbn: '9780691118802'
    mr_number: MR2467561
    doi: 10.1515/9781400830398
  - title: 'How to Prove It: A Structured Approach'
    author: Daniel J. Velleman
    edition: 2nd
    publisher: Cambridge University Press
    year: 2006
    isbn: '9780521675994'
    mr_number: MR2448845
    doi: 10.1017/CBO9780511811029
external_ids:
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=00A99
---
# CI/CD 工作流状态

## 工作流状态徽章

| 工作流 | 状态 | 说明 |
|--------|------|------|
| Build | ![Build](https://github.com/FormalMath) | 构建流程 |
| Test | ![Test](https://github.com/FormalMath) | 测试流程 |
| Deploy | ![Deploy](https://github.com/FormalMath) | 部署流程 |
| Release | ![Release](https://github.com/FormalMath) | 发布流程 |
| Security | ![Security](https://github.com/FormalMath) | 安全扫描 |
| Quality Assurance | ![Quality Assurance](https://github.com/FormalMath) | 质量保障 |

## 代码质量徽章

![Codecov](https://codecov.io/gh/formalmath/formalmath/branch/main/graph/badge.svg)
![CodeQL](https://github.com/FormalMath)

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

- [Actions Dashboard](https://github.com/FormalMath)
- [Deployment History](https://github.com/FormalMath)
- [Releases](https://github.com/FormalMath)
- [Security Advisories](https://github.com/FormalMath)

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

---

## 参考文献

- Timothy Gowers (ed.), *The Princeton Companion to Mathematics*, 1st ed., Princeton University Press, 2008, ISBN: 9780691118802 / MR2467561
- Daniel J. Velleman, *How to Prove It: A Structured Approach*, 2nd ed., Cambridge University Press, 2006, ISBN: 9780521675994 / MR2448845