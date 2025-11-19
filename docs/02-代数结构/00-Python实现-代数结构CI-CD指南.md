# 代数结构Python实现CI/CD指南

## 概述

本文档提供代数结构Python实现项目的完整持续集成（CI）和持续部署（CD）指南，包括CI/CD概念、配置、最佳实践和故障排除。

## 目录

- [CI/CD概述](#cicd概述)
- [CI/CD架构](#cicd架构)
- [GitHub Actions配置](#github-actions配置)
- [CI工作流](#ci工作流)
- [CD工作流](#cd工作流)
- [测试自动化](#测试自动化)
- [代码质量检查](#代码质量检查)
- [部署自动化](#部署自动化)
- [监控和通知](#监控和通知)
- [最佳实践](#最佳实践)
- [常见问题](#常见问题)
- [故障排除](#故障排除)

## CI/CD概述

### 什么是CI/CD

- **CI (Continuous Integration)**: 持续集成，自动构建和测试代码变更
- **CD (Continuous Deployment/Delivery)**: 持续部署/交付，自动部署到生产环境

### CI/CD的价值

1. **自动化**: 减少手动操作，提高效率
2. **早期发现问题**: 在合并前发现Bug
3. **一致性**: 确保所有环境的一致性
4. **快速反馈**: 快速获得测试结果
5. **降低风险**: 自动化减少人为错误

### CI/CD流程

```
代码提交 → 自动构建 → 自动测试 → 代码质量检查 → 自动部署 → 监控
```

## CI/CD架构

### 整体架构

```
┌─────────────┐
│  开发者提交  │
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ GitHub Actions│
└──────┬──────┘
       │
       ├──► 构建
       ├──► 测试
       ├──► 代码质量检查
       └──► 部署
```

### 工作流类型

1. **CI工作流**: 每次推送和PR时运行
2. **CD工作流**: 合并到主分支或发布标签时运行
3. **计划工作流**: 按计划运行（如每日构建）

## GitHub Actions配置

### 基本配置

创建 `.github/workflows/ci.yml`:

```yaml
name: CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.8', '3.9', '3.10', '3.11']

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}
        cache: 'pip'

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-dev.txt

    - name: Run tests
      run: |
        pytest --cov=algebraic_structures --cov-report=xml --cov-report=html

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml
        flags: unittests
        name: codecov-umbrella
```

### 代码质量检查工作流

创建 `.github/workflows/quality.yml`:

```yaml
name: Code Quality

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

jobs:
  lint:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'
        cache: 'pip'

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install black flake8 mypy pylint

    - name: Check code style with Black
      run: black --check .

    - name: Lint with flake8
      run: |
        flake8 . --count --select=E9,F63,F7,F82 --show-source --statistics
        flake8 . --count --exit-zero --max-complexity=10 --max-line-length=127 --statistics

    - name: Type check with mypy
      run: |
        mypy algebraic_structures --ignore-missing-imports

    - name: Lint with pylint
      run: |
        pylint algebraic_structures --disable=C,R
```

### 安全扫描工作流

创建 `.github/workflows/security.yml`:

```yaml
name: Security Scan

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]
  schedule:
    - cron: '0 0 * * 0'  # 每周日运行

jobs:
  security:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install safety bandit

    - name: Check dependencies with Safety
      run: |
        safety check --json

    - name: Scan code with Bandit
      run: |
        bandit -r algebraic_structures -f json -o bandit-report.json

    - name: Upload security report
      uses: actions/upload-artifact@v3
      with:
        name: security-report
        path: bandit-report.json
```

## CI工作流

### 测试工作流

#### 单元测试

```yaml
- name: Run unit tests
  run: |
    pytest tests/unit/ -v --cov=algebraic_structures --cov-report=xml
```

#### 集成测试

```yaml
- name: Run integration tests
  run: |
    pytest tests/integration/ -v
```

#### 性能测试

```yaml
- name: Run performance tests
  run: |
    pytest tests/performance/ -v --benchmark-only
```

### 多平台测试

```yaml
jobs:
  test:
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        python-version: ['3.8', '3.9', '3.10', '3.11']

    runs-on: ${{ matrix.os }}

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-dev.txt

    - name: Run tests
      run: pytest
```

### 并行测试

```yaml
jobs:
  test:
    strategy:
      matrix:
        test-group: [group-theory, ring-theory, field-theory, other]

    steps:
    - name: Run test group
      run: |
        pytest tests/${{ matrix.test-group }}/ -v
```

## CD工作流

### 发布工作流

创建 `.github/workflows/release.yml`:

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build-and-publish:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'

    - name: Install build dependencies
      run: |
        python -m pip install --upgrade pip
        pip install build twine

    - name: Build package
      run: python -m build

    - name: Publish to PyPI
      env:
        TWINE_USERNAME: __token__
        TWINE_PASSWORD: ${{ secrets.PYPI_API_TOKEN }}
      run: twine upload dist/*

    - name: Create GitHub Release
      uses: actions/create-release@v1
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
      with:
        tag_name: ${{ github.ref }}
        release_name: Release ${{ github.ref }}
        body: |
          See CHANGELOG.md for details
        draft: false
        prerelease: false
```

### 自动部署到测试环境

```yaml
name: Deploy to Staging

on:
  push:
    branches: [ develop ]

jobs:
  deploy-staging:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Deploy to staging
      run: |
        # 部署脚本
        ./scripts/deploy.sh staging
      env:
        STAGING_URL: ${{ secrets.STAGING_URL }}
        DEPLOY_KEY: ${{ secrets.DEPLOY_KEY }}
```

### 自动部署到生产环境

```yaml
name: Deploy to Production

on:
  push:
    branches: [ main ]

jobs:
  deploy-production:
    runs-on: ubuntu-latest
    environment: production

    steps:
    - uses: actions/checkout@v3

    - name: Deploy to production
      run: |
        ./scripts/deploy.sh production
      env:
        PRODUCTION_URL: ${{ secrets.PRODUCTION_URL }}
        DEPLOY_KEY: ${{ secrets.DEPLOY_KEY }}
```

## 测试自动化

### 测试矩阵

```yaml
strategy:
  matrix:
    python-version: ['3.8', '3.9', '3.10', '3.11']
    os: [ubuntu-latest, windows-latest, macos-latest]
    include:
      - python-version: '3.10'
        os: ubuntu-latest
        coverage: true
```

### 测试缓存

```yaml
- name: Cache dependencies
  uses: actions/cache@v3
  with:
    path: ~/.cache/pip
    key: ${{ runner.os }}-pip-${{ hashFiles('**/requirements.txt') }}
    restore-keys: |
      ${{ runner.os }}-pip-
```

### 测试报告

```yaml
- name: Publish test results
  uses: EnricoMi/publish-unit-test-result-action@v2
  if: always()
  with:
    files: 'test-results.xml'
```

## 代码质量检查

### 代码覆盖率

```yaml
- name: Run tests with coverage
  run: |
    pytest --cov=algebraic_structures --cov-report=xml --cov-report=html

- name: Upload coverage to Codecov
  uses: codecov/codecov-action@v3
  with:
    file: ./coverage.xml
    flags: unittests
    name: codecov-umbrella
    fail_ci_if_error: true
```

### 代码复杂度检查

```yaml
- name: Check code complexity
  run: |
    radon cc algebraic_structures --min B
```

### 代码重复检查

```yaml
- name: Check code duplication
  run: |
    pydocstyle algebraic_structures
```

## 部署自动化

### Docker构建和推送

```yaml
- name: Build Docker image
  run: |
    docker build -t algebraic-structures:${{ github.sha }} .
    docker tag algebraic-structures:${{ github.sha }} algebraic-structures:latest

- name: Push to Docker Hub
  run: |
    echo "${{ secrets.DOCKER_PASSWORD }}" | docker login -u "${{ secrets.DOCKER_USERNAME }}" --password-stdin
    docker push algebraic-structures:${{ github.sha }}
    docker push algebraic-structures:latest
```

### 文档部署

```yaml
- name: Deploy documentation
  run: |
    pip install mkdocs mkdocs-material
    mkdocs gh-deploy --force
```

### 包发布

```yaml
- name: Publish to PyPI
  env:
    TWINE_USERNAME: __token__
    TWINE_PASSWORD: ${{ secrets.PYPI_API_TOKEN }}
  run: |
    python -m build
    twine upload dist/*
```

## 监控和通知

### 通知配置

```yaml
- name: Notify on failure
  if: failure()
  uses: 8398a7/action-slack@v3
  with:
    status: ${{ job.status }}
    text: 'CI failed!'
    webhook_url: ${{ secrets.SLACK_WEBHOOK }}
```

### 状态徽章

在README中添加状态徽章:

```markdown
![CI](https://github.com/username/algebraic-structures/workflows/CI/badge.svg)
![Codecov](https://codecov.io/gh/username/algebraic-structures/branch/main/graph/badge.svg)
![PyPI](https://img.shields.io/pypi/v/algebraic-structures.svg)
```

### 性能监控

```yaml
- name: Run performance benchmarks
  run: |
    pytest tests/performance/ --benchmark-only --benchmark-json=benchmark.json

- name: Upload benchmark results
  uses: actions/upload-artifact@v3
  with:
    name: benchmark-results
    path: benchmark.json
```

## 最佳实践

### 1. 工作流组织

- **单一职责**: 每个工作流专注于一个任务
- **可重用性**: 使用可重用的工作流
- **清晰命名**: 使用清晰的命名约定

### 2. 性能优化

- **缓存依赖**: 使用缓存加速构建
- **并行执行**: 并行运行独立任务
- **条件执行**: 只在必要时运行任务

### 3. 安全性

- **密钥管理**: 使用GitHub Secrets存储敏感信息
- **最小权限**: 使用最小必要权限
- **依赖扫描**: 定期扫描依赖漏洞

### 4. 错误处理

- **失败通知**: 及时通知失败
- **重试机制**: 对临时失败进行重试
- **详细日志**: 提供详细的错误日志

### 5. 可维护性

- **文档化**: 文档化所有工作流
- **版本控制**: 使用版本化的Actions
- **测试工作流**: 测试工作流本身

## 常见问题

### Q1: 如何调试失败的CI？

**A**:
1. 查看GitHub Actions日志
2. 在本地复现问题
3. 使用`act`工具本地测试
4. 检查依赖版本

### Q2: 如何加速CI？

**A**:
1. 使用缓存
2. 并行执行任务
3. 只运行必要的测试
4. 使用更快的运行器

### Q3: 如何处理flaky测试？

**A**:
1. 修复测试本身
2. 使用重试机制
3. 标记为flaky测试
4. 调查根本原因

### Q4: 如何管理多个环境？

**A**:
1. 使用环境保护规则
2. 使用不同的工作流
3. 使用矩阵策略
4. 使用条件执行

### Q5: 如何回滚部署？

**A**:
1. 使用版本标签
2. 保留旧版本
3. 使用回滚脚本
4. 监控部署状态

## 故障排除

### 常见错误

#### 1. 依赖安装失败

```yaml
# 解决方案：使用缓存和锁定版本
- name: Cache pip packages
  uses: actions/cache@v3
  with:
    path: ~/.cache/pip
    key: ${{ runner.os }}-pip-${{ hashFiles('**/requirements.txt') }}

- name: Install dependencies
  run: |
    pip install --upgrade pip
    pip install -r requirements.txt
```

#### 2. 测试超时

```yaml
# 解决方案：增加超时时间
- name: Run tests
  timeout-minutes: 30
  run: pytest
```

#### 3. 权限错误

```yaml
# 解决方案：检查权限设置
permissions:
  contents: read
  pull-requests: write
```

### 调试技巧

#### 1. 启用调试日志

```yaml
- name: Debug
  run: |
    echo "::debug::Debug information"
    echo "::warning::Warning message"
    echo "::error::Error message"
```

#### 2. 保存构建产物

```yaml
- name: Upload artifacts
  uses: actions/upload-artifact@v3
  with:
    name: test-results
    path: test-results/
```

#### 3. 本地测试

```bash
# 使用act工具本地测试
act -j test
```

## 工作流示例

### 完整CI工作流

```yaml
name: Complete CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: ['3.8', '3.9', '3.10', '3.11']

    steps:
    - uses: actions/checkout@v3

    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v4
      with:
        python-version: ${{ matrix.python-version }}
        cache: 'pip'

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-dev.txt

    - name: Run tests
      run: |
        pytest --cov=algebraic_structures --cov-report=xml

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml

  lint:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'

    - name: Install linting tools
      run: |
        pip install black flake8 mypy

    - name: Check code style
      run: |
        black --check .
        flake8 .
        mypy algebraic_structures

  security:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'

    - name: Install security tools
      run: |
        pip install safety bandit

    - name: Check dependencies
      run: safety check

    - name: Scan code
      run: bandit -r algebraic_structures
```

## 资源链接

### 相关文档

- **[测试指南](00-Python实现-代数结构测试指南.md)**: 测试编写和执行指南
- **[发布指南](00-Python实现-代数结构发布指南.md)**: 版本发布流程
- **[代码审查指南](00-Python实现-代数结构代码审查指南.md)**: 代码审查流程
- **[开发者指南](00-Python实现-代数结构开发者指南.md)**: 开发环境和技术细节

### 外部资源

- **GitHub Actions文档**: https://docs.github.com/en/actions
- **Python CI/CD最佳实践**: https://docs.python-guide.org/scenarios/ci/
- **Codecov文档**: https://docs.codecov.com/

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
