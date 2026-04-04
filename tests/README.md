# FormalMath 自动化测试系统

## 概述

本文档描述 FormalMath 项目的全面自动化测试体系，包括前端测试、后端测试、Lean4测试和CI/CD集成。

## 测试架构

```
tests/
├── frontend/           # 前端测试
│   ├── unit/          # 单元测试 (Jest)
│   ├── e2e/           # 端到端测试 (Cypress)
│   ├── __mocks__/     # Mock模块
│   └── coverage/      # 覆盖率报告
├── backend/           # 后端测试
│   ├── unit/          # Python单元测试
│   ├── integration/   # 集成测试
│   └── coverage/      # 覆盖率报告
├── lean4/             # Lean4测试
│   ├── FormalMathTests/  # 测试库
│   └── Test/          # 测试入口
└── integration/       # 全栈集成测试
```

## 前端测试

### 技术栈
- **Jest**: 单元测试框架
- **React Testing Library**: React组件测试
- **Cypress**: E2E测试
- **MSW**: API Mock

### 运行测试

```bash
# 安装依赖
cd tests
npm install

# 运行单元测试
npm run test:unit

# 运行单元测试（监视模式）
npm run test:unit:watch

# 运行E2E测试
npm run test:e2e

# 打开Cypress交互式界面
npm run test:e2e:open

# 生成覆盖率报告
npm run test:unit -- --coverage
```

### 测试规范

1. **单元测试**
   - 组件测试: `*.test.tsx`
   - Hook测试: `*.test.ts`
   - 工具函数: `*.test.ts`
   - 覆盖率要求: 70%

2. **E2E测试**
   - 测试文件: `*.cy.ts`
   - 测试场景: 用户完整工作流
   - 支持视口: 桌面(1280x720)、平板(768x1024)、移动(375x667)

## 后端测试

### 技术栈
- **Pytest**: 测试框架
- **pytest-cov**: 覆盖率
- **pytest-mock**: Mock工具
- **responses**: HTTP Mock

### 运行测试

```bash
# 安装依赖
cd tests/backend
pip install -r requirements-test.txt

# 运行所有测试
pytest

# 运行单元测试
pytest unit/

# 运行集成测试
pytest integration/ -m integration

# 生成覆盖率报告
pytest --cov=../../tools --cov-report=html

# 运行特定标记的测试
pytest -m "not slow"
```

### 测试规范

1. **单元测试**
   - 测试文件: `test_*.py`
   - 测试类: `Test*` 
   - 测试函数: `test_*`
   - 覆盖率要求: 70%

2. **集成测试**
   - 使用 `@pytest.mark.integration` 标记
   - 测试完整工作流
   - 可能需要外部服务

## Lean4测试

### 技术栈
- **Lake**: Lean4构建工具
- **Mathlib4**: 数学库

### 运行测试

```bash
# 进入测试目录
cd tests/lean4

# 安装依赖
lake update

# 构建测试
lake build

# 运行测试
lake test

# 检查证明
lake check
```

### 测试结构

```lean4
-- FormalMathTests/Basic.lean: 基础数学测试
-- FormalMathTests/Graph.lean: 知识图谱测试
-- Test/Main.lean: 测试主入口
```

## CI/CD集成

### GitHub Actions工作流

1. **CI工作流** (`.github/workflows/ci.yml`)
   - 前端测试
   - 后端测试
   - Lean4测试
   - E2E测试
   - 代码质量检查
   - 构建测试

2. **CD工作流** (`.github/workflows/cd.yml`)
   - 构建Docker镜像
   - 部署到Staging
   - 部署到Production
   - 发布文档

### 触发条件

- **Push到main/develop分支**: 运行完整CI
- **Pull Request**: 运行代码检查和单元测试
- **Tag发布**: 触发CD部署
- **手动触发**: 可指定部署环境

## 覆盖率要求

| 组件 | 目标覆盖率 | 最低覆盖率 |
|------|-----------|-----------|
| 前端单元测试 | 80% | 70% |
| 后端单元测试 | 80% | 70% |
| E2E测试 | - | 核心流程 |
| Lean4测试 | 100% | 核心定理 |

## 测试数据

### 前端Mock数据
- `tests/frontend/e2e/fixtures/`: E2E测试数据
- `tests/frontend/__mocks__/`: Mock模块

### 后端Fixture
- `tests/backend/conftest.py`: 共享fixture
- `pytest.fixture`: 测试数据生成

## 环境变量

```bash
# 测试环境
TESTING=true
API_URL=http://localhost:8000
FRONTEND_URL=http://localhost:3000

# CI环境
CI=true
COVERAGE=true
```

## 最佳实践

1. **测试独立性**: 每个测试应该独立运行，不依赖其他测试
2. **Mock外部依赖**: 使用Mock隔离外部服务
3. **清理数据**: 测试后清理创建的数据
4. **描述性命名**: 测试名称应该清楚描述测试内容
5. **AAA模式**: Arrange(准备)、Act(执行)、Assert(断言)

## 故障排除

### 常见问题

1. **前端测试失败**
   ```bash
   # 清除缓存
   rm -rf node_modules .jest-cache
   npm install
   ```

2. **后端测试失败**
   ```bash
   # 重新安装依赖
   pip install -r requirements-test.txt --force-reinstall
   ```

3. **Lean4测试失败**
   ```bash
   # 清理lake构建
   lake clean
   lake build
   ```

### 调试技巧

- 使用 `--verbose` 查看详细输出
- 使用 `--pdb` 进入调试模式
- 使用 `--tb=long` 查看完整堆栈

## 贡献指南

1. 为新功能编写对应的测试
2. 保持测试代码简洁清晰
3. 更新此文档以反映测试变化
4. 确保所有测试通过后再提交PR

## 相关链接

- [Jest文档](https://jestjs.io/docs/getting-started)
- [Cypress文档](https://docs.cypress.io/)
- [Pytest文档](https://docs.pytest.org/)
- [Lean4文档](https://leanprover.github.io/lean4/doc/)
