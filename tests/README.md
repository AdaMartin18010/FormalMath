# FormalMath 自动化测试套件

FormalMath项目的综合自动化测试解决方案，支持文档格式验证、Lean4代码测试和内容一致性检查。

## 📋 目录

- [概述](#概述)
- [功能特性](#功能特性)
- [安装要求](#安装要求)
- [快速开始](#快速开始)
- [测试模块](#测试模块)
- [使用指南](#使用指南)
- [CI/CD集成](#cicd集成)
- [覆盖率目标](#覆盖率目标)
- [报告说明](#报告说明)
- [故障排除](#故障排除)

## 🎯 概述

FormalMath测试套件是一个全面的自动化测试框架，旨在确保项目文档和代码的质量与一致性。测试套件包含三个主要模块：

1. **文档格式测试** - 验证Markdown语法、Frontmatter完整性和编码格式
2. **Lean4代码测试** - 检查Lean4代码的语法、导入依赖和编译
3. **内容一致性测试** - 验证MSC编码、交叉引用和术语一致性

## ✨ 功能特性

### 文档格式测试
- ✅ Markdown语法检查（标题、列表、表格、代码块）
- ✅ Frontmatter完整性验证（必需字段、MSC格式）
- ✅ 编码格式检查（UTF-8、无BOM、行尾格式）
- ✅ 内部链接有效性验证

### Lean4代码测试
- ✅ Lean4语法检查
- ✅ 导入依赖验证
- ✅ 编译测试（lake build）
- ✅ 代码风格检查

### 内容一致性测试
- ✅ MSC编码有效性验证
- ✅ 交叉引用检查
- ✅ 术语一致性验证
- ✅ 概念ID唯一性检查
- ✅ 多语言对齐检查

### 报告功能
- 📊 生成精美的HTML测试报告
- 📄 生成JSON格式报告（便于集成）
- 📈 测试覆盖率统计
- 🎨 交互式测试结果过滤

## 🔧 安装要求

### 必需
- Python 3.8+
- PyYAML (`pip install pyyaml`)

### 可选
- Lean4工具链（用于Lean4编译测试）
- Coverage.py (`pip install coverage`)
- lake（用于Lean4项目构建）

### 安装依赖

```bash
# 安装Python依赖
pip install pyyaml

# 可选: 安装覆盖率工具
pip install coverage

# 可选: 安装Lean4工具链
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## 🚀 快速开始

### 运行所有测试

```bash
cd tests
python run_tests.py
```

### 运行特定模块

```bash
# 文档格式测试
python run_tests.py --module document

# Lean4代码测试
python run_tests.py --module lean4

# 内容一致性测试
python run_tests.py --module content
```

### 生成报告

```bash
# 生成HTML报告
python run_tests.py --html

# 生成JSON报告
python run_tests.py --json

# 生成所有报告
python run_tests.py --html --json --coverage
```

### CI模式

```bash
# CI模式会自动启用所有报告选项
python run_tests.py --ci
```

## 🧪 测试模块

### 1. 文档格式测试 (`DocumentFormatTests`)

测试Markdown文档的格式和结构：

| 测试项 | 说明 | 优先级 |
|--------|------|--------|
| `test_01_markdown_syntax` | 检查Markdown语法正确性 | P0 |
| `test_02_frontmatter_integrity` | 验证Frontmatter完整性 | P0 |
| `test_03_encoding_format` | 检查编码格式规范 | P0 |
| `test_04_internal_links` | 验证内部链接有效性 | P1 |

**测试目标文件**：
- `concept/**/*.md`
- `docs/**/*.md`

**Frontmatter必需字段**：
```yaml
---
msc_primary: "03E99"        # 主MSC编码
msc_secondary: ["00A05"]    # 次MSC编码（可选）
---
```

### 2. Lean4代码测试 (`Lean4CodeTests`)

测试Lean4代码的质量：

| 测试项 | 说明 | 优先级 |
|--------|------|--------|
| `test_01_lean_syntax` | 检查Lean4语法 | P0 |
| `test_02_lean_imports` | 验证导入依赖 | P0 |
| `test_03_lean_compilation` | 编译测试 | P1 |

**测试目标文件**：
- `FormalMath-Enhanced/lean4/FormalMath/**/*.lean`（排除.lake目录）

### 3. 内容一致性测试 (`ContentConsistencyTests`)

测试内容的一致性和完整性：

| 测试项 | 说明 | 优先级 |
|--------|------|--------|
| `test_01_msc_code_validity` | MSC编码有效性 | P0 |
| `test_02_cross_reference_validity` | 交叉引用检查 | P1 |
| `test_03_terminology_consistency` | 术语一致性 | P1 |
| `test_04_concept_id_uniqueness` | 概念ID唯一性 | P0 |
| `test_05_multilang_alignment` | 多语言对齐 | P1 |

## 📖 使用指南

### 命令行参数

```
usage: run_tests.py [-h] [-m {document,lean4,content,all}] [--html] [--json] 
                    [--coverage] [-v {0,1,2}] [--ci] [--fail-fast]

FormalMath项目自动化测试运行器

可选参数:
  -h, --help            显示帮助信息
  -m {document,lean4,content,all}, --module {document,lean4,content,all}
                        选择测试模块 (默认: all)
  --html                生成HTML测试报告
  --json                生成JSON测试报告
  --coverage            计算测试覆盖率
  -v {0,1,2}, --verbosity {0,1,2}
                        测试输出详细程度 (默认: 1)
  --ci                  CI模式: 启用所有报告并简洁输出
  --fail-fast           遇到第一个失败时停止
```

### 使用示例

#### 基础用法

```bash
# 运行所有测试，详细输出
python run_tests.py -v 2

# 运行文档测试并生成HTML报告
python run_tests.py --module document --html

# CI环境使用
python run_tests.py --ci
```

#### 高级用法

```bash
# 运行测试并计算覆盖率
python run_tests.py --coverage

# 快速失败模式（调试使用）
python run_tests.py --module lean4 --fail-fast

# 静默模式（仅输出结果）
python run_tests.py -v 0 --html --json
```

### 作为模块导入

```python
from tests.test_suite import create_test_suite, create_specific_suite
import unittest

# 运行所有测试
suite = create_test_suite()
runner = unittest.TextTestRunner()
runner.run(suite)

# 运行特定模块
suite = create_specific_suite('document')
runner.run(suite)
```

## 🔁 CI/CD集成

### GitHub Actions

```yaml
name: FormalMath Tests

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.10'
      
      - name: Install dependencies
        run: |
          pip install pyyaml coverage
      
      - name: Run tests
        run: |
          cd tests
          python run_tests.py --ci
      
      - name: Upload test reports
        uses: actions/upload-artifact@v3
        if: always()
        with:
          name: test-reports
          path: tests/output/reports/
      
      - name: Check test results
        run: |
          # 解析JSON报告检查成功率
          success_rate=$(python -c "
          import json
          with open('tests/output/reports/test_report_latest.json') as f:
              data = json.load(f)
              print(data.get('success_rate', 0))
          ")
          if (( $(echo "$success_rate < 80" | bc -l) )); then
            echo "测试成功率低于80%"
            exit 1
          fi
```

### GitLab CI

```yaml
stages:
  - test

test:
  stage: test
  image: python:3.10
  script:
    - pip install pyyaml coverage
    - cd tests
    - python run_tests.py --ci
  artifacts:
    paths:
      - tests/output/reports/
    expire_in: 1 week
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
    - if: '$CI_COMMIT_BRANCH == "main"'
```

### Jenkins

```groovy
pipeline {
    agent any
    
    stages {
        stage('Test') {
            steps {
                sh '''
                    pip install pyyaml coverage
                    cd tests
                    python run_tests.py --ci
                '''
            }
        }
    }
    
    post {
        always {
            publishHTML([
                allowMissing: false,
                alwaysLinkToLastBuild: true,
                keepAll: true,
                reportDir: 'tests/output/reports',
                reportFiles: 'test_report_latest.html',
                reportName: 'FormalMath Test Report'
            ])
        }
    }
}
```

## 🎯 覆盖率目标

### 当前覆盖率目标: **80%+**

### 覆盖率计算范围

| 类别 | 包含 | 不包含 |
|------|------|--------|
| 文档文件 | concept/**/*.md, docs/**/*.md | 归档文件, 历史文档 |
| Lean4代码 | FormalMath-Enhanced/lean4/FormalMath/**/*.lean | .lake/packages/* |
| 配置文件 | *.yaml, *.json | 缓存文件, 临时文件 |

### 提升覆盖率的建议

1. **文档格式测试**
   - 确保所有Markdown文件符合规范
   - 完善Frontmatter信息
   - 修复编码格式问题

2. **Lean4代码测试**
   - 添加更多形式化证明
   - 确保所有定义都有对应定理
   - 补充缺失的import

3. **内容一致性测试**
   - 统一术语使用
   - 完善MSC编码
   - 建立完整的概念引用网络

## 📊 报告说明

### HTML报告

HTML报告包含以下内容：

1. **测试摘要卡片** - 总测试数、通过、失败、错误、跳过、覆盖率
2. **成功率进度条** - 可视化显示测试成功率
3. **详细结果表格** - 可筛选的测试结果列表
4. **错误详情** - 失败的测试详情和堆栈跟踪

报告位置：`tests/output/reports/test_report_latest.html`

### JSON报告

JSON报告包含机器可读的结构化数据：

```json
{
  "start_time": "2026-04-05T08:30:00",
  "end_time": "2026-04-05T08:35:00",
  "total_tests": 100,
  "passed": 85,
  "failed": 10,
  "errors": 5,
  "skipped": 0,
  "duration": 300.0,
  "success_rate": 85.0,
  "coverage": 82.5,
  "test_results": [
    {
      "name": "test_01_markdown_syntax",
      "test_class": "DocumentFormatTests",
      "status": "passed",
      "duration": 1.5
    }
  ]
}
```

报告位置：`tests/output/reports/test_report_latest.json`

## 🔧 故障排除

### 常见问题

#### 1. "未找到Lean可执行文件"

**问题**: Lean4代码测试被跳过

**解决**:
```bash
# 安装Lean4工具链
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
```

#### 2. "YAML解析错误"

**问题**: Frontmatter格式不正确

**解决**: 检查Markdown文件的Frontmatter格式，确保使用有效的YAML语法。

#### 3. 测试超时

**问题**: Lean4编译测试超时

**解决**: 
- 增加超时时间（修改代码中的timeout参数）
- 或使用 `--module document` 跳过编译测试

#### 4. 内存不足

**问题**: 测试大量文件时内存不足

**解决**: 
- 分批运行测试
- 限制并发文件数量（修改`[:100]`限制）

### 调试模式

```bash
# 详细输出
python run_tests.py -v 2

# 快速失败模式（便于调试）
python run_tests.py --fail-fast

# 仅测试特定文件
python -m unittest test_suite.DocumentFormatTests.test_01_markdown_syntax
```

## 📝 维护信息

### 添加新测试

1. 在对应的测试类中添加新方法
2. 方法名必须以`test_`开头
3. 使用`self.record_result()`记录结果
4. 更新本README文档

### 修改配置

配置项位于 `test_suite.py` 文件顶部：

```python
PROJECT_ROOT = Path(__file__).parent.parent  # 项目根目录
CONCEPT_DIR = PROJECT_ROOT / "concept"       # 概念目录
LEAN4_DIR = PROJECT_ROOT / "FormalMath-Enhanced/lean4/FormalMath"  # Lean4目录
ENCODING = 'utf-8'  # 文件编码
```

## 📄 许可证

本测试套件与FormalMath项目使用相同的许可证。

## 🤝 贡献

欢迎提交Issue和Pull Request来改进测试套件。

---

**最后更新**: 2026年4月5日  
**版本**: 1.0.0  
**维护者**: FormalMath项目团队
