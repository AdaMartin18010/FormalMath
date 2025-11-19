# 代数结构Python实现测试指南

## 概述

本文档提供代数结构Python实现的完整测试指南，包括测试策略、测试类型、测试工具、测试实践和测试最佳实践。

## 目录

- [代数结构Python实现测试指南](#代数结构python实现测试指南)
  - [概述](#概述)
  - [目录](#目录)
  - [测试策略](#测试策略)
    - [测试金字塔](#测试金字塔)
    - [测试原则](#测试原则)
    - [测试目标](#测试目标)
  - [测试类型](#测试类型)
    - [1. 单元测试](#1-单元测试)
      - [目的](#目的)
      - [示例](#示例)
    - [2. 集成测试](#2-集成测试)
      - [目的](#目的-1)
      - [示例](#示例-1)
    - [3. 数学公理测试](#3-数学公理测试)
      - [目的](#目的-2)
      - [示例](#示例-2)
    - [4. 边界测试](#4-边界测试)
      - [目的](#目的-3)
      - [示例](#示例-3)
    - [5. 性能测试](#5-性能测试)
      - [目的](#目的-4)
      - [示例](#示例-4)
    - [6. 回归测试](#6-回归测试)
      - [目的](#目的-5)
      - [示例](#示例-5)
  - [测试工具](#测试工具)
    - [1. pytest](#1-pytest)
      - [安装](#安装)
      - [基本使用](#基本使用)
    - [2. 测试覆盖率](#2-测试覆盖率)
      - [安装](#安装-1)
      - [使用](#使用)
    - [3. 参数化测试](#3-参数化测试)
    - [4. 测试标记](#4-测试标记)
  - [测试实践](#测试实践)
    - [1. 测试文件组织](#1-测试文件组织)
    - [2. 测试夹具](#2-测试夹具)
    - [3. 测试数据](#3-测试数据)
    - [4. 模拟和存根](#4-模拟和存根)
  - [测试覆盖率](#测试覆盖率)
    - [覆盖率目标](#覆盖率目标)
    - [覆盖率报告](#覆盖率报告)
    - [覆盖率分析](#覆盖率分析)
  - [持续集成](#持续集成)
    - [GitHub Actions配置](#github-actions配置)
  - [测试最佳实践](#测试最佳实践)
    - [1. 测试命名](#1-测试命名)
    - [2. 测试组织](#2-测试组织)
    - [3. 测试独立性](#3-测试独立性)
    - [4. 测试断言](#4-测试断言)
    - [5. 测试文档](#5-测试文档)
  - [常见问题](#常见问题)
    - [1. 如何运行特定测试？](#1-如何运行特定测试)
    - [2. 如何跳过慢速测试？](#2-如何跳过慢速测试)
    - [3. 如何查看测试覆盖率？](#3-如何查看测试覆盖率)
    - [4. 如何处理测试数据？](#4-如何处理测试数据)
    - [5. 如何测试异常？](#5-如何测试异常)
  - [资源链接](#资源链接)


## 测试策略

### 测试金字塔

```text
        /\
       /  \      E2E测试 (少量)
      /____\
     /      \    集成测试 (中等)
    /________\
   /          \  单元测试 (大量)
  /____________\
```

### 测试原则

1. **全面性**: 覆盖所有功能和边界情况
2. **独立性**: 测试之间相互独立
3. **可重复性**: 测试结果可重复
4. **快速性**: 测试执行速度快
5. **可维护性**: 测试代码易于维护

### 测试目标

- **功能正确性**: 确保代码功能正确
- **数学正确性**: 确保数学算法正确
- **性能保证**: 确保性能满足要求
- **稳定性**: 确保代码稳定可靠

## 测试类型

### 1. 单元测试

#### 目的

测试单个函数或类的功能。

#### 示例

```python
import pytest
from algebraic_structures.groups import FiniteGroup, cyclic_group

class TestCyclicGroup:
    """测试循环群"""

    def test_creation(self):
        """测试创建循环群"""
        G = cyclic_group(6)
        assert G.order() == 6
        assert len(G.elements) == 6

    def test_operation(self):
        """测试群运算"""
        G = cyclic_group(6)
        a, b = G.elements[1], G.elements[2]
        result = G.operation(a, b)
        assert result in G.elements

    def test_identity(self):
        """测试单位元"""
        G = cyclic_group(6)
        e = G.identity()
        for g in G.elements:
            assert G.operation(g, e) == g
            assert G.operation(e, g) == g

    def test_inverse(self):
        """测试逆元"""
        G = cyclic_group(6)
        for g in G.elements:
            inv = G.inverse(g)
            assert G.operation(g, inv) == G.identity()

    @pytest.mark.parametrize("n", [1, 2, 3, 5, 7, 10, 12])
    def test_cyclic_properties(self, n):
        """参数化测试循环群性质"""
        G = cyclic_group(n)
        assert G.order() == n
        assert G.is_cyclic()
```

### 2. 集成测试

#### 目的

测试多个模块之间的交互。

#### 示例

```python
import pytest
from algebraic_structures.groups import FiniteGroup, cyclic_group
from algebraic_structures.rings import IntegerModRing
from algebraic_structures.fields import FiniteField

class TestIntegration:
    """集成测试"""

    def test_group_ring_integration(self):
        """测试群和环的集成"""
        G = cyclic_group(6)
        R = IntegerModRing(7)

        # 验证它们可以独立工作
        assert G.order() == 6
        assert R.order() == 7

    def test_field_operations(self):
        """测试域运算"""
        F = FiniteField(7)
        a, b = F.elements[1], F.elements[2]

        # 加法
        sum_result = F.add(a, b)
        assert sum_result in F.elements

        # 乘法
        prod_result = F.multiply(a, b)
        assert prod_result in F.elements

        # 除法
        if b != F.zero():
            div_result = F.divide(a, b)
            assert div_result in F.elements
```

### 3. 数学公理测试

#### 目的

验证数学公理的正确性。

#### 示例

```python
import pytest
from algebraic_structures.groups import FiniteGroup, cyclic_group

class TestGroupAxioms:
    """测试群公理"""

    def test_closure(self):
        """测试封闭性"""
        G = cyclic_group(6)
        for a in G.elements:
            for b in G.elements:
                result = G.operation(a, b)
                assert result in G.elements

    def test_associativity(self):
        """测试结合律"""
        G = cyclic_group(6)
        elements = G.elements
        for a, b, c in zip(elements, elements[1:], elements[2:]):
            left = G.operation(G.operation(a, b), c)
            right = G.operation(a, G.operation(b, c))
            assert left == right

    def test_identity(self):
        """测试单位元"""
        G = cyclic_group(6)
        e = G.identity()
        for a in G.elements:
            assert G.operation(e, a) == a
            assert G.operation(a, e) == a

    def test_inverse(self):
        """测试逆元"""
        G = cyclic_group(6)
        e = G.identity()
        for a in G.elements:
            inv = G.inverse(a)
            assert G.operation(a, inv) == e
            assert G.operation(inv, a) == e
```

### 4. 边界测试

#### 目的

测试边界情况和极端情况。

#### 示例

```python
import pytest
from algebraic_structures.groups import FiniteGroup, cyclic_group

class TestEdgeCases:
    """测试边界情况"""

    def test_trivial_group(self):
        """测试平凡群"""
        G = cyclic_group(1)
        assert G.order() == 1
        assert len(G.elements) == 1

    def test_large_group(self):
        """测试大群"""
        G = cyclic_group(1000)
        assert G.order() == 1000
        # 验证基本操作仍然有效
        a, b = G.elements[0], G.elements[1]
        result = G.operation(a, b)
        assert result in G.elements

    def test_empty_input(self):
        """测试空输入"""
        with pytest.raises(ValueError):
            cyclic_group(0)

    def test_negative_input(self):
        """测试负输入"""
        with pytest.raises(ValueError):
            cyclic_group(-1)
```

### 5. 性能测试

#### 目的

测试代码性能。

#### 示例

```python
import pytest
import time
from algebraic_structures.groups import FiniteGroup, cyclic_group

class TestPerformance:
    """性能测试"""

    def test_group_creation_performance(self):
        """测试群创建性能"""
        start = time.time()
        G = cyclic_group(1000)
        elapsed = time.time() - start
        assert elapsed < 1.0  # 必须在1秒内完成

    def test_operation_performance(self):
        """测试运算性能"""
        G = cyclic_group(1000)
        a, b = G.elements[0], G.elements[1]

        start = time.time()
        for _ in range(1000):
            G.operation(a, b)
        elapsed = time.time() - start

        assert elapsed < 0.1  # 1000次运算必须在0.1秒内完成

    @pytest.mark.slow
    def test_large_group_performance(self):
        """测试大群性能（标记为慢速测试）"""
        G = cyclic_group(10000)
        assert G.order() == 10000
```

### 6. 回归测试

#### 目的

防止已修复的bug再次出现。

#### 示例

```python
import pytest
from algebraic_structures.groups import FiniteGroup, cyclic_group

class TestRegression:
    """回归测试"""

    def test_fixed_bug_001(self):
        """测试已修复的bug #001"""
        # Bug: 循环群创建时元素顺序错误
        G = cyclic_group(6)
        assert G.elements[0] == G.identity()

    def test_fixed_bug_002(self):
        """测试已修复的bug #002"""
        # Bug: 逆元计算错误
        G = cyclic_group(6)
        for g in G.elements:
            inv = G.inverse(g)
            assert G.operation(g, inv) == G.identity()
```

## 测试工具

### 1. pytest

#### 安装

```bash
pip install pytest pytest-cov pytest-mock
```

#### 基本使用

```bash
# 运行所有测试
pytest

# 运行特定测试文件
pytest tests/test_groups.py

# 运行特定测试类
pytest tests/test_groups.py::TestCyclicGroup

# 运行特定测试方法
pytest tests/test_groups.py::TestCyclicGroup::test_creation

# 运行并显示详细输出
pytest -v

# 运行并显示打印语句
pytest -s
```

### 2. 测试覆盖率

#### 安装

```bash
pip install pytest-cov
```

#### 使用

```bash
# 运行测试并生成覆盖率报告
pytest --cov=algebraic_structures --cov-report=html

# 查看覆盖率报告
# 打开 htmlcov/index.html

# 生成终端报告
pytest --cov=algebraic_structures --cov-report=term

# 设置覆盖率阈值
pytest --cov=algebraic_structures --cov-report=term --cov-fail-under=80
```

### 3. 参数化测试

```python
import pytest
from algebraic_structures.groups import cyclic_group

@pytest.mark.parametrize("n,expected_order", [
    (1, 1),
    (2, 2),
    (3, 3),
    (5, 5),
    (7, 7),
    (10, 10),
    (12, 12),
])
def test_cyclic_group_order(n, expected_order):
    """参数化测试循环群的阶"""
    G = cyclic_group(n)
    assert G.order() == expected_order
```

### 4. 测试标记

```python
import pytest

@pytest.mark.slow
def test_slow_operation():
    """慢速测试"""
    # 运行慢速测试: pytest -m slow
    pass

@pytest.mark.skip(reason="功能未实现")
def test_unimplemented():
    """跳过测试"""
    pass

@pytest.mark.skipif(sys.platform == "win32", reason="Windows不支持")
def test_platform_specific():
    """条件跳过测试"""
    pass
```

## 测试实践

### 1. 测试文件组织

```text
tests/
├── __init__.py
├── test_groups.py
├── test_rings.py
├── test_fields.py
├── test_modules.py
├── test_representations.py
├── test_lie_algebras.py
├── test_integration.py
├── test_performance.py
└── fixtures/
    ├── __init__.py
    └── common.py
```

### 2. 测试夹具

```python
import pytest
from algebraic_structures.groups import cyclic_group

@pytest.fixture
def small_group():
    """小群夹具"""
    return cyclic_group(6)

@pytest.fixture
def large_group():
    """大群夹具"""
    return cyclic_group(100)

@pytest.fixture
def groups():
    """多个群夹具"""
    return [cyclic_group(n) for n in [3, 5, 7, 11]]

def test_with_fixture(small_group):
    """使用夹具的测试"""
    assert small_group.order() == 6
```

### 3. 测试数据

```python
import pytest
from algebraic_structures.groups import cyclic_group

# 测试数据
TEST_GROUPS = [
    (1, 1),
    (2, 2),
    (3, 3),
    (5, 5),
    (7, 7),
    (10, 10),
    (12, 12),
]

@pytest.mark.parametrize("n,expected", TEST_GROUPS)
def test_group_order(n, expected):
    """使用测试数据"""
    G = cyclic_group(n)
    assert G.order() == expected
```

### 4. 模拟和存根

```python
import pytest
from unittest.mock import Mock, patch
from algebraic_structures.groups import FiniteGroup

def test_with_mock():
    """使用模拟对象"""
    mock_group = Mock(spec=FiniteGroup)
    mock_group.order.return_value = 6
    assert mock_group.order() == 6

@patch('algebraic_structures.groups.cyclic_group')
def test_with_patch(mock_cyclic):
    """使用补丁"""
    mock_cyclic.return_value.order.return_value = 6
    result = mock_cyclic(6)
    assert result.order() == 6
```

## 测试覆盖率

### 覆盖率目标

- **总体覆盖率**: 80%+
- **核心算法**: 100%
- **公共API**: 100%
- **边界情况**: 90%+

### 覆盖率报告

```bash
# 生成HTML报告
pytest --cov=algebraic_structures --cov-report=html

# 生成XML报告（用于CI/CD）
pytest --cov=algebraic_structures --cov-report=xml

# 生成终端报告
pytest --cov=algebraic_structures --cov-report=term-missing
```

### 覆盖率分析

```python
# 检查未覆盖的代码
# 1. 运行覆盖率测试
# 2. 查看htmlcov/index.html
# 3. 识别未覆盖的代码行
# 4. 添加相应的测试
```

## 持续集成

### GitHub Actions配置

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        python-version: [3.8, 3.9, '3.10', '3.11']

    steps:
    - uses: actions/checkout@v2
    - name: Set up Python ${{ matrix.python-version }}
      uses: actions/setup-python@v2
      with:
        python-version: ${{ matrix.python-version }}

    - name: Install dependencies
      run: |
        python -m pip install --upgrade pip
        pip install -r requirements.txt
        pip install -r requirements-dev.txt

    - name: Run tests
      run: |
        pytest --cov=algebraic_structures --cov-report=xml

    - name: Upload coverage
      uses: codecov/codecov-action@v2
      with:
        file: ./coverage.xml
```

## 测试最佳实践

### 1. 测试命名

```python
# ✅ 好的命名
def test_cyclic_group_creation():
    """测试循环群创建"""
    pass

def test_group_operation_commutativity():
    """测试群运算交换性"""
    pass

# ❌ 不好的命名
def test1():
    """测试1"""
    pass

def test_thing():
    """测试东西"""
    pass
```

### 2. 测试组织

```python
# ✅ 好的组织
class TestCyclicGroup:
    """测试循环群"""

    def test_creation(self):
        """测试创建"""
        pass

    def test_operation(self):
        """测试运算"""
        pass

# ❌ 不好的组织
def test_everything():
    """测试所有内容"""
    # 太多测试混在一起
    pass
```

### 3. 测试独立性

```python
# ✅ 独立的测试
def test_group_creation():
    """每个测试独立"""
    G = cyclic_group(6)
    assert G.order() == 6

def test_group_operation():
    """不依赖其他测试"""
    G = cyclic_group(6)
    a, b = G.elements[0], G.elements[1]
    assert G.operation(a, b) in G.elements

# ❌ 依赖的测试
class_state = None

def test_setup():
    """设置状态"""
    global class_state
    class_state = cyclic_group(6)

def test_use_state():
    """依赖setup"""
    # 如果setup失败，这个测试也会失败
    assert class_state.order() == 6
```

### 4. 测试断言

```python
# ✅ 明确的断言
def test_group_order():
    """明确的断言"""
    G = cyclic_group(6)
    assert G.order() == 6, "循环群Z6的阶应该是6"

# ❌ 模糊的断言
def test_group():
    """模糊的断言"""
    G = cyclic_group(6)
    assert G  # 太模糊
```

### 5. 测试文档

```python
# ✅ 好的文档
def test_cyclic_group_creation():
    """
    测试循环群的创建。

    验证：
    - 群可以正确创建
    - 群的阶正确
    - 群的元素正确
    """
    G = cyclic_group(6)
    assert G.order() == 6
    assert len(G.elements) == 6

# ❌ 缺少文档
def test_thing():
    """测试"""
    pass
```

## 常见问题

### 1. 如何运行特定测试？

```bash
# 运行特定文件
pytest tests/test_groups.py

# 运行特定类
pytest tests/test_groups.py::TestCyclicGroup

# 运行特定方法
pytest tests/test_groups.py::TestCyclicGroup::test_creation
```

### 2. 如何跳过慢速测试？

```bash
# 跳过标记为slow的测试
pytest -m "not slow"
```

### 3. 如何查看测试覆盖率？

```bash
# 生成HTML报告
pytest --cov=algebraic_structures --cov-report=html
# 然后打开 htmlcov/index.html
```

### 4. 如何处理测试数据？

```python
# 使用夹具
@pytest.fixture
def test_data():
    return {"group": cyclic_group(6)}

def test_with_data(test_data):
    assert test_data["group"].order() == 6
```

### 5. 如何测试异常？

```python
def test_invalid_input():
    """测试无效输入"""
    with pytest.raises(ValueError):
        cyclic_group(0)
```

## 资源链接

- **[贡献指南](00-Python实现-代数结构贡献指南.md)**: 包含测试要求
- **[最佳实践](00-Python实现-代数结构最佳实践.md)**: 包含测试最佳实践
- **[故障排除指南](00-Python实现-代数结构故障排除与调试指南.md)**: 测试问题诊断

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
