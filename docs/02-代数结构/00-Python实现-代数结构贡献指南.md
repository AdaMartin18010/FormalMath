# 代数结构Python实现贡献指南

## 概述

感谢您对代数结构Python实现项目的兴趣！本文档提供如何为项目做出贡献的详细指南。

## 1. 贡献方式

### 1.1 代码贡献

- **修复Bug**: 报告和修复代码中的错误
- **新功能**: 实现新的算法或功能
- **性能优化**: 改进代码性能
- **代码重构**: 改进代码结构和可读性

### 1.2 文档贡献

- **完善文档**: 改进现有文档或添加新文档
- **翻译**: 翻译文档到其他语言
- **示例**: 添加更多使用示例
- **教程**: 编写教程和指南

### 1.3 测试贡献

- **单元测试**: 添加或改进单元测试
- **集成测试**: 添加集成测试
- **性能测试**: 添加性能基准测试
- **测试覆盖**: 提高测试覆盖率

### 1.4 其他贡献

- **问题报告**: 报告Bug或提出改进建议
- **功能请求**: 提出新功能需求
- **代码审查**: 审查Pull Request
- **社区支持**: 帮助其他用户

## 2. 开发流程

### 2.1 准备工作

1. **Fork项目**

   ```bash
   # 在GitHub上Fork项目
   ```

2. **克隆仓库**

   ```bash
   git clone https://github.com/your-username/algebraic-structures.git
   cd algebraic-structures
   ```

3. **设置开发环境**

   ```bash
   # 创建虚拟环境
   python -m venv venv
   source venv/bin/activate  # Linux/macOS
   # 或
   venv\Scripts\activate  # Windows

   # 安装开发依赖
   pip install -r requirements-dev.txt
   pip install -e .
   ```

4. **创建分支**

   ```bash
   git checkout -b feature/your-feature-name
   # 或
   git checkout -b fix/your-bug-fix
   ```

### 2.2 开发规范

#### 代码风格

- **遵循PEP 8**: Python代码风格指南
- **使用Black**: 自动格式化代码
- **类型提示**: 为函数和类添加类型注解
- **文档字符串**: 使用Google风格的docstring

示例：

```python
from typing import List, Optional

def find_subgroups(
    group: FiniteGroup,
    max_order: Optional[int] = None
) -> List[FiniteGroup]:
    """
    查找群的所有子群。

    Args:
        group: 要查找子群的群
        max_order: 最大子群阶数（可选）

    Returns:
        所有子群的列表

    Raises:
        ValueError: 如果群无效
    """
    # 实现代码
    pass
```

#### 命名规范

- **类名**: 使用PascalCase（如`FiniteGroup`）
- **函数名**: 使用snake_case（如`find_subgroups`）
- **常量**: 使用UPPER_SNAKE_CASE（如`MAX_ITERATIONS`）
- **私有方法**: 使用前导下划线（如`_internal_method`）

#### 提交信息

使用清晰的提交信息：

```bash
# 好的提交信息
git commit -m "feat: 添加循环群子群查找算法"
git commit -m "fix: 修复有限域乘法逆元计算错误"
git commit -m "docs: 更新群论API文档"
git commit -m "test: 添加环论单元测试"

# 提交信息格式
<type>: <subject>

# 类型：
# feat: 新功能
# fix: Bug修复
# docs: 文档更新
# test: 测试相关
# refactor: 代码重构
# perf: 性能优化
# style: 代码格式
# chore: 构建/工具相关
```

### 2.3 测试要求

#### 编写测试

```python
import pytest
from algebraic_structures.group_theory import FiniteGroup, cyclic_group

class TestCyclicGroup:
    """循环群测试类"""

    def test_order(self):
        """测试群的阶"""
        G = cyclic_group(6)
        assert G.order() == 6

    def test_identity(self):
        """测试单位元"""
        G = cyclic_group(6)
        e = G.identity()
        for g in G.elements():
            assert G.operation(e, g) == g
            assert G.operation(g, e) == g

    def test_inverse(self):
        """测试逆元"""
        G = cyclic_group(6)
        for g in G.elements():
            inv = G.inverse(g)
            assert G.operation(g, inv) == G.identity()

    @pytest.mark.parametrize("n", [1, 2, 3, 5, 7, 10])
    def test_cyclic_group_properties(self, n):
        """参数化测试"""
        G = cyclic_group(n)
        assert G.order() == n
        assert G.is_cyclic()
```

#### 运行测试

```bash
# 运行所有测试
pytest

# 运行特定测试文件
pytest tests/test_groups.py

# 运行特定测试类
pytest tests/test_groups.py::TestCyclicGroup

# 运行测试并生成覆盖率报告
pytest --cov=algebraic_structures --cov-report=html

# 查看覆盖率报告
# 打开 htmlcov/index.html
```

#### 测试覆盖率要求

- **新代码**: 至少80%覆盖率
- **关键算法**: 100%覆盖率
- **边界情况**: 必须测试

### 2.4 代码审查

#### 提交Pull Request

1. **推送分支**

   ```bash
   git push origin feature/your-feature-name
   ```

2. **创建Pull Request**
   - 在GitHub上创建PR
   - 填写PR描述
   - 关联相关Issue（如果有）

3. **PR描述模板**

   ```markdown
   ## 描述
   简要描述本次更改

   ## 类型
   - [ ] Bug修复
   - [ ] 新功能
   - [ ] 文档更新
   - [ ] 性能优化
   - [ ] 代码重构

   ## 测试
   - [ ] 添加了单元测试
   - [ ] 所有测试通过
   - [ ] 测试覆盖率达标

   ## 检查清单
   - [ ] 代码遵循PEP 8
   - [ ] 添加了类型提示
   - [ ] 更新了文档
   - [ ] 更新了CHANGELOG
   ```

#### 代码审查流程

1. **自动检查**
   - CI/CD运行测试
   - 代码风格检查
   - 类型检查

2. **人工审查**
   - 至少一名维护者审查
   - 检查代码质量和正确性
   - 检查测试覆盖

3. **反馈处理**
   - 根据反馈修改代码
   - 重新提交审查

4. **合并**
   - 审查通过后合并
   - 删除功能分支

## 3. 代码规范详解

### 3.1 类型提示

```python
from typing import List, Dict, Optional, Tuple, Union, Callable

# 基本类型
def add(a: int, b: int) -> int:
    return a + b

# 容器类型
def process_items(items: List[str]) -> Dict[str, int]:
    return {item: len(item) for item in items}

# 可选类型
def find_element(items: List[int], value: int) -> Optional[int]:
    return next((i for i in items if i == value), None)

# 联合类型
def process(value: Union[int, str]) -> str:
    return str(value)

# 函数类型
def apply_function(
    func: Callable[[int, int], int],
    a: int,
    b: int
) -> int:
    return func(a, b)
```

### 3.2 文档字符串

```python
class FiniteGroup:
    """
    有限群类。

    表示一个有限群，支持群运算、子群查找、共轭类计算等操作。

    Attributes:
        elements: 群的所有元素
        operation: 群运算函数
        identity: 单位元

    Example:
        >>> G = FiniteGroup([0, 1, 2], lambda a, b: (a + b) % 3)
        >>> G.order()
        3
        >>> G.is_abelian()
        True
    """

    def __init__(self, elements: List[GroupElement], operation: Callable):
        """
        初始化有限群。

        Args:
            elements: 群元素列表
            operation: 二元运算函数

        Raises:
            ValueError: 如果元素列表为空或运算不满足群公理
        """
        pass

    def order(self) -> int:
        """
        返回群的阶。

        Returns:
            群的阶（元素个数）
        """
        return len(self.elements)
```

### 3.3 错误处理

```python
def divide(a: float, b: float) -> float:
    """
    除法运算。

    Args:
        a: 被除数
        b: 除数

    Returns:
        商

    Raises:
        ZeroDivisionError: 如果除数为0
        TypeError: 如果参数类型不正确
    """
    if not isinstance(a, (int, float)):
        raise TypeError(f"a必须是数字，得到{type(a)}")
    if not isinstance(b, (int, float)):
        raise TypeError(f"b必须是数字，得到{type(b)}")
    if b == 0:
        raise ZeroDivisionError("除数不能为0")
    return a / b
```

## 4. 项目结构

### 4.1 目录组织

```text
algebraic_structures/
├── src/
│   └── algebraic_structures/
│       ├── __init__.py
│       ├── group_theory/
│       │   ├── __init__.py
│       │   ├── groups.py
│       │   └── representations.py
│       └── ...
├── tests/
│   ├── __init__.py
│   ├── test_groups.py
│   └── ...
├── docs/
│   ├── api/
│   └── tutorials/
└── examples/
    └── ...
```

### 4.2 模块组织原则

- **单一职责**: 每个模块只负责一个功能领域
- **低耦合**: 模块之间依赖最小化
- **高内聚**: 相关功能组织在一起
- **可扩展**: 易于添加新功能

## 5. 数学正确性

### 5.1 公理验证

所有代数结构实现必须验证数学公理：

```python
def verify_group_axioms(group: FiniteGroup) -> bool:
    """
    验证群公理。

    检查：
    1. 封闭性
    2. 结合律
    3. 单位元存在
    4. 逆元存在
    """
    # 实现验证逻辑
    pass
```

### 5.2 定理实现

实现数学定理时，必须：

- 提供定理的数学表述
- 实现算法
- 提供证明或引用
- 添加测试用例

### 5.3 算法正确性

- 使用已知正确的算法
- 与标准实现对比验证
- 测试边界情况
- 处理数值误差

## 6. 性能考虑

### 6.1 性能要求

- **时间复杂度**: 使用最优算法
- **空间复杂度**: 优化内存使用
- **缓存**: 对重复计算使用缓存
- **向量化**: 使用NumPy进行向量化运算

### 6.2 性能测试

```python
import time
import pytest

def test_performance():
    """性能测试"""
    start = time.time()
    result = expensive_operation()
    elapsed = time.time() - start

    assert elapsed < 1.0  # 必须在1秒内完成
    assert result is not None
```

## 7. 文档要求

### 7.1 代码文档

- 所有公共API必须有文档字符串
- 复杂算法必须有注释
- 示例代码必须可运行

### 7.2 用户文档

- 更新相关用户文档
- 添加使用示例
- 更新API参考

## 8. 许可证

### 8.1 代码许可

- 所有贡献的代码必须使用MIT许可证
- 确保代码不侵犯第三方版权

### 8.2 文档许可

- 文档使用相同的许可证
- 引用外部资源时注明来源

## 9. 行为准则

### 9.1 社区准则

- **尊重**: 尊重所有贡献者
- **包容**: 欢迎不同背景的贡献者
- **专业**: 保持专业和礼貌
- **协作**: 积极协作和沟通

### 9.2 沟通渠道

- **GitHub Issues**: 报告问题和讨论
- **Pull Requests**: 代码审查和讨论
- **讨论区**: 一般性讨论
- **邮件**: 敏感问题

## 10. 获取帮助

### 10.1 常见问题

查看文档和FAQ：

- 完整指南
- 快速参考
- 示例项目

### 10.2 联系维护者

- 通过GitHub Issues
- 通过邮件列表
- 通过讨论区

## 11. 贡献者认可

### 11.1 贡献者列表

所有贡献者将被列在：

- README.md
- CONTRIBUTORS.md
- 项目文档

### 11.2 致谢

- 重大贡献将在发布说明中特别致谢
- 定期更新贡献者列表

## 12. 资源链接

- **完整指南**: `00-Python实现-代数结构完整指南.md`
- **快速参考**: `00-Python实现-代数结构快速参考.md`
- **安装指南**: `00-Python实现-代数结构安装部署指南.md`
- **示例项目**: `00-Python实现-代数结构示例项目.md`

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
