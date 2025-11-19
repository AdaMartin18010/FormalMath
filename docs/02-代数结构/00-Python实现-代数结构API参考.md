# 代数结构Python实现API参考

## 概述

本文档提供代数结构Python实现库的完整API参考，包括所有公共类、函数和方法的详细说明。

## 目录

- [群论API](#群论api)
- [环论API](#环论api)
- [域论API](#域论api)
- [模论API](#模论api)
- [表示论API](#表示论api)
- [李代数API](#李代数api)
- [范畴论API](#范畴论api)
- [线性代数API](#线性代数api)
- [综合工具API](#综合工具api)

## 群论API

### 类

#### `FiniteGroup`

有限群类。

```python
class FiniteGroup:
    """有限群类"""

    def __init__(self, elements: List[GroupElement], operation: Callable):
        """
        初始化有限群。

        参数:
            elements: 群元素列表
            operation: 群运算函数
        """
        pass

    def order(self) -> int:
        """返回群的阶"""
        pass

    def identity(self) -> GroupElement:
        """返回单位元"""
        pass

    def contains(self, element: GroupElement) -> bool:
        """检查元素是否在群中"""
        pass

    def __contains__(self, element: GroupElement) -> bool:
        """支持 in 操作符"""
        pass
```

#### `GroupElement`

群元素类。

```python
class GroupElement:
    """群元素类"""

    def __init__(self, value, group: FiniteGroup):
        """
        初始化群元素。

        参数:
            value: 元素值
            group: 所属群
        """
        pass

    def __mul__(self, other: GroupElement) -> GroupElement:
        """群运算"""
        pass

    def __pow__(self, n: int) -> GroupElement:
        """元素的n次幂"""
        pass

    def inverse(self) -> GroupElement:
        """返回逆元"""
        pass

    def order(self) -> int:
        """返回元素的阶"""
        pass
```

### 函数

#### `cyclic_group(n: int) -> FiniteGroup`

创建n阶循环群。

```python
def cyclic_group(n: int) -> FiniteGroup:
    """
    创建n阶循环群Z_n。

    参数:
        n: 群的阶，必须为正整数

    返回:
        FiniteGroup: n阶循环群

    异常:
        ValueError: 如果n <= 0

    示例:
        >>> G = cyclic_group(6)
        >>> G.order()
        6
    """
    pass
```

#### `symmetric_group(n: int) -> FiniteGroup`

创建n阶对称群。

```python
def symmetric_group(n: int) -> FiniteGroup:
    """
    创建n阶对称群S_n。

    参数:
        n: 群的阶，必须为正整数

    返回:
        FiniteGroup: n阶对称群

    异常:
        ValueError: 如果n <= 0

    示例:
        >>> S3 = symmetric_group(3)
        >>> S3.order()
        6
    """
    pass
```

#### `find_all_subgroups(group: FiniteGroup) -> List[FiniteGroup]`

查找群的所有子群。

```python
def find_all_subgroups(group: FiniteGroup) -> List[FiniteGroup]:
    """
    查找群的所有子群。

    参数:
        group: 要查找子群的群

    返回:
        List[FiniteGroup]: 所有子群的列表

    示例:
        >>> G = cyclic_group(12)
        >>> subgroups = find_all_subgroups(G)
        >>> len(subgroups)
        6
    """
    pass
```

#### `is_subgroup(H: FiniteGroup, G: FiniteGroup) -> bool`

判断H是否为G的子群。

```python
def is_subgroup(H: FiniteGroup, G: FiniteGroup) -> bool:
    """
    判断H是否为G的子群。

    参数:
        H: 候选子群
        G: 父群

    返回:
        bool: 如果H是G的子群返回True，否则返回False

    示例:
        >>> G = cyclic_group(12)
        >>> H = cyclic_group(6)
        >>> is_subgroup(H, G)
        False  # H不是G的子群（不同群）
    """
    pass
```

#### `is_normal(H: FiniteGroup, G: FiniteGroup) -> bool`

判断H是否为G的正规子群。

```python
def is_normal(H: FiniteGroup, G: FiniteGroup) -> bool:
    """
    判断H是否为G的正规子群。

    参数:
        H: 候选正规子群
        G: 父群

    返回:
        bool: 如果H是G的正规子群返回True，否则返回False
    """
    pass
```

#### `conjugacy_classes(group: FiniteGroup) -> List[List[GroupElement]]`

计算群的共轭类。

```python
def conjugacy_classes(group: FiniteGroup) -> List[List[GroupElement]]:
    """
    计算群的所有共轭类。

    参数:
        group: 要计算共轭群的群

    返回:
        List[List[GroupElement]]: 共轭类列表，每个共轭类是一个元素列表

    示例:
        >>> S4 = symmetric_group(4)
        >>> classes = conjugacy_classes(S4)
        >>> len(classes)
        5
    """
    pass
```

## 环论API

### 类

#### `Ring`

环类。

```python
class Ring:
    """环类"""

    def __init__(self, elements: List[RingElement], add_op: Callable, mul_op: Callable):
        """
        初始化环。

        参数:
            elements: 环元素列表
            add_op: 加法运算
            mul_op: 乘法运算
        """
        pass

    def order(self) -> int:
        """返回环的阶"""
        pass

    def zero(self) -> RingElement:
        """返回零元"""
        pass

    def one(self) -> RingElement:
        """返回单位元（如果存在）"""
        pass
```

#### `IntegerModRing`

整数模n环类。

```python
class IntegerModRing(Ring):
    """整数模n环Z/nZ"""

    def __init__(self, n: int):
        """
        初始化整数模n环。

        参数:
            n: 模数，必须为正整数

        异常:
            ValueError: 如果n <= 0
        """
        pass
```

#### `RingElement`

环元素类。

```python
class RingElement:
    """环元素类"""

    def __init__(self, value, ring: Ring):
        """
        初始化环元素。

        参数:
            value: 元素值
            ring: 所属环
        """
        pass

    def __add__(self, other: RingElement) -> RingElement:
        """环加法"""
        pass

    def __mul__(self, other: RingElement) -> RingElement:
        """环乘法"""
        pass

    def __neg__(self) -> RingElement:
        """加法逆元"""
        pass
```

### 函数

#### `find_all_ideals(ring: Ring) -> List[Ideal]`

查找环的所有理想。

```python
def find_all_ideals(ring: Ring) -> List[Ideal]:
    """
    查找环的所有理想。

    参数:
        ring: 要查找理想的环

    返回:
        List[Ideal]: 所有理想的列表
    """
    pass
```

#### `generate_ideal(generators: List[RingElement], ring: Ring) -> Ideal`

生成理想。

```python
def generate_ideal(generators: List[RingElement], ring: Ring) -> Ideal:
    """
    由生成元生成理想。

    参数:
        generators: 生成元列表
        ring: 所属环

    返回:
        Ideal: 生成的理想
    """
    pass
```

#### `is_ideal(I: Ideal, R: Ring) -> bool`

判断I是否为R的理想。

```python
def is_ideal(I: Ideal, R: Ring) -> bool:
    """
    判断I是否为R的理想。

    参数:
        I: 候选理想
        R: 父环

    返回:
        bool: 如果I是R的理想返回True，否则返回False
    """
    pass
```

## 域论API

### 类

#### `Field`

域类（抽象基类）。

```python
class Field(ABC):
    """域类（抽象基类）"""

    @abstractmethod
    def order(self) -> int:
        """返回域的阶"""
        pass

    @abstractmethod
    def characteristic(self) -> int:
        """返回域的特征"""
        pass
```

#### `FiniteField`

有限域类。

```python
class FiniteField(Field):
    """有限域类"""

    def __init__(self, p: int, n: int = 1):
        """
        初始化有限域GF(p^n)。

        参数:
            p: 素数
            n: 扩张次数，默认为1

        异常:
            ValueError: 如果p不是素数或n < 1
        """
        pass

    def order(self) -> int:
        """返回域的阶p^n"""
        pass

    def characteristic(self) -> int:
        """返回域的特征p"""
        pass
```

### 函数

#### `find_primitive_element(field: FiniteField) -> FieldElement`

查找域的本原元。

```python
def find_primitive_element(field: FiniteField) -> FieldElement:
    """
    查找有限域的本原元。

    参数:
        field: 有限域

    返回:
        FieldElement: 本原元
    """
    pass
```

#### `galois_group(E: FiniteField, F: FiniteField) -> FiniteGroup`

计算伽罗瓦群。

```python
def galois_group(E: FiniteField, F: FiniteField) -> FiniteGroup:
    """
    计算域扩张E/F的伽罗瓦群。

    参数:
        E: 扩张域
        F: 基域

    返回:
        FiniteGroup: 伽罗瓦群Gal(E/F)

    异常:
        ValueError: 如果E不是F的扩张
    """
    pass
```

## 模论API

### 类

#### `Module`

模类。

```python
class Module:
    """模类"""

    def __init__(self, elements: List[ModuleElement], ring: Ring):
        """
        初始化模。

        参数:
            elements: 模元素列表
            ring: 系数环
        """
        pass

    def rank(self) -> int:
        """返回模的秩"""
        pass
```

#### `FreeModule`

自由模类。

```python
class FreeModule(Module):
    """自由模类"""

    def __init__(self, rank: int, ring: Ring):
        """
        初始化自由模。

        参数:
            rank: 模的秩
            ring: 系数环
        """
        pass
```

### 函数

#### `free_module(rank: int, ring: Ring) -> FreeModule`

创建自由模。

```python
def free_module(rank: int, ring: Ring) -> FreeModule:
    """
    创建指定秩的自由模。

    参数:
        rank: 模的秩
        ring: 系数环

    返回:
        FreeModule: 自由模
    """
    pass
```

#### `tensor_product_of_modules(M: Module, N: Module) -> Module`

计算模的张量积。

```python
def tensor_product_of_modules(M: Module, N: Module) -> Module:
    """
    计算两个模的张量积M ⊗ N。

    参数:
        M: 第一个模
        N: 第二个模

    返回:
        Module: 张量积M ⊗ N
    """
    pass
```

## 表示论API

### 类

#### `GroupRepresentation`

群表示类。

```python
class GroupRepresentation:
    """群表示类"""

    def __init__(self, group: FiniteGroup, matrices: Dict[GroupElement, np.ndarray]):
        """
        初始化群表示。

        参数:
            group: 被表示的群
            matrices: 群元素到矩阵的映射
        """
        pass

    def dimension(self) -> int:
        """返回表示的维数"""
        pass

    def character(self) -> Dict[GroupElement, complex]:
        """计算特征标"""
        pass

    def is_irreducible(self) -> bool:
        """判断是否为不可约表示"""
        pass
```

### 函数

#### `character_table(group: FiniteGroup) -> pd.DataFrame`

计算群的特征标表。

```python
def character_table(group: FiniteGroup) -> pd.DataFrame:
    """
    计算群的特征标表。

    参数:
        group: 要计算特征标表的群

    返回:
        pd.DataFrame: 特征标表
    """
    pass
```

#### `trivial_representation(group: FiniteGroup) -> GroupRepresentation`

创建平凡表示。

```python
def trivial_representation(group: FiniteGroup) -> GroupRepresentation:
    """
    创建群的平凡表示。

    参数:
        group: 群

    返回:
        GroupRepresentation: 平凡表示
    """
    pass
```

## 李代数API

### 类

#### `LieAlgebra`

李代数类（抽象基类）。

```python
class LieAlgebra(ABC):
    """李代数类（抽象基类）"""

    @abstractmethod
    def dimension(self) -> int:
        """返回李代数的维数"""
        pass

    @abstractmethod
    def lie_bracket(self, x, y):
        """计算李括号[x, y]"""
        pass
```

#### `MatrixLieAlgebra`

矩阵李代数类。

```python
class MatrixLieAlgebra(LieAlgebra):
    """矩阵李代数类"""

    def __init__(self, basis: List[np.ndarray], bracket_func: Callable):
        """
        初始化矩阵李代数。

        参数:
            basis: 基矩阵列表
            bracket_func: 李括号函数
        """
        pass
```

### 函数

#### `killing_form(x, y, lie_algebra: LieAlgebra) -> float`

计算Killing形式。

```python
def killing_form(x, y, lie_algebra: LieAlgebra) -> float:
    """
    计算Killing形式κ(x, y)。

    参数:
        x: 第一个元素
        y: 第二个元素
        lie_algebra: 李代数

    返回:
        float: Killing形式的值
    """
    pass
```

#### `root_system(lie_algebra: LieAlgebra) -> List[np.ndarray]`

计算根系。

```python
def root_system(lie_algebra: LieAlgebra) -> List[np.ndarray]:
    """
    计算半单李代数的根系。

    参数:
        lie_algebra: 半单李代数

    返回:
        List[np.ndarray]: 根系列表

    异常:
        ValueError: 如果李代数不是半单的
    """
    pass
```

## 范畴论API

### 类

#### `Category`

范畴类。

```python
class Category:
    """范畴类"""

    def __init__(self, objects: List, morphisms: Dict, composition: Callable):
        """
        初始化范畴。

        参数:
            objects: 对象列表
            morphisms: 态射字典
            composition: 复合函数
        """
        pass
```

#### `Functor`

函子类。

```python
class Functor:
    """函子类"""

    def __init__(self, source: Category, target: Category,
                 object_map: Callable, morphism_map: Callable):
        """
        初始化函子。

        参数:
            source: 源范畴
            target: 目标范畴
            object_map: 对象映射函数
            morphism_map: 态射映射函数
        """
        pass
```

### 函数

#### `product(A, B, category: Category) -> object`

计算对象的积。

```python
def product(A, B, category: Category) -> object:
    """
    计算范畴中两个对象的积。

    参数:
        A: 第一个对象
        B: 第二个对象
        category: 所属范畴

    返回:
        object: 积对象
    """
    pass
```

## 线性代数API

### 函数

#### `lu_decomposition(A: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]`

LU分解。

```python
def lu_decomposition(A: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    计算矩阵的LU分解A = P * L * U。

    参数:
        A: 输入矩阵

    返回:
        Tuple[np.ndarray, np.ndarray, np.ndarray]: (L, U, P)三元组

    异常:
        ValueError: 如果矩阵不可分解
    """
    pass
```

#### `qr_decomposition(A: np.ndarray) -> Tuple[np.ndarray, np.ndarray]`

QR分解。

```python
def qr_decomposition(A: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """
    计算矩阵的QR分解A = Q * R。

    参数:
        A: 输入矩阵

    返回:
        Tuple[np.ndarray, np.ndarray]: (Q, R)二元组
    """
    pass
```

#### `eigenvalues(A: np.ndarray) -> np.ndarray`

计算特征值。

```python
def eigenvalues(A: np.ndarray) -> np.ndarray:
    """
    计算矩阵的特征值。

    参数:
        A: 输入矩阵

    返回:
        np.ndarray: 特征值数组
    """
    pass
```

## 综合工具API

### 类

#### `UniversalAlgebraicCalculator`

通用代数结构计算器。

```python
class UniversalAlgebraicCalculator:
    """通用代数结构计算器"""

    def __init__(self):
        """初始化计算器"""
        pass

    def add_structure(self, name: str, structure):
        """
        添加代数结构。

        参数:
            name: 结构名称
            structure: 代数结构对象
        """
        pass

    def analyze_all(self):
        """分析所有添加的结构"""
        pass

    def compare_structures(self, name1: str, name2: str) -> Dict:
        """
        比较两个结构。

        参数:
            name1: 第一个结构名称
            name2: 第二个结构名称

        返回:
            Dict: 比较结果
        """
        pass
```

#### `StructureValidator`

结构验证器。

```python
class StructureValidator:
    """结构验证器"""

    def validate_group(self, group: FiniteGroup) -> Dict[str, bool]:
        """
        验证群公理。

        参数:
            group: 要验证的群

        返回:
            Dict[str, bool]: 公理验证结果
        """
        pass

    def validate_ring(self, ring: Ring) -> Dict[str, bool]:
        """
        验证环公理。

        参数:
            ring: 要验证的环

        返回:
            Dict[str, bool]: 公理验证结果
        """
        pass
```

## 类型提示

### 常用类型

```python
from typing import List, Dict, Tuple, Callable, Optional, Union
import numpy as np

# 群论类型
GroupElement = ...
FiniteGroup = ...

# 环论类型
RingElement = ...
Ring = ...

# 域论类型
FieldElement = ...
Field = ...
FiniteField = ...

# 模论类型
ModuleElement = ...
Module = ...

# 表示论类型
GroupRepresentation = ...

# 李代数类型
LieAlgebra = ...

# 范畴论类型
Category = ...
Functor = ...
```

## 异常类

### `StructureError`

结构相关错误。

```python
class StructureError(Exception):
    """结构相关错误"""
    pass
```

### `ValidationError`

验证错误。

```python
class ValidationError(Exception):
    """验证错误"""
    pass
```

## 资源链接

- **[完整指南](00-Python实现-代数结构完整指南.md)**: 完整的用户指南
- **[快速参考](00-Python实现-代数结构快速参考.md)**: 常用函数速查表
- **[快速入门教程](00-Python实现-代数结构快速入门教程.md)**: 快速入门教程

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
