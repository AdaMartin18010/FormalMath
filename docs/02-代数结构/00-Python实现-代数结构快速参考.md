# 代数结构Python实现快速参考卡片

## 概述

本文档提供代数结构Python实现体系的快速参考，包括常用函数、类、方法和示例代码的速查表。

## 1. 群论快速参考

### 1.1 基础类

```python
from group_theory import GroupElement, FiniteGroup

# 创建群元素
g = GroupElement(1, "g")
h = GroupElement(2, "h")

# 创建有限群
G = FiniteGroup([g, h], lambda a, b: GroupElement(a.value + b.value, f"{a.name}*{b.name}"))
```

### 1.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `is_subgroup(H, G)` | 判断是否为子群 | `is_subgroup(H, G)` |
| `find_all_subgroups(G)` | 查找所有子群 | `subgroups = find_all_subgroups(G)` |
| `conjugacy_classes(G)` | 计算共轭类 | `classes = conjugacy_classes(G)` |
| `center(G)` | 计算中心 | `Z = center(G)` |
| `is_normal(H, G)` | 判断是否为正规子群 | `is_normal(H, G)` |
| `quotient_group(G, N)` | 构造商群 | `Q = quotient_group(G, N)` |
| `is_isomorphic(G1, G2)` | 判断是否同构 | `is_isomorphic(G1, G2)` |
| `order_of_element(g, G)` | 计算元素阶 | `n = order_of_element(g, G)` |
| `is_abelian(G)` | 判断是否为交换群 | `is_abelian(G)` |
| `is_cyclic(G)` | 判断是否为循环群 | `is_cyclic(G)` |

### 1.3 群表示

```python
from group_theory import GroupRepresentation

# 创建群表示
rho = GroupRepresentation(G, matrices)

# 特征标
chi = rho.character()

# 不可约分解
irreps = rho.decompose_irreducibles()
```

## 2. 环论快速参考

### 2.1 基础类

```python
from ring_theory import RingElement, Ring

# 创建环元素
a = RingElement(3, "a")
b = RingElement(5, "b")

# 创建环
R = Ring([a, b], add_op, mul_op)
```

### 2.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `is_ideal(I, R)` | 判断是否为理想 | `is_ideal(I, R)` |
| `generate_ideal(S, R)` | 生成理想 | `I = generate_ideal(S, R)` |
| `is_prime_ideal(I, R)` | 判断是否为素理想 | `is_prime_ideal(I, R)` |
| `find_all_ideals(R)` | 查找所有理想 | `ideals = find_all_ideals(R)` |
| `quotient_ring(R, I)` | 构造商环 | `Q = quotient_ring(R, I)` |
| `is_integral_domain(R)` | 判断是否为整环 | `is_integral_domain(R)` |
| `is_field(R)` | 判断是否为域 | `is_field(R)` |
| `units(R)` | 计算单位群 | `U = units(R)` |

### 2.3 多项式环

```python
from ring_theory import PolynomialRing

# 创建多项式环
R = PolynomialRing(base_ring, variable="x")

# 创建多项式
p = R([1, 2, 3])  # 1 + 2x + 3x^2

# 多项式运算
q = p + p
r = p * p
```

## 3. 域论快速参考

### 3.1 基础类

```python
from field_theory import Field, FiniteField, RationalField

# 创建有理数域
Q = RationalField()

# 创建有限域
F = FiniteField(7)  # GF(7)
```

### 3.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `field_extension(F, alpha)` | 域扩张 | `E = field_extension(F, alpha)` |
| `galois_group(E, F)` | 伽罗瓦群 | `G = galois_group(E, F)` |
| `is_galois_extension(E, F)` | 判断是否为伽罗瓦扩张 | `is_galois_extension(E, F)` |
| `primitive_element(F)` | 本原元 | `alpha = primitive_element(F)` |
| `minimal_polynomial(alpha, F)` | 极小多项式 | `p = minimal_polynomial(alpha, F)` |
| `subfields(F)` | 所有子域 | `subs = subfields(F)` |

### 3.3 有限域

```python
from field_theory import FiniteField

# 创建有限域
F = FiniteField(7)  # GF(7)
F2 = FiniteField(2, 3)  # GF(2^3)

# 域元素运算
a = F(3)
b = F(5)
c = a + b
d = a * b
e = a ** (-1)  # 逆元
```

## 4. 模论快速参考

### 4.1 基础类

```python
from module_theory import ModuleElement, Module

# 创建模元素
m = ModuleElement([1, 2], "m")
n = ModuleElement([3, 4], "n")

# 创建模
M = Module([m, n], scalar_mult, add_op)
```

### 4.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `is_submodule(N, M)` | 判断是否为子模 | `is_submodule(N, M)` |
| `free_module(rank, ring)` | 自由模 | `M = free_module(3, R)` |
| `tensor_product(M, N)` | 张量积 | `T = tensor_product(M, N)` |
| `direct_sum(M, N)` | 直和 | `D = direct_sum(M, N)` |
| `quotient_module(M, N)` | 商模 | `Q = quotient_module(M, N)` |
| `is_projective(M)` | 判断是否为投射模 | `is_projective(M)` |
| `is_injective(M)` | 判断是否为内射模 | `is_injective(M)` |

## 5. 李代数快速参考

### 5.1 基础类

```python
from lie_algebra import LieAlgebra, MatrixLieAlgebra

# 创建矩阵李代数
L = MatrixLieAlgebra(matrices, bracket_op)
```

### 5.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `lie_bracket(x, y, L)` | 李括号 | `[x, y] = lie_bracket(x, y, L)` |
| `killing_form(x, y, L)` | Killing形式 | `k = killing_form(x, y, L)` |
| `is_ideal(I, L)` | 判断是否为理想 | `is_ideal(I, L)` |
| `center(L)` | 中心 | `Z = center(L)` |
| `derived_algebra(L)` | 导出代数 | `L' = derived_algebra(L)` |
| `is_semisimple(L)` | 判断是否为半单 | `is_semisimple(L)` |
| `root_system(L)` | 根系 | `roots = root_system(L)` |

### 5.3 经典李代数

```python
from lie_algebra import sl, so, sp

# 特殊线性李代数
L1 = sl(3)

# 正交李代数
L2 = so(4)

# 辛李代数
L3 = sp(4)
```

## 6. 表示论快速参考

### 6.1 群表示

```python
from representation_theory import GroupRepresentation

# 创建群表示
rho = GroupRepresentation(G, matrices)

# 特征标
chi = rho.character()

# 不可约分解
irreps = rho.decompose_irreducibles()

# 张量积
rho_tensor = rho1.tensor_product(rho2)
```

### 6.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `trivial_representation(G)` | 平凡表示 | `triv = trivial_representation(G)` |
| `regular_representation(G)` | 正则表示 | `reg = regular_representation(G)` |
| `permutation_representation(G, X)` | 置换表示 | `perm = permutation_representation(G, X)` |
| `is_irreducible(rho)` | 判断是否不可约 | `is_irreducible(rho)` |
| `character_table(G)` | 特征标表 | `table = character_table(G)` |
| `induced_representation(H, rho, G)` | 诱导表示 | `ind = induced_representation(H, rho, G)` |
| `restricted_representation(rho, H)` | 限制表示 | `res = restricted_representation(rho, H)` |

## 7. 范畴论快速参考

### 7.1 基础类

```python
from category_theory import Category, Functor, NaturalTransformation

# 创建范畴
C = Category(objects, morphisms, composition)

# 创建函子
F = Functor(C, D, object_map, morphism_map)

# 自然变换
eta = NaturalTransformation(F, G, components)
```

### 7.2 常用函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `product(A, B, C)` | 积 | `P = product(A, B, C)` |
| `coproduct(A, B, C)` | 余积 | `CP = coproduct(A, B, C)` |
| `equalizer(f, g, C)` | 等化子 | `E = equalizer(f, g, C)` |
| `coequalizer(f, g, C)` | 余等化子 | `CE = coequalizer(f, g, C)` |
| `is_adjoint(F, G)` | 判断是否伴随 | `is_adjoint(F, G)` |
| `left_adjoint(F)` | 左伴随 | `L = left_adjoint(F)` |
| `right_adjoint(F)` | 右伴随 | `R = right_adjoint(F)` |

## 8. 线性代数快速参考

### 8.1 矩阵分解

```python
import numpy as np
from linear_algebra import lu_decomposition, qr_decomposition, svd_decomposition

# LU分解
L, U, P = lu_decomposition(A)

# QR分解
Q, R = qr_decomposition(A)

# SVD分解
U, s, Vt = svd_decomposition(A)
```

### 8.2 特征值计算

```python
from linear_algebra import power_iteration, qr_algorithm

# 幂迭代法
eigenvalue, eigenvector = power_iteration(A)

# QR算法
eigenvalues, eigenvectors = qr_algorithm(A)
```

### 8.3 线性方程组

```python
from linear_algebra import solve_linear_system, jacobi_method, gauss_seidel

# 直接求解
x = solve_linear_system(A, b)

# 迭代求解
x = jacobi_method(A, b)
x = gauss_seidel(A, b)
```

## 9. 综合工具快速参考

### 9.1 统一接口

```python
from algebraic_structures import AlgebraicStructure, GroupStructure, RingStructure

# 创建代数结构
G = GroupStructure(elements, operation)

# 分析结构
from algebraic_structures import AlgebraicStructureAnalyzer

analyzer = AlgebraicStructureAnalyzer()
report = analyzer.analyze(G)
```

### 9.2 综合计算器

```python
from algebraic_structures import UniversalAlgebraicCalculator

calc = UniversalAlgebraicCalculator()

# 添加结构
calc.add_structure("G", G)
calc.add_structure("R", R)

# 分析
calc.analyze_all()

# 比较
calc.compare_structures("G", "R")
```

### 9.3 可视化

```python
from algebraic_structures import visualize_structure_relationships

# 可视化结构关系
visualize_structure_relationships(structures)
```

## 10. 常用模式

### 10.1 创建对称群

```python
from group_theory import symmetric_group

# 创建S3
S3 = symmetric_group(3)
```

### 10.2 创建循环群

```python
from group_theory import cyclic_group

# 创建Z/nZ
Zn = cyclic_group(5)
```

### 10.3 创建有限域

```python
from field_theory import FiniteField

# 创建GF(p)
Fp = FiniteField(7)

# 创建GF(p^n)
Fpn = FiniteField(2, 3)  # GF(2^3)
```

### 10.4 创建多项式环

```python
from ring_theory import PolynomialRing

# 创建Z[x]
Zx = PolynomialRing(integers, "x")

# 创建F[x]
Fx = PolynomialRing(finite_field, "x")
```

### 10.5 创建矩阵环

```python
from ring_theory import MatrixRing

# 创建M_n(R)
MnR = MatrixRing(n, base_ring)
```

## 11. 错误处理

### 11.1 常见错误

```python
# 检查结构是否满足公理
from algebraic_structures import StructureValidator

validator = StructureValidator()
if not validator.validate_group(G):
    raise ValueError("G is not a valid group")
```

### 11.2 安全操作

```python
from algebraic_structures import safe_operation

@safe_operation
def group_operation(a, b):
    return a * b
```

## 12. 性能优化

### 12.1 使用缓存

```python
from functools import lru_cache

@lru_cache(maxsize=128)
def expensive_computation(x):
    # 计算
    return result
```

### 12.2 使用NumPy

```python
import numpy as np

# 向量化运算
A = np.array([[1, 2], [3, 4]])
B = np.array([[5, 6], [7, 8]])
C = A @ B  # 矩阵乘法
```

## 13. 测试

### 13.1 单元测试

```python
import unittest

class TestGroup(unittest.TestCase):
    def test_closure(self):
        # 测试封闭性
        pass

    def test_associativity(self):
        # 测试结合律
        pass
```

### 13.2 公理验证

```python
from group_theory import verify_group_axioms

# 验证群公理
assert verify_group_axioms(G)
```

## 14. 导入语句速查

```python
# 群论
from group_theory import GroupElement, FiniteGroup, is_subgroup, conjugacy_classes

# 环论
from ring_theory import RingElement, Ring, is_ideal, quotient_ring

# 域论
from field_theory import Field, FiniteField, field_extension, galois_group

# 模论
from module_theory import ModuleElement, Module, tensor_product, direct_sum

# 李代数
from lie_algebra import LieAlgebra, MatrixLieAlgebra, lie_bracket, killing_form

# 表示论
from representation_theory import GroupRepresentation, character_table

# 范畴论
from category_theory import Category, Functor, NaturalTransformation

# 线性代数
from linear_algebra import lu_decomposition, qr_decomposition, svd_decomposition

# 综合工具
from algebraic_structures import (
    AlgebraicStructure,
    UniversalAlgebraicCalculator,
    AlgebraicStructureAnalyzer
)
```

## 15. 常用常量

```python
# 常用群
S3 = symmetric_group(3)
A4 = alternating_group(4)
D4 = dihedral_group(4)

# 常用环
Z = IntegerRing()
Zn = IntegerModRing(n)
Zx = PolynomialRing(Z, "x")

# 常用域
Q = RationalField()
Fp = FiniteField(p)
Fpn = FiniteField(p, n)
```

## 16. 快速检查清单

### 16.1 创建群

- [ ] 定义元素集合
- [ ] 定义二元运算
- [ ] 验证封闭性
- [ ] 验证结合律
- [ ] 验证单位元
- [ ] 验证逆元

### 16.2 创建环

- [ ] 定义元素集合
- [ ] 定义加法运算
- [ ] 定义乘法运算
- [ ] 验证环公理
- [ ] 验证分配律

### 16.3 创建域

- [ ] 验证是环
- [ ] 验证非零元有乘法逆元
- [ ] 验证交换性（可选）

## 17. 调试技巧

### 17.1 打印结构信息

```python
# 打印群信息
print(f"Order: {G.order()}")
print(f"Is abelian: {G.is_abelian()}")
print(f"Subgroups: {G.subgroups()}")

# 打印环信息
print(f"Characteristic: {R.characteristic()}")
print(f"Is integral domain: {R.is_integral_domain()}")
```

### 17.2 验证公理

```python
from group_theory import verify_group_axioms
from ring_theory import verify_ring_axioms

# 验证群公理
if not verify_group_axioms(G):
    print("Group axioms violated!")

# 验证环公理
if not verify_ring_axioms(R):
    print("Ring axioms violated!")
```

## 18. 性能提示

1. **使用缓存**: 对重复计算使用`@lru_cache`
2. **向量化**: 使用NumPy进行矩阵运算
3. **生成器**: 对大型结构使用生成器而非列表
4. **预计算**: 预计算结构常数、Killing矩阵等
5. **并行计算**: 对独立计算使用多进程

## 19. 常见问题

### Q: 如何判断两个群是否同构？

```python
from group_theory import is_isomorphic

if is_isomorphic(G1, G2):
    print("Groups are isomorphic")
```

### Q: 如何计算群的所有子群？

```python
from group_theory import find_all_subgroups

subgroups = find_all_subgroups(G)
```

### Q: 如何构造商环？

```python
from ring_theory import quotient_ring

Q = quotient_ring(R, I)
```

### Q: 如何计算域扩张的伽罗瓦群？

```python
from field_theory import galois_group

G = galois_group(E, F)
```

## 20. 资源链接

- **完整指南**: `00-Python实现-代数结构完整指南.md`
- **综合工具**: `00-Python实现-代数结构综合工具.md`
- **进展报告**: `00-Python实现-代数结构进展报告.md`
- **群论实现**: `群论/07-Python实现-群论算法.md`
- **环论实现**: `环论/07-Python实现-环论算法.md`
- **域论实现**: `域论/07-Python实现-域论算法.md`

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
