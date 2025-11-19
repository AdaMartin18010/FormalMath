# 代数结构Python实现术语表

## 概述

本文档提供代数结构Python实现体系中使用的数学术语和编程术语的详细解释，帮助用户理解相关概念。

## 群论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 群 | Group | 具有二元运算的集合，满足封闭性、结合律、单位元、逆元 | `FiniteGroup` |
| 子群 | Subgroup | 群的子集，本身也是群 | `is_subgroup(H, G)` |
| 正规子群 | Normal subgroup | 对共轭封闭的子群 | `is_normal(H, G)` |
| 商群 | Quotient group | 群模正规子群的商集 | `quotient_group(G, N)` |
| 陪集 | Coset | 子群的左陪集或右陪集 | `left_coset(g, H)` |
| 阶 | Order | 群的元素个数或元素的阶 | `G.order()`, `order_of_element(g)` |
| 生成元 | Generator | 能生成整个群的元素 | `generators(G)` |
| 循环群 | Cyclic group | 由单个元素生成的群 | `cyclic_group(n)` |
| 交换群 | Abelian group | 运算满足交换律的群 | `is_abelian(G)` |

### 同态与同构

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 同态 | Homomorphism | 保持群运算的映射 | `is_homomorphism(phi, G1, G2)` |
| 同构 | Isomorphism | 双射同态 | `is_isomorphic(G1, G2)` |
| 自同构 | Automorphism | 群到自身的同构 | `automorphism_group(G)` |
| 核 | Kernel | 同态的核 | `kernel(phi)` |
| 像 | Image | 同态的像 | `image(phi)` |

### 特殊群类

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 对称群 | Symmetric group | n个元素的置换群 | `symmetric_group(n)` |
| 交错群 | Alternating group | 偶置换群 | `alternating_group(n)` |
| 二面体群 | Dihedral group | 正n边形的对称群 | `dihedral_group(n)` |
| 共轭类 | Conjugacy class | 共轭元素形成的等价类 | `conjugacy_classes(G)` |
| 中心 | Center | 与所有元素交换的元素集合 | `center(G)` |

## 环论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 环 | Ring | 具有加法和乘法的代数结构 | `Ring` |
| 交换环 | Commutative ring | 乘法满足交换律的环 | `is_commutative(R)` |
| 整环 | Integral domain | 无零因子的交换环 | `is_integral_domain(R)` |
| 域 | Field | 非零元有乘法逆元的交换环 | `is_field(R)` |
| 理想 | Ideal | 环的子集，对加法和乘法封闭 | `is_ideal(I, R)` |
| 素理想 | Prime ideal | 满足素性条件的理想 | `is_prime_ideal(I, R)` |
| 极大理想 | Maximal ideal | 不被其他真理想包含的理想 | `is_maximal_ideal(I, R)` |
| 商环 | Quotient ring | 环模理想的商集 | `quotient_ring(R, I)` |

### 特殊环类

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 多项式环 | Polynomial ring | 多项式的环 | `PolynomialRing(R, "x")` |
| 矩阵环 | Matrix ring | 矩阵的环 | `MatrixRing(n, R)` |
| 整数模n环 | Integer mod ring | Z/nZ | `IntegerModRing(n)` |

## 域论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 域 | Field | 非零元有乘法逆元的交换环 | `Field` |
| 有限域 | Finite field | 元素个数有限的域 | `FiniteField(p, n)` |
| 域扩张 | Field extension | 包含子域的域 | `field_extension(F, alpha)` |
| 扩张次数 | Extension degree | 域扩张的维数 | `E.degree_over(F)` |
| 代数扩张 | Algebraic extension | 所有元素都是代数的扩张 | `is_algebraic_extension(E, F)` |
| 超越扩张 | Transcendental extension | 包含超越元素的扩张 | `is_transcendental_extension(E, F)` |
| 本原元 | Primitive element | 能生成整个域扩张的元素 | `find_primitive_element(F)` |
| 极小多项式 | Minimal polynomial | 代数元素的最小次数多项式 | `minimal_polynomial(alpha, F)` |

### 伽罗瓦理论

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 伽罗瓦群 | Galois group | 域扩张的自同构群 | `galois_group(E, F)` |
| 伽罗瓦扩张 | Galois extension | 正规且可分的扩张 | `is_galois_extension(E, F)` |
| 伽罗瓦对应 | Galois correspondence | 子群与中间域的对应 | `galois_correspondence(E, F)` |
| 可分扩张 | Separable extension | 所有元素都是可分的 | `is_separable_extension(E, F)` |
| 正规扩张 | Normal extension | 分裂域 | `is_normal_extension(E, F)` |

## 模论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 模 | Module | 环上的模 | `Module` |
| 子模 | Submodule | 模的子集，本身也是模 | `is_submodule(N, M)` |
| 自由模 | Free module | 有基的模 | `free_module(rank, R)` |
| 投射模 | Projective module | 满足投射性质的模 | `is_projective(M)` |
| 内射模 | Injective module | 满足内射性质的模 | `is_injective(M)` |
| 商模 | Quotient module | 模模子模的商集 | `quotient_module(M, N)` |
| 张量积 | Tensor product | 模的张量积 | `tensor_product_of_modules(M, N)` |
| 直和 | Direct sum | 模的直和 | `direct_sum_of_modules(M, N)` |
| 直积 | Direct product | 模的直积 | `direct_product_of_modules(M, N)` |

### 同调代数

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 链复形 | Chain complex | 模的序列和边界映射 | `ChainComplex` |
| 同调群 | Homology group | 链复形的同调 | `homology_group(complex, n)` |
| 上同调群 | Cohomology group | 上链复形的上同调 | `cohomology_group(complex, n)` |

## 李代数术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 李代数 | Lie algebra | 具有李括号的向量空间 | `LieAlgebra` |
| 李括号 | Lie bracket | 反对称双线性运算 | `lie_bracket(x, y, L)` |
| 雅可比恒等式 | Jacobi identity | 李括号满足的恒等式 | `verify_jacobi_identity(L)` |
| Killing形式 | Killing form | 李代数的双线性形式 | `killing_form(x, y, L)` |
| 理想 | Ideal | 对李括号封闭的子空间 | `is_ideal(I, L)` |
| 中心 | Center | 与所有元素交换的元素集合 | `center(L)` |
| 导出代数 | Derived algebra | 由所有换位子生成的子代数 | `derived_algebra(L)` |

### 特殊李代数

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 半单李代数 | Semisimple Lie algebra | 没有非零可解理想的李代数 | `is_semisimple(L)` |
| 单李代数 | Simple Lie algebra | 没有非平凡理想的李代数 | `is_simple(L)` |
| 可解李代数 | Solvable Lie algebra | 导出列终止于零的李代数 | `is_solvable(L)` |
| 幂零李代数 | Nilpotent Lie algebra | 下中心列终止于零的李代数 | `is_nilpotent(L)` |
| 根系 | Root system | 半单李代数的根系 | `root_system(L)` |
| 权格 | Weight lattice | 表示的权格 | `weight_lattice(rho)` |

## 表示论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 表示 | Representation | 群到线性变换群的同态 | `GroupRepresentation` |
| 特征标 | Character | 表示的迹函数 | `rho.character()` |
| 不可约表示 | Irreducible representation | 没有非平凡不变子空间的表示 | `is_irreducible(rho)` |
| 特征标表 | Character table | 所有不可约表示的特征标表 | `character_table(G)` |
| 平凡表示 | Trivial representation | 所有元素映射到恒等变换 | `trivial_representation(G)` |
| 正则表示 | Regular representation | 群在自身上的左正则作用 | `regular_representation(G)` |
| 诱导表示 | Induced representation | 从子群诱导的表示 | `induced_representation(H, rho, G)` |
| 限制表示 | Restricted representation | 限制到子群的表示 | `restricted_representation(rho, H)` |

### 表示运算

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 直和 | Direct sum | 表示的直和 | `rho1.direct_sum(rho2)` |
| 张量积 | Tensor product | 表示的张量积 | `rho1.tensor_product(rho2)` |
| 对偶表示 | Dual representation | 表示的对偶 | `rho.dual()` |

## 范畴论术语

### 基础概念

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 范畴 | Category | 对象和态射的集合 | `Category` |
| 态射 | Morphism | 对象之间的映射 | `Morphism` |
| 函子 | Functor | 范畴之间的映射 | `Functor` |
| 自然变换 | Natural transformation | 函子之间的变换 | `NaturalTransformation` |
| 极限 | Limit | 范畴的极限 | `limit(diagram, C)` |
| 余极限 | Colimit | 范畴的余极限 | `colimit(diagram, C)` |
| 积 | Product | 对象的积 | `product(A, B, C)` |
| 余积 | Coproduct | 对象的余积 | `coproduct(A, B, C)` |
| 等化子 | Equalizer | 态射的等化子 | `equalizer(f, g, C)` |
| 余等化子 | Coequalizer | 态射的余等化子 | `coequalizer(f, g, C)` |
| 伴随 | Adjoint | 函子的伴随 | `is_adjoint(F, G)` |

## 线性代数术语

### 矩阵运算

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| LU分解 | LU decomposition | 矩阵的LU分解 | `lu_decomposition(A)` |
| QR分解 | QR decomposition | 矩阵的QR分解 | `qr_decomposition(A)` |
| SVD分解 | SVD decomposition | 奇异值分解 | `svd_decomposition(A)` |
| 特征值 | Eigenvalue | 矩阵的特征值 | `eigenvalues(A)` |
| 特征向量 | Eigenvector | 矩阵的特征向量 | `eigenvectors(A)` |
| 条件数 | Condition number | 矩阵的条件数 | `condition_number(A)` |

## 编程术语

### 设计模式

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 工厂模式 | Factory pattern | 创建对象的模式 | `AlgebraicStructureFactory` |
| 策略模式 | Strategy pattern | 算法选择的模式 | `OperationStrategy` |
| 装饰器模式 | Decorator pattern | 功能扩展的模式 | `@safe_operation` |

### 性能优化

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| 缓存 | Cache | 存储计算结果 | `@lru_cache` |
| 预计算 | Precomputation | 提前计算常用值 | `precompute_structure_constants` |
| 向量化 | Vectorization | 使用数组运算 | `numpy.array` |
| 并行计算 | Parallel computation | 多进程计算 | `Parallel(n_jobs=4)` |

## 数学符号对照

### 常用符号

| 符号 | 含义 | 英文 | 代码表示 |
|------|------|------|----------|
| $G$ | 群 | Group | `G` |
| $H \leq G$ | H是G的子群 | H is a subgroup of G | `is_subgroup(H, G)` |
| $H \triangleleft G$ | H是G的正规子群 | H is a normal subgroup of G | `is_normal(H, G)` |
| $G/H$ | 商群 | Quotient group | `quotient_group(G, H)` |
| $\|G\|$ | 群的阶 | Order of group | `G.order()` |
| $Z(G)$ | 中心 | Center | `center(G)` |
| $[G:H]$ | 指数 | Index | `index(H, G)` |
| $\phi: G \to H$ | 同态 | Homomorphism | `phi: G -> H` |
| $\ker(\phi)$ | 核 | Kernel | `kernel(phi)` |
| $\text{im}(\phi)$ | 像 | Image | `image(phi)` |
| $R$ | 环 | Ring | `R` |
| $I \triangleleft R$ | 理想 | Ideal | `is_ideal(I, R)` |
| $R/I$ | 商环 | Quotient ring | `quotient_ring(R, I)` |
| $F$ | 域 | Field | `F` |
| $E/F$ | 域扩张 | Field extension | `field_extension(E, F)` |
| $\text{Gal}(E/F)$ | 伽罗瓦群 | Galois group | `galois_group(E, F)` |
| $M$ | 模 | Module | `M` |
| $M \otimes N$ | 张量积 | Tensor product | `tensor_product(M, N)` |
| $\mathfrak{g}$ | 李代数 | Lie algebra | `L` |
| $[x, y]$ | 李括号 | Lie bracket | `lie_bracket(x, y)` |
| $\rho: G \to \text{GL}(V)$ | 表示 | Representation | `GroupRepresentation` |
| $\chi$ | 特征标 | Character | `chi` |

## 代码术语

### 类和方法

| 术语 | 定义 | 示例 |
|------|------|------|
| 类 | 对象的模板 | `class FiniteGroup` |
| 方法 | 类的函数 | `def order(self)` |
| 属性 | 类的变量 | `self.elements` |
| 继承 | 从基类派生 | `class Ring(AlgebraicStructure)` |
| 多态 | 同一接口不同实现 | `operation()` 在不同类中的实现 |
| 抽象方法 | 必须实现的方法 | `@abstractmethod` |

### 函数和装饰器

| 术语 | 定义 | 示例 |
|------|------|------|
| 装饰器 | 修改函数行为的函数 | `@lru_cache`, `@safe_operation` |
| 生成器 | 返回迭代器的函数 | `def elements(self): yield ...` |
| 类型提示 | 函数参数和返回值的类型 | `def f(x: int) -> str` |
| 文档字符串 | 函数的文档 | `"""函数说明"""` |

## 算法术语

### 复杂度

| 术语 | 定义 | 示例 |
|------|------|------|
| 时间复杂度 | 算法执行时间 | $O(n^2)$, $O(n \log n)$ |
| 空间复杂度 | 算法内存使用 | $O(n)$, $O(1)$ |
| 最优算法 | 复杂度最低的算法 | 快速排序 $O(n \log n)$ |

### 算法类型

| 术语 | 定义 | 示例 |
|------|------|------|
| 递归算法 | 调用自身的算法 | 子群查找 |
| 迭代算法 | 循环执行的算法 | 幂迭代法 |
| 分治算法 | 分而治之的算法 | 快速排序 |
| 动态规划 | 存储中间结果的算法 | 最长公共子序列 |

## 应用术语

### 密码学

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| RSA | RSA | 公钥密码系统 | `RSACryptosystem` |
| Diffie-Hellman | Diffie-Hellman | 密钥交换协议 | `DiffieHellmanKeyExchange` |
| 椭圆曲线 | Elliptic curve | 椭圆曲线密码学 | `EllipticCurveRing` |

### 编码理论

| 术语 | 英文 | 定义 | 代码示例 |
|------|------|------|----------|
| Reed-Solomon码 | Reed-Solomon code | 纠错码 | `ReedSolomonCode` |
| 循环码 | Cyclic code | 循环码 | `CyclicCode` |
| 汉明距离 | Hamming distance | 码字之间的距离 | `hamming_distance(c1, c2)` |

## 资源链接

- **[完整指南](00-Python实现-代数结构完整指南.md)**: 完整的用户指南
- **[快速参考](00-Python实现-代数结构快速参考.md)**: 常用函数速查表
- **[常见问题FAQ](00-Python实现-代数结构常见问题FAQ.md)**: 常见问题解答

---

**版本**: 1.0
**最后更新**: 2025年1月
**维护者**: FormalMath项目组
