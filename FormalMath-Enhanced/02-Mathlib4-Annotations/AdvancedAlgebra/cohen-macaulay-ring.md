---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Cohen-Macaulay环
---
# Cohen-Macaulay环

## Mathlib4 引用

```lean
import Mathlib.RingTheory.CohenMacaulay

namespace CommutativeAlgebra

/-- Cohen-Macaulay环的定义 -/
theorem cohen_macaulay_def
    {R : Type*} [CommRing R] [IsNoetherianRing R] :
    IsCohenMacaulay R ↔ ∀ (p : PrimeSpectrum R),
      depth R p = height p := by
  -- Cohen-Macaulay：深度等于高度
  rfl

/-- Cohen-Macaulay环的维数公式 -/
theorem cohen_macaulay_dimension
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsCohenMacaulay R] (p : PrimeSpectrum R) :
    depth R p = krullDim R ⧸ p := by
  -- 深度与维数的关系
  rw [IsCohenMacaulay.depth_eq_height]
  -- 应用维数公式
  sorry

end CommutativeAlgebra
```

## 数学背景

Cohen-Macaulay环以Francis Sowerby Macaulay和Irving S. Cohen命名，是交换代数中最重要的环类之一。Macaulay在1916年研究了多项式环中的这种性质，Cohen在1946年将其推广到一般诺特环。Cohen-Macaulay环是代数几何中最"良态"的环之一，许多一般交换环中的病态在CM环中不会出现。它们在建模代数簇、组合数学和代数统计中有广泛应用。

## 直观解释

Cohen-Macaulay环是那些"深度与维数相等"的环。深度度量了正则序列的长度（可以理解为"非零因子链"的长度），而维数是素理想链的长度。在一般情况下，深度 $\leq$ 维数；CM环正是取等号的环。这意味着这些环"没有隐藏的结构"——它们的同调性质完全由维数决定，没有"意外的"同调或奇点。几何上，CM环对应"等维且无嵌入分支"的簇。

## 形式化表述

设 $(R, \mathfrak{m})$ 是诺特局部环，维数为 $d$。

**定义**：$R$ 是**Cohen-Macaulay**，若存在（等价地，任何）参数系 $\underline{x} = x_1, \ldots, x_d$ 构成正则序列。

**等价条件**：

- $\text{depth}(R) = \dim(R)$
- 对任意素理想 $\mathfrak{p}$，$R_{\mathfrak{p}}$ 是CM
- 对任意真理想 $I$，$\text{grade}(I) = \text{ht}(I)$

**基本例子**：

- 正则局部环是CM
- 完全交是CM
- 多项式环模单项式理想的商（Stanley-Reisner环）在某些条件下是CM

## 证明思路

1. **正则序列存在性**：在CM环中，参数系总是正则序列
2. **局部化性质**：CM性质在局部化下保持
3. **维数公式**：利用深度-高度关系
4. **同调判别**：用局部上同调或Ext模刻画

## 示例

### 示例 1：超曲面

**问题**：证明 $R = k[x,y,z]/(xy - z^2)$ 是Cohen-Macaulay。

**解答**：

$\dim(R) = 2$（三维空间中的二次曲面）。

验证 $x, z$ 是正则序列：

- $x$ 不是零因子（$R$ 是整环）
- 在 $R/(x) = k[y,z]/(z^2)$ 中，$z$ 不是零因子

因此 $\text{depth}(R) \geq 2 = \dim(R)$，故 $R$ 是CM。

### 示例 2：非CM环

**问题**：$R = k[x,y,z]/(xy, xz)$ 是否是Cohen-Macaulay？

**解答**：

$\dim(R) = 2$，但 $\text{depth}(R) = 1$。

$x$ 不是零因子，但在 $R/(x) = k[y,z]/(0)$ 中，任何元素都是零因子。

因此 $R$ 不是CM。几何上，这对应两个相交平面（$y=0$ 和 $z=0$），在原点有嵌入分支。

## 应用

- **代数几何**：对偶性定理（Serre对偶、Grothendieck对偶）
- **组合数学**：Stanley-Reisner环的$h$-向量理论
- **不变量理论**：不变量环的CM性质
- **代数统计**：分层的条件独立模型
- **交截理论**：Chow群的性质

## 相关概念

- [Krull维数](./krull-dimension.md)：CM定义的核心
- 正则序列：CM环的基本工具
- 深度：同调不变量
- Gorenstein环：CM的特殊子类
- 正则局部环：CM且正则参数系生成极大理想

## 参考

### 教材

- Bruns, W. & Herzog, J. Cohen-Macaulay Rings. Cambridge, 1993.
- Matsumura, H. Commutative Ring Theory. Cambridge, 1986. Chapter 17

### 论文

- Cohen, I.S. On the structure and ideal theory of complete local rings. Trans. Amer. Math. Soc., 59: 54-106, 1946.
- Macaulay, F.S. The Algebraic Theory of Modular Systems. Cambridge, 1916.

### 在线资源

- [Cohen-Macaulay Ring Wikipedia](https://en.wikipedia.org/wiki/Cohen%E2%80%93Macaulay_ring)
- [Stacks Project - Cohen-Macaulay Rings](https://stacks.math.columbia.edu/tag/00N7)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
