---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Noether 正规化定理 (Noether Normalization Theorem)
---
# Noether 正规化定理 (Noether Normalization Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian

namespace RingTheory

variable {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra k R]
  (hfin : Algebra.FiniteType k R)

/-- Noether 正规化定理：有限生成 k-代数包含一个多项式子代数，
    且在该子代数上整 -/
theorem noether_normalization :
    ∃ (n : ℕ) (x : Fin n → R),
      AlgebraicIndependent k x ∧
      (algebraMap k R).range ≤Subalgebra.ofAlgebraicIndependent x ∧
      IsIntegral (Subalgebra.ofAlgebraicIndependent x) R := by
  -- 通过对生成元个数归纳，利用原像消去法证明
  sorry

end RingTheory
```

## 数学背景

Noether 正规化定理是交换代数和代数几何中最深刻、最具结构性的定理之一，由德国数学家埃米·诺特（Emmy Noether）在20世纪20年代证明。该定理断言：若 $R$ 是域 $k$ 上的有限生成交换代数，则存在 $R$ 中代数无关的元素 $x_1, \dots, x_n$ 使得 $R$ 在多项式子代数 $k[x_1, \dots, x_n]$ 上是整的。这一定理是证明 Hilbert 零点定理、Krull 维数理论和代数簇的纤维维数定理的核心工具。它将任意有限生成代数的研究化归为多项式环上的整扩张研究，从而可以利用数论和代数几何中关于整扩张的丰富工具。

## 直观解释

Noether 正规化定理告诉我们：任何由有限多个元素生成的交换代数，其内部都隐藏着一个多项式环，并且整个代数在这个多项式环上表现得像一个有限覆盖。想象一个复杂的曲面（如扭曲的纸带），Noether 正规化定理保证你可以在这个曲面上找到一个坐标系统（多项式子代数），使得曲面在这个坐标系统上的每一点只有有限多个原像。这就好比你用一张平面的地图（多项式环）来覆盖一个复杂的地形（有限生成代数），虽然地形起伏不平，但每个地图格子只对应有限多个地形点。这种结构简化是研究高维代数簇和交换环的基石。

## 形式化表述

设 $k$ 是域，$R$ 是 $k$ 上的有限生成交换代数。则存在 $n \geq 0$ 和 $R$ 中的元素 $x_1, x_2, \dots, x_n$ 使得：

1. **代数无关性**：$x_1, \dots, x_n$ 在 $k$ 上代数无关，即 $k[x_1, \dots, x_n]$ 同构于 $n$ 元多项式环
2. **整性**：$R$ 在 $k[x_1, \dots, x_n]$ 上是整的，即 $R$ 的每个元素都满足一个以 $k[x_1, \dots, x_n]$ 中元素为系数的首一多项式

等价表述（几何形式）：任何仿射代数簇 $X$ 都允许一个到仿射空间 $\mathbb{A}^n_k$ 的有限态射 $\pi: X \to \mathbb{A}^n_k$，其中 $n = \dim(X)$。

其中：

- $k[x_1, \dots, x_n]$ 称为 $R$ 的 Noether 正规化子
- 整性意味着 $R$ 作为 $k[x_1, \dots, x_n]$-模是有限生成的
- 维数 $n$ 等于 $R$ 的 Krull 维数

## 证明思路

1. **原像消去法**：设 $R = k[y_1, \dots, y_m]/(f_1, \dots, f_r)$。若 $y_1, \dots, y_m$ 代数相关，则存在非零多项式关系 $P(y_1, \dots, y_m) = 0$
2. **坐标变换**：通过适当的线性变换 $z_i = y_i + \lambda_i y_m$（$\lambda_i \in k$），可以将 $y_m$ 从这个关系中消去，得到 $y_m$ 在 $k[z_1, \dots, z_{{m-1}}]$ 上是整的
3. **归纳**：对 $k[z_1, \dots, z_{{m-1}}]$ 的子代数重复上述过程，直到得到一个代数无关的集合
4. **整性验证**：每次消去都保证了一个生成元在剩余生成元上的整性

核心洞察在于通过巧妙的坐标变换，可以将代数相关关系转化为整依赖关系。

## 示例

### 示例 1：椭圆曲线

设 $R = k[x, y]/(y^2 - x^3 + x)$ 是椭圆曲线的坐标环。$x$ 在 $k$ 上超越，而 $y$ 在 $k[x]$ 上整（满足 $y^2 = x^3 - x$）。因此 $k[x] \subseteq R$ 是一个 Noether 正规化。几何上，这对应于椭圆曲线到 $\mathbb{A}^1$ 的 2:1 映射。

### 示例 2：Hilbert 零点定理的证明

在 Zariski 对 Hilbert 零点定理的证明中，Noether 正规化定理是关键一步。它将任意仿射簇的坐标环化归为多项式环上的整扩张，从而将问题转化为已知的整扩张性质。

### 示例 3：维数理论

Noether 正规化定理直接推出有限生成交换代数的 Krull 维数等于其 Noether 正规化子的 transcendence degree。这为计算代数簇的维数提供了代数方法。

## 应用

- **代数几何**：仿射簇的有限态射和纤维维数理论
- **交换代数**：整扩张、维数理论和深度理论
- **不变量理论**：群作用下不变量环的结构研究
- **代数数论**：代数整数环和 Dedekind 域的构造
- **表示论**：代数群和 Lie 代数的坐标环研究

## 相关概念

- 整扩张 (Integral Extension)：环的每个元素都满足首一多项式
- 代数无关 (Algebraically Independent)：不存在非零多项式关系
- Krull 维数 (Krull Dimension)：素理想链的最大长度
- 有限生成代数 (Finitely Generated Algebra)：作为代数由有限个元素生成
- 仿射簇 (Affine Variety)：多项式零点集的代数几何对象

## 参考

### 教材

- [M. F. Atiyah, I. G. Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 5]
- [D. Eisenbud. Commutative Algebra with a View Toward Algebraic Geometry. Springer, 1995. Chapter 13]

### 在线资源

- [Mathlib4 - Noetherian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
