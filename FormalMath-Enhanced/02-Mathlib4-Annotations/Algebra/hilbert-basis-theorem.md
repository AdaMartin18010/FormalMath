---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Hilbert 基定理 (Hilbert's Basis Theorem)
---
# Hilbert 基定理 (Hilbert's Basis Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian

namespace RingTheory

variable {R : Type*} [CommRing R]

/-- Hilbert 基定理：若 R 是 Noether 环，则多项式环 R[X] 也是 Noether 环 -/
theorem hilbert_basis [IsNoetherianRing R] : IsNoetherianRing (Polynomial R) := by
  -- 利用理想的首项系数构造 R 中的升链，由 R 的 ACC 推出 R[X] 的 ACC
  sorry

end RingTheory
```

## 数学背景

Hilbert 基定理是交换代数中最具影响力的定理之一，由德国数学家大卫·希尔伯特（David Hilbert）于1890年证明。该定理断言：若 $R$ 是 Noether 环（即每个理想都是有限生成的），则一元多项式环 $R[X]$ 也是 Noether 环。由归纳法，多元多项式环 $R[X_1, \dots, X_n]$ 也是 Noether 环。Hilbert 基定理是代数几何的基石之一：它保证了仿射代数簇可以由有限多个多项式方程定义，从而将代数几何从无限的方程组研究中解放出来。这一定理也是证明代数不变量有限生成性的核心工具。

## 直观解释

Hilbert 基定理解决了一个基本但至关重要的问题：多项式环中的理想是否总是有限生成的？在整数环 $\mathbb{Z}$ 或域 $k$ 上，答案是肯定的。Hilbert 基定理将这个性质优雅地推广到了多项式环：如果基础环 $R$ 的每个理想都是有限生成的，那么 $R[X]$（进而 $R[X_1, \dots, X_n]$）的每个理想也都是有限生成的。在代数几何中，这意味着任何由多项式方程定义的集合（仿射簇）实际上只需要有限多个方程就能描述。例如，三维空间中的任何代数曲面系统，尽管可能涉及无穷多个多项式方程，但 Hilbert 基定理保证其中只有有限个是独立的，其余都可以由这有限个方程导出。

## 形式化表述

设 $R$ 是含幺交换环。若 $R$ 是 Noether 环，即 $R$ 的每个理想都是有限生成的，则：

1. 一元多项式环 $R[X]$ 也是 Noether 环
2. 由归纳法，多元多项式环 $R[X_1, X_2, \dots, X_n]$ 也是 Noether 环

等价表述：

$R[X]$ 中的任何理想的升链 $I_1 \subseteq I_2 \subseteq I_3 \subseteq \cdots$ 都会稳定化，即存在 $N$ 使得对所有 $n \geq N$ 有 $I_n = I_N$。

其中：

- Noether 环是以埃米·诺特（Emmy Noether）命名的环，满足理想的升链条件（ACC）
- 有限生成理想是指存在有限个元素 $f_1, \dots, f_m$ 使得 $I = (f_1, \dots, f_m)$
- 该定理对非交换环也有相应版本，但表述更为复杂

## 证明思路

1. **首项系数的提取**：设 $I \subseteq R[X]$ 是理想。对每个多项式，考虑其首项系数，定义 $J_n \subseteq R$ 为 $I$ 中次数不超过 $n$ 的多项式的首项系数集合
2. **理想的升链**：$J_0 \subseteq J_1 \subseteq J_2 \subseteq \cdots$ 构成 $R$ 中理想的升链
3. **ACC 的应用**：由于 $R$ 是 Noether 环，这个升链稳定化：存在 $N$ 使得 $J_N = J_{{N+1}} = \cdots$
4. **有限生成性**：每个 $J_n$（$n \leq N$）都是有限生成的，对应的生成元可以提升为 $I$ 中的有限个多项式。可以证明这有限个多项式生成整个 $I$

核心洞察在于多项式环中理想的复杂程度可以被基础环中的理想升链所控制。

## 示例

### 示例 1：仿射簇的有限定义

设 $k$ 是代数闭域。$k^n$ 中的任何代数集 $V$ 都可以由有限多个多项式方程定义。例如，$k[x, y]$ 中的任何理想都是有限生成的，因此 $k^2$ 中的任何代数曲线系统都只需有限个方程。

### 示例 2：不变量理论

Hilbert 最初证明该定理的动机是解决不变量理论中的问题：设 $G$ 是 $GL_n(k)$ 的子群，作用在多项式环 $k[x_1, \dots, x_n]$ 上。不变量环 $k[x_1, \dots, x_n]^G$ 是有限生成的 $k$-代数。这是 Hilbert 基定理和 Noether 正规化定理的推论。

### 示例 3：Grobner 基的计算终止性

在计算代数中，Buchberger 算法用于计算理想的 Grobner 基。Hilbert 基定理保证了该算法在有限步内终止，因为多项式环中的理想升链必须稳定。

## 应用

- **代数几何**：仿射簇的有限定义和坐标环的研究
- **交换代数**：Noether 环的构造和理想的有限生成性
- **不变量理论**：群作用下不变量环的有限生成性
- **计算代数**：Grobner 基和理想成员的判定算法
- **代数数论**：整数环上多项式环的算术性质

## 相关概念

- Noether 环 (Noetherian Ring)：满足理想升链条件的环
- 多项式环 (Polynomial Ring)：一个或多个不定元的多项式构成的环
- 升链条件 (ACC)：任何理想的升链最终稳定
- 仿射簇 (Affine Variety)：多项式零点集的代数几何对象
- Grobner 基 (Grobner Basis)：多项式理想的特殊生成集，便于计算

## 参考

### 教材

- [M. F. Atiyah, I. G. Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 7]
- [D. Eisenbud. Commutative Algebra with a View Toward Algebraic Geometry. Springer, 1995. Chapter 1]

### 在线资源

- [Mathlib4 - Noetherian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*