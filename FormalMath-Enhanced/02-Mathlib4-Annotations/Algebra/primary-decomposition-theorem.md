---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 准素分解定理 (Primary Decomposition Theorem)
---
# 准素分解定理 (Primary Decomposition Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian

namespace RingTheory

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Lasker-Noether 准素分解定理：Noether 环中任何理想可分解为准素理想的有限交 -/
theorem primary_decomposition (I : Ideal R) :
    ∃ (n : ℕ) (Q : Fin n → Ideal R),
      (∀ i, (Q i).IsPrimary) ∧
      I = ⨅ i, Q i := by
  -- 利用 Noether 归纳法和相伴素理想的理论证明
  sorry

end RingTheory
```

## 数学背景

准素分解定理（Lasker-Noether 定理）是交换代数中最深刻、最核心的结果之一，由德国数学家伊曼纽尔·拉斯克（Emanuel Lasker）于1905年对多项式环证明，后由埃米·诺特（Emmy Noether）于1921年推广到一般 Noether 环。该定理断言：在 Noether 交换环中，任何理想都可以表示为有限多个准素理想的交。这是算术基本定理在一般交换环中的深刻推广：正如整数可以唯一分解为素数的幂，Noether 环中的理想也可以（在某种意义上）唯一分解为准素理想的交。准素分解定理是代数几何、代数数论和组合交换代数中不可绕过的基础。

## 直观解释

准素分解定理是整数的唯一素因子分解定理在交换环理想论中的高维推广。在整数环 $\mathbb{Z}$ 中，每个理想 $(n)$ 都可以唯一地写成素数幂理想的乘积：$(n) = (p_1^{{a_1}}) \cap \cdots \cap (p_k^{{a_k}})$。在更一般的 Noether 环中，理想的乘法结构可能非常复杂，但准素分解定理保证：任何理想仍然可以分解为有限多个准素理想的交。每个准素理想对应一个素理想（称为其根），就像 $p^k$ 对应素数 $p$ 一样。虽然分解在一般情况下不唯一，但相伴素理想的集合是唯一的——这保留了唯一分解理论的核心精神。

## 形式化表述

设 $R$ 是 Noether 交换环，$I$ 是 $R$ 的任意理想。则存在有限多个准素理想 $Q_1, Q_2, \dots, Q_n$ 使得：

$$I = Q_1 \cap Q_2 \cap \cdots \cap Q_n$$

进一步，若要求分解是极小的（即去掉任何 $Q_i$ 都会改变交，且各相伴素理想互不相同），则：

1. **相伴素理想的唯一性**：$\{\sqrt{Q_1}, \sqrt{Q_2}, \dots, \sqrt{Q_n}\}$ 由 $I$ 唯一确定
2. **孤立分支的唯一性**：对应于极小相伴素理想的分支 $Q_i$ 是唯一的

其中：

- 准素理想 $Q$ 是指：若 $ab \in Q$ 且 $a \notin Q$，则 $b \in \sqrt{Q}$（某个幂在 $Q$ 中）
- $\sqrt{Q}$ 是包含 $Q$ 的最小素理想，称为相伴素理想
- 该定理对一般交换环不成立，Noether 条件至关重要

## 证明思路

1. **不可约理想**：首先证明 Noether 环中任何理想都可以表示为有限多个不可约理想的交
2. **不可约蕴含准素**：在 Noether 环中，不可约理想必是准素理想。证明思路：若 $Q$ 不是准素的，则可以构造出严格包含于 $Q$ 的两个理想的真交等于 $Q$，与不可约性矛盾
3. **Noether 归纳**：利用理想的集合上的 Noether 条件（升链条件）进行归纳，证明任何理想都有准素分解
4. **唯一性**：利用局部化技巧证明相伴素理想集合的唯一性

核心洞察在于 Noether 条件迫使理想的复杂结构可以被有限个基本构建块（准素理想）所捕捉。

## 示例

### 示例 1：整数环中的分解

在 $\mathbb{Z}$ 中，理想 $(12) = (4) \cap (3) = (2^2) \cap (3)$。这里 $(4)$ 是准素理想（相伴素理想为 $(2)$），$(3)$ 本身是素理想（也是准素理想）。

### 示例 2：多项式环中的几何解释

在 $k[x, y]$ 中，理想 $I = (x^2, xy)$ 对应于 y 轴（$x = 0$）和原点（$x = y = 0$）的并集。其准素分解为 $I = (x) \cap (x^2, y)$。这里 $(x)$ 对应于 y 轴，$(x^2, y)$ 是准素理想（相伴素理想 $(x, y)$），对应于原点处的嵌入结构。

### 示例 3：Stanley-Reisner 环

在组合交换代数中，单纯复形的 Stanley-Reisner 理想的准素分解与复形的面结构密切相关。这是代数组合学中代数与组合结构相互翻译的典范。

## 应用

- **代数几何**：仿射簇的不可约分解和嵌入分量的研究
- **代数数论**：Dedekind 整环中理想的素因子分解（唯一分解的特殊情形）
- **组合交换代数**：单纯复形与单项式理想的几何对应
- **计算代数**：Macaulay2 和 Singular 中理想分解的算法基础
- **表示论**：模的相伴素理想和支撑集的分类

## 相关概念

- 准素理想 (Primary Ideal)：类素理想的推广
- 相伴素理想 (Associated Prime)：准素理想的根理想
- 不可约理想 (Irreducible Ideal）：不能写成两个严格大理想的交的 ideal
- Noether 归纳法 (Noetherian Induction)：基于 ACC 的归纳证明技巧
- 局部化 (Localization)：在素理想处考察环的局部性质

## 参考

### 教材

- [M. F. Atiyah, I. G. Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 4]
- [D. Eisenbud. Commutative Algebra with a View Toward Algebraic Geometry. Springer, 1995. Chapter 3]

### 在线资源

- [Mathlib4 - Ideal Operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
