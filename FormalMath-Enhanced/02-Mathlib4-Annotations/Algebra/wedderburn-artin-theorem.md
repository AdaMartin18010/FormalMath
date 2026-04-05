---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Wedderburn-Artin定理 (Wedderburn-Artin Theorem)
---
# Wedderburn-Artin定理 (Wedderburn-Artin Theorem)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Semiprime
import Mathlib.RingTheory.SimpleModule

namespace WedderburnArtin

variable {R : Type*} [Ring R]

/-- Wedderburn-Artin定理：半单Artin环的结构 -/
theorem wedderburn_artin [IsSemiprime R] [IsArtinian R R] :
    ∃ (n : ℕ) (D : Fin n → Type*) [∀ i, DivisionRing (D i)]
      (h : R ≃+* (Π i, Matrix (Fin (r i)) (Fin (r i)) (D i))),
      True := by
  -- 分解为本原中心幂等元
  have hprim : ∃ (e : Fin n → R), 
    (∀ i, IsPrimitiveCentralIdempotent (e i)) ∧
    (∑ i, e i = 1) ∧ Pairwise (λ i j => e i * e j = 0) := by
    sorry
  -- 每个分量是除环上的矩阵代数
  sorry

/-- 单Artin环是除环上的矩阵环 -/
theorem simple_artin_ring {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinian R R] :
    ∃ (n : ℕ) (D : Type*) [DivisionRing D],
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  -- 极小左理想的存在性
  have hmin : ∃ I : Ideal R, IsAtom I := by
    sorry
  -- 单环的结构
  sorry

/-- 交换半单Artin环是有限个域的积 -/
theorem commutative_semisimple_artin [CommRing R] [IsSemiprime R] [IsArtinian R R] :
    ∃ (n : ℕ) (K : Fin n → Type*) [∀ i, Field (K i)],
      Nonempty (R ≃+* Π i, K i) := by
  sorry

end WedderburnArtin
```

## 数学背景

Wedderburn-Artin定理由Joseph Wedderburn在1907年和Emil Artin在1927年证明，是环论中最深刻的结构定理之一。它完全分类了半单Artin环（或等价地，半单有限维代数），表明它们都同构于除环上矩阵环的有限直积。这一定理是表示论、同调代数和非交换代数几何的基石，提供了理解半单代数结构的完整框架。

## 直观解释

Wedderburn-Artin定理告诉我们：**半单环就是除环上矩阵环的积木拼成的**。

想象半单环是由"原子"构建的。定理说这些原子就是除环上的矩阵代数。整个环可以分解为这些简单成分的直和，类似于将复杂分子分解为元素。这种分解是唯一的（除顺序和同构外），给出了半单环的完整分类。

## 形式化表述

环 $R$ 称为**半单**，如果 $R$ 作为左 $R$-模是半单的（即单模的直和）。

**Wedderburn-Artin定理**：

**左半单 $\Leftrightarrow$ 右半单 $\Leftrightarrow$ $R \cong \prod_{i=1}^n M_{r_i}(D_i)$**

其中：
- $M_{r_i}(D_i)$ 是除环 $D_i$ 上的 $r_i \times r_i$ 矩阵环
- 分解在重排和同构意义下唯一
- 等价条件：$R$ 是半素Artin环

**单Artin环**：$R \cong M_n(D)$（单一矩阵块）

## 证明思路

1. **半单模的分解**：$R \cong \bigoplus_i S_i^{n_i}$（单模的直和）
2. **本原幂等元**：构造正交本原中心幂等元 $e_i$，$R \cong \prod_i e_i R$
3. **单分量**：每个 $e_i R$ 是单Artin环
4. **Schur引理**：单模自同态环是除环
5. **对偶性**：$R^{op} \cong \text{End}_R(_R R)$，给出矩阵结构

核心洞察是模论、表示论和环论的对偶关系。

## 示例

### 示例 1：复群代数

$\mathbb{C}[S_3]$ 是半单的（Maschke定理）。

Wedderburn-Artin分解：
$$\mathbb{C}[S_3] \cong \mathbb{C} \times \mathbb{C} \times M_2(\mathbb{C})$$

对应不可约表示的维数：$1^2 + 1^2 + 2^2 = 6$。

### 示例 2：矩阵代数

$M_n(k)$ 是单Artin环，除环 $D = k$。

唯一的单模是 $k^n$（列向量）。

### 示例 3：直积环

$k \times k \times k$ 是交换半单Artin环。

每个分量都是域 $k$，没有矩阵结构。

## 应用

- **表示论**：群代数的分解
- **同调代数**：半单环的投射维数为0
- **代数几何**：Azumaya代数的分类
- **编码理论**：群码的结构
- **量子群**：半单表示的范畴

## 相关概念

- 半单环 (Semisimple Ring)：半单模上的环
- Artin环 (Artinian Ring)：满足降链条件的环
- 单环 (Simple Ring)：无非平凡双边理想的环
- 半素环 (Semiprime Ring)：无幂零理想的环
- 本原幂等元 (Primitive Idempotent)：不可分解的幂等元

## 参考

### 教材

- [Lam. A First Course in Noncommutative Rings. Springer, 1991. Chapter 3]
- [Pierce. Associative Algebras. Springer, 1982. Chapter 4]

### 历史文献

- [Wedderburn. On hypercomplex numbers. 1907]
- [Artin. Zur Theorie der hyperkomplexen Zahlen. 1927]

### 在线资源

- [Mathlib4 文档 - Artinian](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian.html)[需更新]
- [Stacks Project - 0744](https://stacks.math.columbia.edu/tag/0744)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
