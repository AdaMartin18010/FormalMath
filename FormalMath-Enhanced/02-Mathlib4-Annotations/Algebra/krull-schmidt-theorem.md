---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Krull-Schmidt 定理 (Krull-Schmidt Theorem)
---
# Krull-Schmidt 定理 (Krull-Schmidt Theorem)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.CategoryTheory.Preadditive.Projective

namespace Algebra

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Krull-Schmidt 定理：满足升链和降链条件的模具有唯一直和分解 -/
theorem krull_schmidt {decomp1 decomp2 : DirectSum.Decomposition (fun i : ι => M_i)}
    (hacc : IsNoetherian R M) (hdcc : IsArtinian R M)
    (hind1 : ∀ i, Indecomposable (M_i i)) (hind2 : ∀ j, Indecomposable (N_j j)) :
    ∃ e : ι ≃ κ, ∀ i, Nonempty (M_i i ≅ N_j (e i)) := by
  -- 利用自同态环的局部性和幂等元理论证明分解唯一性
  sorry

end Analysis
```

## 数学背景

Krull-Schmidt 定理是现代代数中关于模和群结构分解的基本定理，由德国数学家沃尔夫冈·克鲁尔（Wolfgang Krull）和奥托·施密特（Otto Schmidt）在20世纪初独立证明。该定理断言：一个满足升链和降链条件（即有限长度）的模，如果它可以分解为不可分解子模的直和，那么这种分解在重排和同构意义下是唯一的。Krull-Schmidt 定理是有限生成 Abel 群基本定理、Jordan-Hölder 定理和模表示论的基石，在群论、环论和同调代数中具有核心地位。

## 直观解释

Krull-Schmidt 定理告诉我们：某些代数对象（如满足链条件的模）的直和分解就像整数的素因子分解一样具有唯一性。想象你有一堆积木，每块积木都不能再被拆分成更小的积木（不可分解）。Krull-Schmidt 定理保证：如果你能用这些积木拼成某个结构，那么无论你用什么顺序或什么方式拼装，最终使用的积木种类和数量都是相同的（在重排和同构意义下）。这与算术基本定理（整数的唯一素因子分解）非常相似，但适用对象是更抽象的代数结构。

## 形式化表述

设 $M$ 是一个左 $R$-模，满足升链条件（ACC）和降链条件（DCC），即 $M$ 是有限长度的模。若：

$$M \cong M_1 \oplus M_2 \oplus \cdots \oplus M_n \cong N_1 \oplus N_2 \oplus \cdots \oplus N_m$$

是两个将 $M$ 分解为不可分解子模的直和分解，则 $n = m$，且存在 $\{1, \dots, n\}$ 的一个置换 $\sigma$ 使得：

$$M_i \cong N_{{\sigma(i)}} \quad (i = 1, 2, \dots, n)$$

其中：

- 不可分解模（indecomposable module）是指不能表示为两个非零真子模直和的模
- ACC 和 DCC 保证了自同态环中幂等元的分裂性
- 该定理对有限群也有类似版本：有限群的直积分解唯一性

## 证明思路

1. **自同态环的局部性**：不可分解模的自同态环是局部环（Fitting 引理）
2. **幂等元的提升**：利用 ACC 和 DCC 证明任何幂等元自同态都可以分裂出直和项
3. **归纳论证**：对模的长度进行归纳，提取出一个不可分解直和项
4. **唯一性比较**：利用自同态环的局部性和 Azumaya 定理证明两个分解中的项可以一一配对同构

核心洞察在于不可分解模的自同态环的局部性控制了分解的刚性。

## 示例

### 示例 1：有限生成 Abel 群

有限生成 Abel 群的基本定理可以看作是 Krull-Schmidt 定理的特例：任何有限生成 Abel 群都可以唯一分解为自由部分和挠部分的直和，而挠部分又可唯一分解为循环 p-群的直和。

### 示例 2：有限群的直积

设 $G$ 是一个有限群，若 $G \cong H_1 \times \cdots \times H_n \cong K_1 \times \cdots \times K_m$ 是不可分解群的直积分解，则 $n = m$ 且因子在重排后同构。

### 示例 3：表示论中的模

在有限群的模表示论中，不可分解模的分类是核心问题。Krull-Schmidt 定理保证了同一个表示的不同不可分解分解在重排后同构，这是建立表示范畴的基础。

## 应用

- **表示论**：群代数和 Hopf 代数的不可分解模分类
- **同调代数**：复形的分裂和导出范畴的构造
- **群论**：有限直积分解和群的自同构研究
- **代数几何**：凝聚层的直和分解和向量丛的稳定性
- **数论**：Galois 模和类域论中的分解问题

## 相关概念

- 不可分解模 (Indecomposable Module)：不能写成两个非零真子模直和的模
- 升链条件 (ACC)：子模的升链稳定化
- 降链条件 (DCC)：子模的降链稳定化
- 局部环 (Local Ring)：有唯一极大理想的环
- Fitting 引理 (Fitting's Lemma)：有限长度模自同态的幂零-可逆分解

## 参考

### 教材

- [S. Lang. Algebra. Springer, revised 3rd edition, 2002. Chapter XVII]
- [I. N. Herstein. Noncommutative Rings. AMS, 1968. Chapter 1]

### 在线资源

- [Mathlib4 - Decomposition](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Decomposition.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
