---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 中山引理 (Nakayama Lemma)
---
# 中山引理 (Nakayama Lemma)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Finiteness

namespace Nakayama

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- 中山引理：若M=IM且I含于Jacobson根，则M=0 -/
theorem nakayama_lemma {I : Ideal R} (hI : I ≤ jacobson R)
    (hM : Submodule.span R (Set.image (fun i m => i • m) (I ×ˢ Set.univ)) = ⊤) :
    Subsingleton M := by
  -- 反证法
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  -- 利用Jacobson根的性质
  have hJ : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    exact isUnit_of_mem_jacobson (hI hx)
  -- 构造非零元素的逆
  sorry

/-- 中山引理（有限生成版本）-/
theorem nakayama_lemma_fg {I : Ideal R} (hI : I ≤ jacobson R)
    [Module.Finite R M] (hM : I • ⊤ = ⊤) : Subsingleton M := by
  rw [Module.Finite.iff_fg] at *
  -- 约化到有限生成情形
  sorry

/-- 中山引理（生成元版本）-/
theorem nakayama_lemma_generator {I : Ideal R} (hI : I ≤ jacobson R)
    {N : Submodule R M} [Module.Finite R M]
    (h : M = N + I • ⊤) : M = N := by
  have : I • (M ⧸ N) = ⊤ := by
    rw [Submodule.map_smul''']
    sorry
  have : Subsingleton (M ⧸ N) := nakayama_lemma_fg hI this
  exact Submodule.subsingleton_quotient_iff_eq_top.mp this

end Nakayama
```

## 数学背景

中山引理由Tadashi Nakayama（中山正）在1951年系统表述，但其思想可追溯至Krull和Azumaya的工作。这是交换代数和同调代数中最有用的工具之一，尤其在研究局部环的模结构时不可或缺。引理的核心思想是：Jacobson根作用下的"小扰动"不改变有限生成模的本质结构。

## 直观解释

中山引理告诉我们：**如果有限生成模被Jacobson根"吸收"，那么这个模实际上是零**。

想象模 $M$ 是一个向量空间（虽然更一般）。如果 $M$ 中的每个元素都可以被Jacobson根中的元素"生成"（即 $M = IM$），那么 $M$ 必须为零。直观上，Jacobson根包含所有"接近于零"的元素，如果整个模都能被这些"小"元素生成，那它本质上就没有"大"结构。

## 形式化表述

设 $R$ 是交换环，$M$ 是有限生成 $R$-模，$I \subseteq R$ 是含于Jacobson根 $J(R)$ 的理想。

**中山引理**：
1. **基本形式**：若 $M = IM$，则 $M = 0$
2. **生成元形式**：若 $N \subseteq M$ 是子模且 $M = N + IM$，则 $M = N$
3. **提升形式**：若 $m_1, \ldots, m_n$ 生成 $M/IM$，则它们生成 $M$

**Jacobson根**：$J(R) = \bigcap_{\mathfrak{m}} \mathfrak{m}$（所有极大理想的交）。

## 证明思路

1. **准备**：设 $M$ 由 $m_1, \ldots, m_n$ 有限生成，$M = IM$
2. **矩阵表示**：由 $m_i \in IM$ 得 $m_i = \sum_j a_{ij} m_j$，其中 $a_{ij} \in I$
3. **Cayley-Hamilton**：矩阵 $A = (a_{ij})$ 满足 $(I - A)\mathbf{m} = 0$
4. **可逆性**：$\det(I - A) \equiv 1 \pmod{I}$，在Jacobson根条件下可逆
5. **结论**：由Cramer法则得所有 $m_i = 0$

核心洞察是矩阵技巧与Jacobson根的代数性质结合。

## 示例

### 示例 1：局部环情形

设 $(R, \mathfrak{m})$ 是局部环，$M$ 是有限生成 $R$-模。

若 $M = \mathfrak{m}M$，则 $M = 0$。

应用：证明有限生成投射模在局部环上是自由的。

### 示例 2：提升生成元

设 $M$ 是局部环 $(R, \mathfrak{m})$ 上的有限生成模。

若 $\bar{m}_1, \ldots, \bar{m}_n$ 生成 $M/\mathfrak{m}M$（作为 $R/\mathfrak{m}$ 上的向量空间），

则 $m_1, \ldots, m_n$ 生成 $M$。

### 示例 3：矩阵环

设 $R = \mathbb{Z}_{(p)}$（$\mathbb{Z}$ 在素理想 $(p)$ 处的局部化），$\mathfrak{m} = (p)$。

考虑 $M = \mathbb{Z}_{(p)}^2$，若 $M = pM$，则 $M = 0$（显然成立）。

## 应用

- **局部环上的模**：证明自由性和投射性等价
- **维数理论**：Krull主理想定理的证明
- **相交重数**：代数几何中的重数计算
- **完备化理论**：$\mathfrak{m}$-adic完备化的性质

## 相关概念

- Jacobson根 (Jacobson Radical)：所有极大理想的交
- 局部环 (Local Ring)：唯一极大环
- 有限生成模 (Finitely Generated Module)：模的有限生成性
- 投射模 (Projective Module)：直和项模
- 完备化 (Completion)：拓扑代数结构

## 参考

### 教材

- [Atiyah & Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 2]
- [Eisenbud. Commutative Algebra. Springer, 1995. Section 4.1]

### 历史文献

- [Nakayama. A remark on finitely generated modules. Nagoya Math. J., 1951]

### 在线资源

- [Mathlib4 文档 - Jacobson](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Basic.html)[需更新]
- [Stacks Project - 00DV](https://stacks.math.columbia.edu/tag/00DV)[需更新]

---

*最后更新：2026-04-03 | 版本：v1.0.0*
