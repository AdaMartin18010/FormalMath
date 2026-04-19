---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Jordan-Hölder定理 (Jordan-Hölder Theorem)
---
# Jordan-Hölder定理 (Jordan-Hölder Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.CompositionSeries
import Mathlib.GroupTheory.GroupAction.Basic

namespace JordanHolder

variable {G : Type*} [Group G]

/-- 合成列的定义 -/
structure CompositionSeries (G : Type*) [Group G] where
  length : ℕ
  series : Fin (length + 1) → Subgroup G
  step : ∀ i : Fin length, (series i.succ).Normal
  isCompositionSeries : ∀ i : Fin length,
    IsSimpleGroup ((series i) ⧸ (series i.succ).comap (series i).subtype)

/-- Jordan-Hölder定理：合成因子的唯一性 -/
theorem jordan_holder_uniqueness (s₁ s₂ : CompositionSeries G) :
    ∃ p : Fin s₁.length ≃ Fin s₂.length,
    ∀ i : Fin s₁.length,
    SimpleGroup ((s₁.series i) ⧸ (s₁.series i.succ).comap (s₁.series i).subtype) ≅
    SimpleGroup ((s₂.series (p i)) ⧸ (s₂.series (p i).succ).comap (s₂.series (p i)).subtype) := by
  -- 对长度进行归纳
  induction s₁.length generalizing s₂ with
  | zero =>
    -- 平凡情形
    sorry
  | succ n ih =>
    -- 利用Schreier细化定理
    sorry

/-- Schreier细化定理 -/
theorem schreier_refinement (s₁ s₂ : CompositionSeries G) :
    ∃ t : CompositionSeries G,
      t.IsRefinementOf s₁ ∧ t.IsRefinementOf s₂ := by
  sorry

end JordanHolder
```

## 数学背景

Jordan-Hölder定理由Camille Jordan在1869年首次证明（对置换群），后由Otto Hölder在1889年推广到一般群。这是有限群论的结构定理，表明有限群可以通过合成列"分解"为单群的序列，且这种分解在重排意义下唯一。这一定理类似于整数的素因数分解定理，是理解有限群结构的基石。

## 直观解释

Jordan-Hölder定理告诉我们：**有限群有唯一的"单群分解"**。

想象将有限群看作一个复杂的分子，定理说存在唯一的（在重排意义下）方式将其分解为"原子"（单群）。合成列就是分解过程：从群 $G$ 开始，找一个极大正规子群 $G_1$，再找 $G_1$ 的极大正规子群 $G_2$，直到平凡群。每一步的商 $G_i/G_{i+1}$ 都是单群，这些单群（重计重数）唯一确定了 $G$ 的结构。

## 形式化表述

群 $G$ 的**合成列**是子群序列：
$$G = G_0 \triangleright G_1 \triangleright G_2 \triangleright \cdots \triangleright G_n = \{e\}$$
使得每个因子 $G_i/G_{i+1}$ 是单群（称为**合成因子**）。

**Jordan-Hölder定理**：若群 $G$ 有两条合成列，则：

1. 它们长度相同
2. 合成因子在同构和重排意义下相同

**Schreier细化定理**：任意两个正规列有等价的细化。

## 证明思路

1. **Schreier细化定理**：
   - Zassenhaus引理（蝴蝶引理）：比较两个正规子群的交与积
   - 构造两个正规列的公共细化

2. **Jordan-Hölder定理**：
   - 合成列已是极大正规列，不可再细化
   - 由Schreier定理，任意两条合成列等价
   - 故合成因子集合同构

核心洞察是正规子群的格结构允许我们"同步"比较两个列。

## 示例

### 示例 1：$S_3$ 的合成列

$$S_3 \triangleright A_3 \triangleright \{e\}$$

合成因子：$S_3/A_3 \cong \mathbb{Z}_2$，$A_3 \cong \mathbb{Z}_3$

### 示例 2：$S_4$ 的合成列

$$S_4 \triangleright A_4 \triangleright V_4 \triangleright \mathbb{Z}_2 \triangleright \{e\}$$

合成因子：$\mathbb{Z}_2$, $\mathbb{Z}_3$, $\mathbb{Z}_2$, $\mathbb{Z}_2$

注意：$V_4$ 有两个不同的 $\mathbb{Z}_2$ 子群，但合成因子相同。

### 示例 3：不同合成列的例子

考虑 $G = \mathbb{Z}_6$：

- 列1：$\mathbb{Z}_6 \triangleright \mathbb{Z}_3 \triangleright \{0\}$，因子：$\mathbb{Z}_2$, $\mathbb{Z}_3$
- 列2：$\mathbb{Z}_6 \triangleright \mathbb{Z}_2 \triangleright \{0\}$，因子：$\mathbb{Z}_3$, $\mathbb{Z}_2$

相同因子集（重排后）。

## 应用

- **有限单群分类**：理解一般有限群的结构
- **可解群理论**：可解性等价于合成因子为素数阶循环群
- **表示论**：模的合成列与合成因子
- **代数几何**：层的合成列

## 相关概念

- 单群 (Simple Group)：没有非平凡正规子群的群
- [可解群 (Solvable Group)](./solvable-group.md)：合成因子为循环群
- 正规列 (Normal Series)：正规子群的降链
- Schreier定理 (Schreier's Theorem)：正规列的细化
- 合成因子 (Composition Factor)：单群因子

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 7]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 3.4]

### 历史文献

- [Jordan. Commentaires sur Galois. Mathematische Annalen, 1869]
- [Hölder. Zurückführung einer beliebigen algebraischen Gleichung auf eine Kette von Gleichungen. 1889]

### 在线资源

- [Mathlib4 文档 - CompositionSeries][https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/CompositionSeries.html](需更新)
- [Groupprops - Composition series][https://groupprops.subwiki.org/wiki/Composition_series](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
