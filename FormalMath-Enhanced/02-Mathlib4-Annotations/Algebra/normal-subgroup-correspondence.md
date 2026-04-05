---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 正规子群对应定理 (Normal Subgroup Correspondence)
---
# 正规子群对应定理 (Normal Subgroup Correspondence)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace NormalSubgroupCorrespondence

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- 正规子群对应定理 -/
theorem normal_correspondence :
    { H : Subgroup G // N ≤ H ∧ H.Normal } ≃
    { K : Subgroup (G ⧸ N) // K.Normal } := by
  refine {
    toFun := fun H => ⟨H.1.map (QuotientGroup.mk' N), by sorry⟩,
    invFun := fun K => ⟨K.1.comap (QuotientGroup.mk' N), by sorry⟩,
    left_inv := sorry,
    right_inv := sorry
  }

/-- 商群的正规子群提升 -/
theorem quotient_normal_lift {K : Subgroup (G ⧸ N)} (hK : K.Normal) :
    ∃! H : Subgroup G, N ≤ H ∧ H.Normal ∧ H.map (QuotientGroup.mk' N) = K := by
  -- 对应的双射性
  sorry

end NormalSubgroupCorrespondence
```

## 数学背景

正规子群对应定理是群论中的基本结构定理，表明商群的正规子群与原群包含核的正规子群之间存在一一对应。这是格同构定理的特例，在理解群的结构层次时非常重要。

## 形式化表述

包含 $N$ 的正规子群 $\leftrightarrow$ $G/N$ 的正规子群

对应保持包含关系、交、并等格运算。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
