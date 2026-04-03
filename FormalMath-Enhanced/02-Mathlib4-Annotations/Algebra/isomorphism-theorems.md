# 同构定理 (Isomorphism Theorems)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

namespace IsomorphismTheorems

variable {G H : Type*} [Group G] [Group H]

/-- 第一同构定理 -/
theorem first_isomorphism (f : G →* H) :
    G ⧸ (ker f) ≅* (range f) := by
  exact QuotientGroup.quotientKerEquivRange f

/-- 第二同构定理（钻石同构）-/
theorem second_isomorphism {H N : Subgroup G} [N.Normal] (hH : H ≤ G) :
    H ⧸ (H ⊓ N) ≅* (H ⊔ N) ⧸ N := by
  -- 对应定理的应用
  sorry

/-- 第三同构定理 -/
theorem third_isomorphism {M N : Subgroup G} [M.Normal] [N.Normal] (hMN : N ≤ M) :
    (G ⧸ N) ⧸ (M ⧸ N) ≅* G ⧸ M := by
  -- 商群的商
  sorry

end IsomorphismTheorems
```

## 数学背景

群同构定理（第一、第二、第三同构定理）是群论的基础结构定理，可以追溯到群论创立时期（Jordan, Hölder等）。这些定理揭示了商群构造与子群格之间的关系，是理解群结构的必要工具。它们在线性代数（向量空间商）、环论（理想商）和模论中有直接类比，是抽象代数的通用语言。

## 直观解释

同构定理告诉我们：**商操作如何与子群结构相互作用**。

- **第一同构**：同态的像与核的商同构
- **第二同构**：子群与正规子群的积的商结构
- **第三同构**：连续取商可以合并为一次商

这就像说，你可以分步骤简化一个代数结构，或者一次性简化，结果相同。

## 形式化表述

**第一同构定理**：$G/\ker f \cong \text{im } f$

**第二同构定理**：$H/(H \cap N) \cong HN/N$（$H \leq G$，$N \trianglelefteq G$）

**第三同构定理**：$(G/N)/(M/N) \cong G/M$（$N \leq M \trianglelefteq G$）

## 应用

- 群的分解和合成
- 同调代数中的长正合列
- 格同构定理的基础

---

*最后更新：2026-04-03 | 版本：v1.0.0*
