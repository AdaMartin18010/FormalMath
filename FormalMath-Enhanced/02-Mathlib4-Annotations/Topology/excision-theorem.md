---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 切除定理 (Excision Theorem)
---
# 切除定理 (Excision Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.SingularHomology
import Mathlib.AlgebraicTopology.RelativeHomology

namespace ExcisionTheorem

variable {X : Type*} [TopologicalSpace X] {A U : Set X}
  (hU : IsOpen U) (hAclosed : IsClosed A) (hUA : U ⊆ A)

/-- 切除定理 -/
theorem excision (n : ℕ) :
    H_n (X \ U, A \ U) ≅ H_n (X, A) := by
  -- 小单纯形论证
  sorry

/-- 切除定理的等价形式 -/
theorem excision_equivalent {Z : Set X} (hZ : closure Z ⊆ interior A) (n : ℕ) :
    H_n (X \ Z, A \ Z) ≅ H_n (X, A) := by
  -- 由标准形式推出
  sorry

end ExcisionTheorem
```

## 数学背景

切除定理是同调论的基本定理之一，表明在同调计算中可以"切除"内部子集而不改变相对同调。这是证明Mayer-Vietoris序列和计算复杂空间同调的关键工具。

## 形式化表述

若 $\overline{U} \subseteq \text{int}(A)$，则 $H_n(X \setminus U, A \setminus U) \cong H_n(X, A)$。

## 应用

- Mayer-Vietoris序列
- 球面的同调计算
- 胞腔同调的等价性

---

*最后更新：2026-04-03 | 版本：v1.0.0*
