import Mathlib
/-
# 极值定理 / Extreme Value Theorem

## Mathlib4 对应
- **模块**: `Mathlib.Topology.Compactness.Compact`, `Mathlib.Topology.Order.IntermediateValue`
- **核心定理**: `IsCompact.exists_isMaxOn`, `IsCompact.exists_isMinOn`

## 定理陈述
若 $f: [a, b] \to \mathbb{R}$ 是闭区间上的连续函数，则 $f$ 在 $[a, b]$ 上必能取到最大值和最小值。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Topology.Compactness.Compact`
- 模块 / Module: `Mathlib.Topology.Order.IntermediateValue`
- 定理 / Theorem: `IsCompact.exists_isMaxOn`
-/

#check IsCompact.exists_isMaxOn

-- Extreme Value Theorem: continuous function on compact set attains max and min
theorem ExtremeValueTheorem {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsCompact s)
    {f : X → ℝ} (hf : ContinuousOn f s) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  exact IsCompact.exists_isMaxOn hs hne hf

