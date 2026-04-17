/-
# 极值定理 / Extreme Value Theorem

## Mathlib4 对应
- **模块**: `Mathlib.Topology.Compactness.Compact`, `Mathlib.Topology.Order.IntermediateValue`
- **核心定理**: `IsCompact.exists_isMaxOn`, `IsCompact.exists_isMinOn`

## 定理陈述
若 $f: [a, b] \to \mathbb{R}$ 是闭区间上的连续函数，则 $f$ 在 $[a, b]$ 上必能取到最大值和最小值。
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real

namespace ExtremeValueTheorem

open Topology Set Real

-- 极值定理：紧致集上的连续实值函数必取到最大值和最小值
theorem extreme_value_max {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) (hKne : K.Nonempty) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  /- 连续函数将紧致集映为紧致集，而 ℝ 中的紧致集是有界闭集，故必含上确界 -/
  have h_image_compact : IsCompact (f '' K) := by
    apply IsCompact.image hK hf
  have h_image_closed : IsClosed (f '' K) := by
    exact h_image_compact.isClosed
  have h_bdd_above : BddAbove (f '' K) := by
    exact h_image_compact.bddAbove
  have h_bdd_below : BddBelow (f '' K) := by
    exact h_image_compact.bddBelow
  /- 紧致集上的连续函数必取到最大值 -/
  rcases IsCompact.exists_isMaxOn hKne hK hf with ⟨x, hxK, hmax⟩
  use x, hxK
  intro y hyK
  exact hmax hyK

-- 最小值版本
theorem extreme_value_min {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K) (hKne : K.Nonempty) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  rcases IsCompact.exists_isMinOn hKne hK hf with ⟨x, hxK, hmin⟩
  use x, hxK
  intro y hyK
  exact hmin hyK

-- 闭区间上的经典版本
theorem extreme_value_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∃ x₁ ∈ Icc a b, ∃ x₂ ∈ Icc a b,
      ∀ x ∈ Icc a b, f x₁ ≤ f x ∧ f x ≤ f x₂ := by
  have hne : (Icc a b).Nonempty := by
    use a
    exact ⟨by linarith, by linarith⟩
  have hcomp : IsCompact (Icc a b) := isCompact_Icc
  rcases extreme_value_min hcomp hf hne with ⟨x₁, hx₁, hmin⟩
  rcases extreme_value_max hcomp hf hne with ⟨x₂, hx₂, hmax⟩
  use x₁, hx₁, x₂, hx₂
  intro x hx
  constructor
  · exact hmin x hx
  · exact hmax x hx

end ExtremeValueTheorem
