---
title: "极值定理 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.100A"
---

## 定理陈述

**自然语言**：设 $f: [a, b] \to \mathbb{R}$ 是闭区间上的连续函数，则 $f$ 在 $[a, b]$ 上必能取到最大值和最小值。即存在 $x_1, x_2 \in [a, b]$，使得对所有 $x \in [a, b]$ 都有
\[
f(x_1) \leq f(x) \leq f(x_2).
\]
更一般地，紧致拓扑空间上的连续实值函数必有最大值和最小值。

**Lean4**：

```lean
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real

namespace ExtremeValueTheorem
open Topology Set Real

-- 紧致集上的连续函数必取到最大值
theorem extreme_value_max {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hKne : K.Nonempty) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  have h_image_compact : IsCompact (f '' K) := by
    apply IsCompact.image hK hf
  rcases IsCompact.exists_isMaxOn hKne hK hf with ⟨x, hxK, hmax⟩
  use x, hxK
  intro y hyK
  exact hmax hyK

-- 最小值版本
theorem extreme_value_min {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hKne : K.Nonempty) :
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
  have hne : (Icc a b).Nonempty := by use a; exact ⟨by linarith, by linarith⟩
  have hcomp : IsCompact (Icc a b) := isCompact_Icc
  rcases extreme_value_min hcomp hf hne with ⟨x₁, hx₁, hmin⟩
  rcases extreme_value_max hcomp hf hne with ⟨x₂, hx₂, hmax⟩
  use x₁, hx₁, x₂, hx₂
  intro x hx
  constructor
  · exact hmin x hx
  · exact hmax x hx
end ExtremeValueTheorem
```

## 证明思路

**自然语言**：极值定理的标准证明基于紧致性：
1. 连续函数将紧致集映为紧致集，因此 $f([a, b])$ 是 $\mathbb{R}$ 中的紧致集。
2. $\mathbb{R}$ 中的紧致集等价于有界闭集，故 $f([a, b])$ 有界。
3. 由于 $f([a, b])$ 是闭集，其上确界和下确界都属于 $f([a, b])$。
4. 因此存在 $x_1, x_2 \in [a, b]$ 使得 $f(x_1) = \inf f([a, b])$ 且 $f(x_2) = \sup f([a, b])$。

**Lean4**：代码展示了两种等价路径。其一是先证明 `f '' K` 紧致，再调用 `exists_isMaxOn`/`exists_isMinOn`；其二直接对闭区间 `Icc a b` 应用这些定理。`isCompact_Icc` 是闭区间紧致性的标准定理。

## 关键 tactic/概念 教学

- `IsCompact.image`：连续映射保持紧致性。
- `IsCompact.exists_isMaxOn` / `exists_isMinOn`：紧致集上的连续实值函数必取到最大/最小值。
- `isCompact_Icc`：闭区间 $[a, b]$ 是紧致的。
- `ContinuousOn`：函数在集合上的连续性。
- `Icc a b`：闭区间 $[a, b]$ 的 Lean 记法。

## 练习

1. 构造一个在开区间 $(0, 1)$ 上连续但取不到最大值和最小值的函数，说明闭区间条件的重要性。
2. 证明：若 $f: [a, b] \to \mathbb{R}$ 连续，则 $f([a, b]) = [m, M]$，其中 $m$ 和 $M$ 分别是 $f$ 的最小值和最大值（结合介值定理）。
3. 在 Lean4 中对 $f(x) = x^3 - 3x$ 在 $[-2, 2]$ 上求最大值和最小值。
