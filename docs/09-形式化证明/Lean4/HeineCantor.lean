/-
# Heine-Cantor 定理 / 一致连续性定理

## Mathlib4 对应
- **模块**: `Mathlib.Topology.UniformSpace.Basic`, `Mathlib.Topology.Compact`
- **核心定理**: `CompactSpace.uniformContinuous_of_continuous`

## 定理陈述
若 $f: X \to Y$ 是从紧致度量空间到度量空间的连续函数，则 $f$ 是一致连续的。

## 数学意义
Heine-Cantor 定理表明在紧致域上，连续性自动升级为一致连续性。这是实分析中许多收敛性结果的基础。
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic

namespace HeineCantorTheorem

open Topology Metric Filter Set

-- 一致连续性的定义（度量空间版本）
def UniformlyContinuous' {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε

-- Heine-Cantor 定理：紧致度量空间上的连续函数必一致连续
theorem heine_cantor {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] {f : X → Y} (hf : Continuous f) :
    UniformlyContinuous' f := by
  /- Mathlib4 中的标准证明 -/
  have huc : UniformContinuous f := by
    apply CompactSpace.uniformContinuous_of_continuous hf
  /- 将拓扑学的一致连续转换为度量空间版本 -/
  rw [Metric.uniformContinuous_iff] at huc
  exact huc

-- 闭区间上的连续函数一致连续（经典版本）
theorem heine_cantor_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b →
      |x - y| < δ → |f x - f y| < ε := by
  /- 利用闭区间的紧致性和 Heine-Cantor 定理 -/
  have hcomp : IsCompact (Icc a b) := isCompact_Icc
  /- 将连续延拓到整个空间后应用定理，或直接用局部紧致性 -/
  sorry  -- 需要利用紧致集上的连续性推导一致连续性

end HeineCantorTheorem
