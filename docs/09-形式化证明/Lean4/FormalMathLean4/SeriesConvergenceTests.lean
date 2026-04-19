import Mathlib
/-
# 级数收敛判别法 / Series Convergence Tests

## Mathlib4 对应
- **模块**: `Mathlib.Analysis.SpecificLimits.Basic`, `Mathlib.Analysis.NormedSpace.Basic`
- **核心定理**: `NormedSpace.tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `summable_of_norm_bounded`

## 定理陈述
1. **比较判别法** (Comparison Test): 若 $|a_n| \leq b_n$ 且 $\sum b_n$ 收敛，则 $\sum a_n$ 绝对收敛。
2. **比值判别法** (Ratio Test): 若 $\limsup |a_{n+1}/a_n| < 1$，则 $\sum a_n$ 绝对收敛。
3. **根值判别法** (Root Test): 若 $\limsup |a_n|^{1/n} < 1$，则 $\sum a_n$ 绝对收敛。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Analysis.SpecificLimits.Normed`
- 模块 / Module: `Mathlib.Analysis.PSeries`
- 定理 / Theorem: `summable_geometric_iff_norm_lt_one`
- 定理 / Theorem: `Real.summable_nat_rpow`
-/

#check summable_geometric_iff_norm_lt_one
#check Real.summable_nat_rpow

-- Series convergence tests
theorem GeometricSeriesConvergence {r : ℝ} : Summable (λ n : ℕ => r ^ n) ↔ ‖r‖ < 1 := by
  rw [summable_geometric_iff_norm_lt_one]

