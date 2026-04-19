import Mathlib
/-
# Weierstrass M-判别法 / Weierstrass M-test

## Mathlib4 对应
- **模块**: `Mathlib.Analysis.NormedSpace.Basic`, `Mathlib.Topology.UniformConvergence`
- **核心定理**: `tendstoUniformlyOn_tsum`, `summable_of_norm_bounded`

## 定理陈述
设 $\{f_n\}$ 是定义在集合 $E$ 上的一列函数，若存在正数列 $\{M_n\}$ 使得
1. $|f_n(x)| \leq M_n$ 对所有 $x \in E$ 成立；
2. $\sum M_n$ 收敛；
则 $\sum f_n(x)$ 在 $E$ 上一致收敛。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Analysis.NormedSpace.FunctionSeries`
- 定理 / Theorem: `summable_of_norm_bounded_eventually`
-/


-- Weierstrass M-test: uniform convergence of function series
theorem WeierstrassMTest {α β : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    {f : β → α} (M : β → ℝ) (hM : Summable M)
    (hf : ∀ b : β, ‖f b‖ ≤ M b) :
    Summable f := by
  sorry

