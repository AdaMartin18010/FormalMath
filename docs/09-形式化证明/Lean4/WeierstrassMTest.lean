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

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.UniformConvergence

namespace WeierstrassMTest

open Topology Filter BigOperators

-- Weierstrass M-判别法
theorem weierstrass_m_test {α β : Type*} [TopologicalSpace α] [NormedAddCommGroup β]
    {E : Set α} {f : ℕ → α → β} {M : ℕ → ℝ}
    (hM : ∀ n x, x ∈ E → ‖f n x‖ ≤ M n) (hsum : Summable M) :
    TendstoUniformlyOn (fun N x => ∑ n in Finset.range N, f n x)
      (fun x => ∑' n : ℕ, f n x) atTop E := by
  /- 这是一致收敛理论中的核心定理 -/
  apply tendstoUniformlyOn_tsum
  · intro n x hx
    exact hM n x hx
  · exact hsum

-- 推论：M-判别法保证和函数连续
theorem weierstrass_m_test_continuous {α β : Type*} [TopologicalSpace α] [NormedAddCommGroup β]
    {E : Set α} {f : ℕ → α → β} {M : ℕ → ℝ}
    (hM : ∀ n x, x ∈ E → ‖f n x‖ ≤ M n) (hsum : Summable M)
    (hf : ∀ n, ContinuousOn (f n) E) :
    ContinuousOn (fun x => ∑' n : ℕ, f n x) E := by
  /- 一致收敛的连续函数列的极限函数连续 -/
  sorry

end WeierstrassMTest
