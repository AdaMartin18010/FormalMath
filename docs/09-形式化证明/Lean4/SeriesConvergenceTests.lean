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

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace SeriesConvergenceTests

open NNReal BigOperators Topology

-- 比较判别法
theorem comparison_test {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hle : ∀ n, a n ≤ b n) (hsum : Summable b) : Summable a := by
  /- 使用非负项级数的比较判别法 -/
  apply Summable.of_nonneg_of_le ha hle hsum

-- 绝对收敛的比较判别法
theorem comparison_test_abs {a b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hle : ∀ n, |a n| ≤ b n) (hsum : Summable b) : Summable a := by
  /- 先证绝对收敛，再由绝对收敛推出收敛 -/
  have h_abs : Summable (fun n => |a n|) := by
    apply Summable.of_nonneg_of_le (fun n => abs_nonneg (a n)) hle hsum
  exact summable_of_abs_summable h_abs

-- 比值判别法（简化版本：设极限存在且小于1）
theorem ratio_test {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0)
    {L : ℝ} (hL : L < 1) (hlim : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 L)) :
    Summable a := by
  /- 利用极限小于1，存在N使得n≥N时 |a(n+1)/a(n)| < r 对某个r<1 -/
  have hr : ∃ r : ℝ, L < r ∧ r < 1 := by
    use (L + 1) / 2
    constructor <;> linarith
  rcases hr with ⟨r, hLr, hr1⟩
  /- 由极限定义，存在 N 使得当 n ≥ N 时不等式成立 -/
  have hN : ∃ N : ℕ, ∀ n ≥ N, |a (n + 1) / a n| < r := by
    rw [tendsto_iff_dist_tendsto_zero] at hlim
    /- 需要更细致地利用极限定义 -/
    sorry
  /- 由此可得 |a_{N+k}| ≤ |a_N| · r^k，再与几何级数比较 -/
  sorry

-- 根值判别法（简化版本）
theorem root_test {a : ℕ → ℝ} {L : ℝ} (hL : L < 1)
    (hlim : Tendsto (fun n => (|a n|) ^ (1 / n : ℝ)) atTop (𝓝 L)) :
    Summable a := by
  /- 类似比值判别法的策略 -/
  sorry

end SeriesConvergenceTests
