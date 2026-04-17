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
    have h : ∀ᶠ n in atTop, |a (n + 1) / a n| < r := by
      apply hlim.eventually_lt_const
      exact hLr
    simp [Filter.eventually_atTop] at h ⊢
    exact h
  rcases hN with ⟨N, hN⟩
  /- 定义 b n = |a (N + n)|，则 b (n+1) ≤ r * b n -/
  let b := fun n => |a (N + n)|
  have hb0 : b 0 ≠ 0 := by
    simp [b]
    exact ha N
  /- 证明 b (n+1) ≤ r * b n -/
  have h_ratio : ∀ n, b (n + 1) ≤ r * b n := by
    intro n
    simp [b]
    have h1 : |a (N + n + 1)| = |a (N + n + 1) / a (N + n)| * |a (N + n)| := by
      field_simp [ha (N + n)]
    rw [h1]
    have h2 : |a (N + n + 1) / a (N + n)| < r := hN (N + n) (by linarith)
    have h3 : |a (N + n + 1) / a (N + n)| * |a (N + n)| ≤ r * |a (N + n)| := by
      apply mul_le_mul_of_nonneg_right
      · linarith [h2.le]
      · exact abs_nonneg (a (N + n))
    exact h3
  /- 由归纳法，b n ≤ b 0 * r^n -/
  have h_bound : ∀ n, b n ≤ b 0 * r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : b (n + 1) ≤ r * b n := h_ratio n
      have h2 : r * b n ≤ r * (b 0 * r ^ n) := mul_le_mul_of_nonneg_left ih (by linarith)
      have h3 : r * (b 0 * r ^ n) = b 0 * r ^ (n + 1) := by ring
      linarith [h1, h2, h3]
  /- 所以 |a (N + n)| ≤ |a N| * r^n -/
  have h_abs_bound : ∀ n, |a (N + n)| ≤ |a N| * r ^ n := by
    intro n
    simpa [b] using h_bound n
  /- 证明 Summable (fun n => a (N + n)) -/
  have h_tail : Summable (fun n => a (N + n)) := by
    apply summable_of_norm_bounded (fun n => |a N| * r ^ n)
    · -- 证明几何级数收敛
      simpa using summable_geometric_of_norm_lt_one (by linarith)
    · -- 证明 |a (N + n)| ≤ |a N| * r^n
      intro n
      simp
      exact h_abs_bound n
  /- 尾部收敛则整体收敛 -/
  exact (summable_nat_add_iff N).mp h_tail

-- 根值判别法（简化版本：从n=1开始避免1/0问题）
theorem root_test {a : ℕ → ℝ} {L : ℝ} (hL : L < 1)
    (hlim : Tendsto (fun n : ℕ => (|a (n + 1)|) ^ (1 / (n + 1 : ℝ))) atTop (𝓝 L)) :
    Summable a := by
  /- 类似比值判别法的策略 -/
  have hr : ∃ r : ℝ, L < r ∧ r < 1 := by
    use (L + 1) / 2
    constructor <;> linarith
  rcases hr with ⟨r, hLr, hr1⟩
  /- 由极限定义，存在 N 使得当 n ≥ N 时 |a (n+1)|^(1/(n+1)) < r -/
  have hN : ∃ N : ℕ, ∀ n ≥ N, (|a (n + 1)|) ^ (1 / (n + 1 : ℝ)) < r := by
    have h : ∀ᶠ n in atTop, (|a (n + 1)|) ^ (1 / (n + 1 : ℝ)) < r := by
      apply hlim.eventually_lt_const
      exact hLr
    simp [Filter.eventually_atTop] at h ⊢
    exact h
  rcases hN with ⟨N, hN⟩
  /- 当 n ≥ N 时，|a (n+1)| < r^(n+1) -/
  have h_bound : ∀ n ≥ N, |a (n + 1)| ≤ r ^ (n + 1 : ℝ) := by
    intro n hn
    have h1 : (|a (n + 1)| : ℝ) ^ (1 / (n + 1 : ℝ)) < r := hN n hn
    have h2 : |a (n + 1)| = ((|a (n + 1)| : ℝ) ^ (1 / (n + 1 : ℝ))) ^ (n + 1 : ℝ) := by
      rw [← Real.rpow_mul]
      field_simp
      exact abs_nonneg (a (n + 1))
    rw [h2]
    have h3 : ((|a (n + 1)| : ℝ) ^ (1 / (n + 1 : ℝ))) ^ (n + 1 : ℝ) ≤ r ^ (n + 1 : ℝ) := by
      apply Real.rpow_le_rpow
      · exact Real.rpow_nonneg (abs_nonneg (a (n + 1))) (1 / (n + 1 : ℝ))
      · linarith [h1.le]
      · exact Nat.cast_nonneg' (n + 1)
    exact h3
  have h_bound' : ∀ n ≥ N, |a (n + 1)| ≤ r ^ (n + 1) := by
    intro n hn
    specialize h_bound n hn
    have : r ^ (n + 1 : ℝ) = r ^ (n + 1) := by rw [Real.rpow_natCast]
    linarith [h_bound, this]
  /- 证明 Summable a -/
  have h0 : Summable (fun n => a (n + 1)) := by
    apply summable_of_norm_bounded (fun n => if n < N then |a (n + 1)| else r ^ (n + 1))
    · -- 证明控制级数收敛
      have h1 : Summable (fun n => if n < N then |a (n + 1)| else r ^ (n + 1)) := by
        apply summable_nat_add_iff N |>.mp
        simp [summable_geometric_of_norm_lt_one (by linarith)]
      exact h1
    · -- 证明 |a (n+1)| ≤ 控制级数
      intro n
      simp
      by_cases hn : n < N
      · simp [hn]
      · simp [hn]
        exact h_bound' n (by linarith)
  /- 由 a 0 + Σ a (n+1) 收敛 -/
  exact (summable_nat_add_iff 1).mp h0

end SeriesConvergenceTests
