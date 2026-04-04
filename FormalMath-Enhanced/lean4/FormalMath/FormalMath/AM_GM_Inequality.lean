/-
# 算术-几何平均不等式 (AM-GM Inequality)

## 数学背景

算术-几何平均不等式（AM-GM不等式）是数学中最基本和最重要的不等式之一。
它连接了算术平均和几何平均两个基本平均概念。

## 不等式陈述

对于非负实数 a₁, a₂, ..., aₙ：

(a₁ + a₂ + ... + aₙ) / n ≥ ⁿ√(a₁·a₂·...·aₙ)

等号成立当且仅当 a₁ = a₂ = ... = aₙ。

## 特殊情形

- n = 2: (a + b)/2 ≥ √(ab)
- n = 3: (a + b + c)/3 ≥ ³√(abc)

## 应用

- 优化问题
- 几何不等式
- 概率论
- 信息论

## Mathlib4对应
- `Mathlib.Analysis.MeanInequalities`
- `Mathlib.Analysis.Convex.SpecificFunctions.Basic`

本文件建立AM-GM不等式及其应用。
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Real.Basic

namespace AMGMInequality

open Real Finset BigOperators

/-
## 两个数的AM-GM不等式

**定理**：对于非负实数 a, b，有 (a + b)/2 ≥ √(ab)

等号成立当且仅当 a = b。

**证明思路**：
考虑 (√a - √b)² ≥ 0
展开得：a + b - 2√(ab) ≥ 0
因此：(a + b)/2 ≥ √(ab)

等号成立当且仅当 √a = √b，即 a = b。
-/
theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ √(a * b) := by
  -- 使用Mathlib中的标准结果
  have h : (a + b) / 2 ≥ √(a * b) := by
    -- 利用凸性证明
    have h_convex : √(a * b) ≤ (a + b) / 2 := by
      -- 利用ln的凹性和Jensen不等式
      -- 或直接使用代数方法
      sorry -- 需要详细证明
    linarith
  exact h

/-
## 两个数AM-GM等号条件

**定理**：(a + b)/2 = √(ab) 当且仅当 a = b
-/
theorem am_gm_two_eq_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 = √(a * b) ↔ a = b := by
  constructor
  · -- 证明：等号成立 ⇒ a = b
    intro h_eq
    -- 由证明过程，等号成立当且仅当 (√a - √b)² = 0
    have h1 : (√a - √b) ^ 2 = 0 := by
      -- 从等式反推
      have h2 : √a * √b = √(a * b) := by
        rw [Real.sqrt_mul ha]
      have h3 : (a + b) / 2 - √(a * b) = 0 := by linarith
      -- 利用恒等式 (a+b)/2 - √(ab) = (√a - √b)²/2
      sorry -- 需要代数恒等式
    -- 因此 √a = √b
    have h4 : √a - √b = 0 := by
      apply pow_eq_zero
      exact h1
    -- 所以 a = b
    have h5 : √a = √b := by linarith
    have h6 : a = b := by
      rw [← Real.sq_sqrt ha, ← Real.sq_sqrt hb, h5]
    exact h6
  · -- 证明：a = b ⇒ 等号成立
    intro h_eq
    rw [h_eq]
    -- 显然，当 a = b 时，(a+a)/2 = a = √(a²) = a
    have h1 : √(b * b) = b := by
      have h2 : b * b = b ^ 2 := by ring
      rw [h2]
      rw [Real.sqrt_sq (by linarith)]
    linarith [h1]

/-
## n个数的AM-GM不等式

**定理**：对于非负实数 a₁, a₂, ..., aₙ，有

(a₁ + a₂ + ... + aₙ) / n ≥ ⁿ√(a₁·a₂·...·aₙ)

**证明思路**（使用ln的凹性）：

考虑函数 f(x) = ln(x)，它在 (0, ∞) 上是凹函数。

由Jensen不等式：
ln((a₁ + ... + aₙ)/n) ≥ (ln(a₁) + ... + ln(aₙ))/n
                           = ln((a₁·...·aₙ)^{1/n})

由于ln是增函数，因此：
(a₁ + ... + aₙ)/n ≥ (a₁·...·aₙ)^{1/n}
-/
theorem am_gm_n {n : ℕ} (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i) / n ≥ (∏ i, a i) ^ (1 / n : ℝ) := by
  -- 处理 a_i = 0 的情况
  by_cases h_all_pos : ∀ i, 0 < a i
  · -- 所有 a_i > 0，可以使用ln
    -- 利用ln的凹性和Jensen不等式
    sorry -- 需要详细证明
  · -- 某些 a_i = 0
    push_neg at h_all_pos
    rcases h_all_pos with ⟨i, hi⟩
    -- 此时右边为0
    have h_prod_zero : ∏ i, a i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      linarith
    -- 左边 ≥ 0，右边 = 0
    rw [h_prod_zero]
    have h_right_zero : (0 : ℝ) ^ (1 / n : ℝ) = 0 := by
      -- 对于 n > 0，0^{1/n} = 0
      sorry -- 需要幂函数性质
    rw [h_right_zero]
    -- 证明左边 ≥ 0
    have h_left_nonneg : (∑ i, a i) / n ≥ 0 := by
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro i hi
        exact ha i
      · exact Nat.cast_nonneg n
    linarith

/-
## n个数AM-GM等号条件

**定理**：等号成立当且仅当所有 a_i 相等。
-/
theorem am_gm_n_eq_iff {n : ℕ} (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∑ i, a i) / n = (∏ i, a i) ^ (1 / n : ℝ) ↔ 
    ∀ i j, a i = a j := by
  constructor
  · -- 证明：等号成立 ⇒ 所有 a_i 相等
    intro h_eq
    -- 利用Jensen不等式的等号条件
    -- ln严格凹，等号成立当且仅当所有点相同
    sorry -- 需要利用严格凹性
  · -- 证明：所有 a_i 相等 ⇒ 等号成立
    intro h_eq
    -- 设所有 a_i = c
    have h_const : ∃ c, ∀ i, a i = c := by
      -- 从所有元素相等得到常数
      sorry -- 需要构造常数
    rcases h_const with ⟨c, hc⟩
    -- 计算两边
    have h_left : (∑ i, a i) / n = c := by
      simp [hc]
      field_simp
    have h_right : (∏ i, a i) ^ (1 / n : ℝ) = c := by
      simp [hc]
      -- c^n^{1/n} = c
      sorry -- 需要幂函数性质
    rw [h_left, h_right]

/-
## 加权AM-GM不等式

**定理**：对于正权重 w₁, ..., wₙ 满足 ∑wᵢ = 1，有

∑ wᵢaᵢ ≥ ∏ aᵢ^{wᵢ}

**证明**：同样利用ln的凹性和Jensen不等式
-/
theorem weighted_am_gm {n : ℕ} (hn : n > 0) (a w : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 < w i)
    (h_sum : ∑ i, w i = 1) :
    ∑ i, w i * a i ≥ ∏ i, (a i) ^ (w i) := by
  -- 利用ln的凹性
  -- ln(∑ wᵢaᵢ) ≥ ∑ wᵢln(aᵢ) = ln(∏ aᵢ^{wᵢ})
  sorry -- 需要详细证明

/-
## 应用：Young不等式

**定理**：对于 p, q > 1 满足 1/p + 1/q = 1，以及非负实数 a, b：

ab ≤ a^p/p + b^q/q

**证明**：利用加权AM-GM不等式
-/
theorem young_inequality (p q : ℝ) (hp : p > 1) (hq : q > 1)
    (h_conj : 1 / p + 1 / q = 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  -- 利用加权AM-GM
  -- ab = (a^p)^{1/p} (b^q)^{1/q} ≤ (1/p)a^p + (1/q)b^q
  sorry -- 需要详细证明

/-
## 应用：Hölder不等式

**定理**：对于 p, q > 1 满足 1/p + 1/q = 1：

∑|aᵢbᵢ| ≤ (∑|aᵢ|^p)^{1/p} (∑|bᵢ|^q)^{1/q}

**证明**：利用Young不等式
-/
theorem holder_inequality {n : ℕ} (p q : ℝ) (hp : p > 1) (hq : q > 1)
    (h_conj : 1 / p + 1 / q = 1) (a b : Fin n → ℝ) :
    ∑ i, |a i * b i| ≤ 
    (∑ i, |a i| ^ p) ^ (1 / p : ℝ) * 
    (∑ i, |b i| ^ q) ^ (1 / q : ℝ) := by
  -- 对每个 i 应用Young不等式
  -- 然后求和并整理
  sorry -- 需要详细证明

/-
## 应用：算术-调和平均不等式

**定理**：对于正实数 a₁, ..., aₙ：

(a₁ + ... + aₙ)/n ≥ n/(1/a₁ + ... + 1/aₙ)

**证明**：对 1/aᵢ 应用AM-GM不等式
-/
theorem ah_inequality {n : ℕ} (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∑ i, a i) / n ≥ n / (∑ i, (a i)⁻¹) := by
  -- 对 1/aᵢ 应用AM-GM
  -- (1/a₁ + ... + 1/aₙ)/n ≥ ⁿ√(1/(a₁·...·aₙ))
  -- 取倒数并整理
  sorry -- 需要详细证明

/-
## 应用：幂平均不等式

**定理**：对于 r < s，r-幂平均 ≤ s-幂平均

M_r = ((a₁^r + ... + aₙ^r)/n)^{1/r}

特别地：
- r = -1: 调和平均
- r = 0（极限）: 几何平均
- r = 1: 算术平均
- r = 2: 平方平均

调和平均 ≤ 几何平均 ≤ 算术平均 ≤ 平方平均
-/
def powerMean {n : ℕ} (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (r : ℝ) (hr : r ≠ 0) : ℝ :=
  ((∑ i, (a i) ^ r) / n) ^ (1 / r : ℝ)

theorem power_mean_inequality {n : ℕ} (hn : n > 0) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_rs : r < s) :
    powerMean hn a ha r hr ≤ powerMean hn a ha s hs := by
  -- 利用凸性证明
  -- 函数 x ↦ x^{s/r} 是凸函数（当 s/r > 1 时）
  sorry -- 需要详细证明

end AMGMInequality
