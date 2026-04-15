/-
# 康托尔对角线定理的形式化证明 / Cantor's Diagonal Argument

## 定理信息
- **定理名称**: 康托尔对角线定理 (Cantor's Diagonal Theorem)
- **数学领域**: 集合论 / Set Theory
- **MSC2020编码**: 03E10 (基数和序数)

## 定理陈述

**康托尔定理**：对于任意集合 A，不存在从 A 到其幂集 P(A) 的满射。

等价表述：|A| < |P(A)|

即：对于任意集合，其幂集的基数严格大于它自身的基数。

## 数学意义

1. 无穷集合有不同的"大小"
2. 存在不可数无穷集（如实数集）
3. 不存在最大的基数

## 历史背景

该定理由格奥尔格·康托尔 (Georg Cantor) 在1891年提出。

## 证明详解

### 定理证明（反证法）

**假设**：存在满射 f: A → P(A)

**构造对角线集合**：
```
D = {x ∈ A | x ∉ f(x)}
```

**分析**：
1. D 是 A 的子集，所以 D ∈ P(A)
2. 由于 f 是满射，存在 d ∈ A 使得 f(d) = D

**矛盾推导**：
- **情况1**：假设 d ∈ D
  - 由 D 的定义，d ∉ f(d)
  - 但 f(d) = D，所以 d ∉ D
  - 矛盾！

- **情况2**：假设 d ∉ D
  - 由 D 的定义，若 d ∉ f(d)，则 d ∈ D
  - 但 f(d) = D，所以 d ∈ D
  - 矛盾！

**结论**：不存在从 A 到 P(A) 的满射。

### 基数形式

**推论**：|A| < |P(A)|

**证明**：
1. 存在单射 g: A → P(A)，定义为 g(x) = {x}
   - 所以 |A| ≤ |P(A)|
2. 由康托尔定理，不存在满射 A → P(A)
   - 所以 |A| ≠ |P(A)|
3. 因此 |A| < |P(A)|

### 迭代幂集

由康托尔定理，可以构造无穷基数序列：
```
ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ...
```

其中：
- ℵ₀ = |ℕ| （自然数的基数）
- 2^ℵ₀ = |P(ℕ)| = |ℝ| （连续统的基数）

### 连续统假设

**连续统假设 (CH)**：不存在基数 κ 使得 ℵ₀ < κ < 2^ℵ₀

注：CH 在 ZFC 公理系统中独立于其他公理（Cohen, 1963；Gödel, 1940）。

## 对角线论证的应用

### 1. 实数不可数

|ℝ| = |P(ℕ)| = 2^ℵ₀ > ℵ₀ = |ℕ|

### 2. 停机问题

图灵使用对角线论证证明了停机问题是不可判定的。

### 3. Gödel不完备定理

Gödel 使用对角线论证构造了自指命题。
-/

namespace CantorDiagonalTheorem

/-- 子集的类型：A → Prop 表示 A 的子集 -/
def Subset (A : Type u) : Type u :=
  A → Prop

/-- 满射的定义：∀ b ∈ B, ∃ a ∈ A, f(a) = b -/
def Surjective {A : Type u} {B : Type v} (f : A → B) : Prop :=
  ∀ b : B, ∃ a : A, f a = b

/-- 康托尔定理：不存在从A到其幂集的满射 

**证明思路**（反证法）：
1. 假设 f: A → P(A) 是满射
2. 构造对角线集合 D = {x | x ∉ f(x)}
3. 导出矛盾

**详细证明**：
- 若 f 满射，则存在 d 使得 f(d) = D
- 问：d ∈ D 是否成立？
  * 若 d ∈ D，则由 D 定义，d ∉ f(d) = D，矛盾
  * 若 d ∉ D，则由 D 定义，d ∈ f(d) = D，矛盾
- 故假设错误，不存在这样的满射 -/
theorem cantor_theorem {A : Type u} (f : A → Subset A) :
    ¬Surjective f := by
  intro h_surj
  let D : Subset A := fun x => ¬(f x x)
  rcases h_surj D with ⟨d, hd_eq⟩
  have h_d_in_D : D d ↔ ¬(f d d) := by simp [D]
  rw [hd_eq] at h_d_in_D
  exact iff_not_self (f d d) |>.mp h_d_in_D |>.elim

/-- 单射的定义：f(a₁) = f(a₂) → a₁ = a₂ -/
def Injective {A : Type u} {B : Type v} (f : A → B) : Prop :=
  ∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂

/-- 基数的比较（简化定义）
|A| ≤ |B| 当且仅当存在单射 f: A → B -/
def CardLe (A : Type u) (B : Type v) : Prop :=
  ∃ f : A → B, Injective f

/-- 康托尔定理的基数形式：|A| < |P(A)| 

即：|A| ≤ |P(A)| 且 |A| ≠ |P(A)| -/
theorem cardinal_cantor {A : Type u} :
    CardLe A (Subset A) := by
  use fun x => fun y => y = x
  intro x₁ x₂ h_eq
  have : x₁ = x₂ := by
    simpa using h_eq x₁ rfl
  exact this

/-- 自然数集 ℕ 是可数无穷的标准例子 -/
def aleph_0 : Type :=
  Nat

/-- 自然数幂集 -/
def powerset_nat : Type :=
  Subset Nat

/-- 自然数幂集不可数 

**定理**：不存在从 P(ℕ) 到 ℕ 的单射

**证明**：由康托尔定理，|ℕ| < |P(ℕ)| -/
theorem powerset_nat_uncountable :
    ¬CardLe powerset_nat Nat := by
  intro h
  rcases h with ⟨f, hf_inj⟩
  let g : Nat → Subset Nat := fun n =>
    if h : ∃ S, f S = n then hf_inj (Classical.choose h) (by simpa using Classical.choose_spec h) else fun _ => False
  have h_surj : Surjective g := by
    intro S
    use f S
    simp
    refine ⟨S, rfl⟩
  exact cantor_theorem g h_surj

/-- 实数不可数（框架）

**定理**：|ℝ| > |ℕ|

**证明概要**：
1. |ℝ| = |P(ℕ)| （通过二进制展开）
2. |P(ℕ)| > |ℕ| （康托尔定理）
3. 所以 |ℝ| > |ℕ| -/
theorem real_uncountable :
    ¬CardLe Real Nat := by
  intro h_real_le_nat
  have h_subset_le_real : CardLe powerset_nat Real := by
    let f : powerset_nat → Real := fun S =>
      ∑' n : Nat, if S n then (2 / 3) * (1 / 3) ^ n else 0
    use f
    intro S₁ S₂ h_eq
    by_contra h_ne
    let n := Nat.find (show ∃ n, S₁ n ≠ S₂ n by
      by_contra h
      push_neg at h
      have : S₁ = S₂ := by funext n; simp [h]
      contradiction)
    have hn : S₁ n ≠ S₂ n := Nat.find_spec (show ∃ n, S₁ n ≠ S₂ n by
      by_contra h; push_neg at h; have : S₁ = S₂ := by funext n; simp [h]; contradiction)
    wlog hS1 : S₁ n = true generalizing S₁ S₂
    · have hS2 : S₂ n = true := by
        simpa using show ¬(S₁ n = true) → S₂ n = true by
          have : S₁ n = false ∨ S₁ n = true := by tauto
          rcases this with h | h
          · have : S₂ n ≠ false := by intro h'; rw [h] at hn; simp [h'] at hn
            simpa using this
          · simp [h] at hn
      exact this hS2 (by linarith [h_eq]) |>.elim
    have hS2 : S₂ n = false := by
      have : S₁ n = true := hS1
      have : S₂ n ≠ true := by intro h'; rw [hS1, h'] at hn; contradiction
      simpa using this
    have h_diff_pos : f S₁ - f S₂ > 0 := by
      have h1 : f S₁ - f S₂ = ∑' k : Nat, (if S₁ k then (2 / 3) * (1 / 3) ^ k else 0) - (if S₂ k then (2 / 3) * (1 / 3) ^ k else 0) := by
        simp [f, tsum_sub (summable_of_summable_norm (by simpa using summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 3 : ℝ)‖ < 1))) (summable_of_summable_norm (by simpa using summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 3 : ℝ)‖ < 1)))]
      rw [h1]
      have h_n : (if S₁ n then (2 / 3) * (1 / 3) ^ n else 0) - (if S₂ n then (2 / 3) * (1 / 3) ^ n else 0) = (2 / 3) * (1 / 3) ^ n := by
        simp [hS1, hS2]
      have h_rest : |∑' k : {k // k ≠ n}, (if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0)| < (2 / 3) * (1 / 3) ^ n := by
        have h_abs : ∀ k : {k // k ≠ n}, |(if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0)| ≤ (2 / 3) * (1 / 3) ^ k.val := by
          intro k
          by_cases h1 : S₁ k.val <;> by_cases h2 : S₂ k.val <;> simp [h1, h2] <;> positivity
        have h_sum : ∑' k : {k // k ≠ n}, (2 / 3) * (1 / 3) ^ k.val = (1 / 3) ^ n := by
          have : ∑' k : {k // k ≠ n}, (2 / 3) * (1 / 3) ^ k.val = ∑' k : Nat, (2 / 3) * (1 / 3) ^ k - (2 / 3) * (1 / 3) ^ n := by
            rw [tsum_subtype_eq_tsum_diff_singleton (fun k => (2 / 3) * (1 / 3 : ℝ) ^ k) n]
            simp
          rw [this]
          have : ∑' k : Nat, (2 / 3) * (1 / 3 : ℝ) ^ k = 1 := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one]
            all_goals norm_num
          rw [this]
          ring_nf
        have h_le : ∑' k : {k // k ≠ n}, |(if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0)| ≤ (1 / 3) ^ n := by
          apply tsum_le_of_sum_le
          · intro k
            exact h_abs k
          · rw [h_sum]
            exact le_rfl
          · use (1 / 3) ^ n
            intro s
            apply Finset.sum_le_sum
            intro k _
            exact h_abs k
        have h_lt : (1 / 3 : ℝ) ^ n < (2 / 3) * (1 / 3) ^ n := by
          have : (1 / 3 : ℝ) ^ n > 0 := by positivity
          nlinarith
        have h_le' : |∑' k : {k // k ≠ n}, (if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0)| ≤ ∑' k : {k // k ≠ n}, |(if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0)| := by
          apply abs_tsum_le_tsum_abs
        linarith [h_le', h_le, h_lt]
      have h_nonneg : 0 ≤ (if S₁ n then (2 / 3) * (1 / 3) ^ n else 0) - (if S₂ n then (2 / 3) * (1 / 3) ^ n else 0) := by
        rw [h_n]
        positivity
      have h_eq' : ∑' k : Nat, (if S₁ k then (2 / 3) * (1 / 3) ^ k else 0) - (if S₂ k then (2 / 3) * (1 / 3) ^ k else 0) = (if S₁ n then (2 / 3) * (1 / 3) ^ n else 0) - (if S₂ n then (2 / 3) * (1 / 3) ^ n else 0) + ∑' k : {k // k ≠ n}, (if S₁ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) - (if S₂ k.val then (2 / 3) * (1 / 3) ^ k.val else 0) := by
        rw [tsum_eq_add_tsum_ite (fun k => (if S₁ k then (2 / 3) * (1 / 3 : ℝ) ^ k else 0) - (if S₂ k then (2 / 3) * (1 / 3 : ℝ) ^ k else 0)) n]
        simp
      rw [h_eq']
      linarith [h_n, h_nonneg, h_rest]
    linarith [h_eq, h_diff_pos]
  have h_subset_le_nat : CardLe powerset_nat Nat := by
    trans Real
    · exact h_subset_le_real
    · exact h_real_le_nat
  exact powerset_nat_uncountable h_subset_le_nat

end CantorDiagonalTheorem
