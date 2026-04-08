/-
# 二项式定理的形式化证明 / Binomial Theorem

## Mathlib4对应
- **模块**: `Mathlib.Data.Nat.Choose.Basic`, `Mathlib.Algebra.BigOperators.Ring`
- **核心定理**: `add_pow`
- **相关定义**:
  - `Nat.choose`: 二项式系数
  - `Finset.sum`: 有限和

## 定理陈述

对于任意 a, b ∈ ℝ 和 n ∈ ℕ：

    (a + b)ⁿ = ∑ₖ₌₀ⁿ C(n,k) · aᵏ · bⁿ⁻ᵏ

其中 C(n,k) = n!/(k!(n-k)!) 是二项式系数。

## 数学意义

二项式定理是代数学的基础定理，在组合数学、概率论和微积分中有广泛应用。

## 证明复杂度分析
- **难度等级**: P1 (本科基础)
- **证明行数**: ~150行
- **关键引理**: 4个
- **主要策略**: 数学归纳法 + 组合恒等式
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

universe u

namespace BinomialTheorem

open Nat BigOperators Finset

/-
## 第一部分：二项式系数的基本性质
-/

-- 二项式系数的对称性
theorem choose_symm (n k : ℕ) (hk : k ≤ n) :
    choose n k = choose n (n - k) := by
  rw [choose_symm_of_le_sub]
  omega

-- 帕斯卡恒等式
theorem pascal_identity (n k : ℕ) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  exact choose_succ_succ n k

/-
## 第二部分：二项式定理

**定理**: (a + b)ⁿ = ∑ₖ C(n,k) · aᵏ · bⁿ⁻ᵏ

**证明**（数学归纳法）:
1. 基础：n = 0 时，两边都等于1
2. 归纳：假设对n成立，证明对n+1成立
   (a + b)ⁿ⁺¹ = (a + b)·(a + b)ⁿ
              = (a + b)·∑ₖ C(n,k)·aᵏ·bⁿ⁻ᵏ
              = ... （利用帕斯卡恒等式）
              = ∑ₖ C(n+1,k)·aᵏ·bⁿ⁺¹⁻ᵏ
-/

-- 二项式定理（实数版本）
theorem binomial_theorem (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k in range (n + 1), choose n k * a ^ k * b ^ (n - k) := by
  /- 使用Mathlib4的add_pow定理 -/
  rw [add_pow a b n]
  /- 化简表达式 -/
  simp [mul_comm]

-- 二项式定理的另一种表述
theorem binomial_theorem' (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k in range (n + 1), (choose n k : ℝ) * a ^ k * b ^ (n - k) := by
  exact binomial_theorem a b n

/-
## 第三部分：特殊情形

### (1 + 1)ⁿ = 2ⁿ
theorem sum_binomial_eq_two_pow (n : ℕ) :
    ∑ k in range (n + 1), choose n k = 2 ^ n := by
  /- 在二项式定理中取 a = b = 1 -/
  have h := binomial_theorem (1 : ℝ) 1 n
  simp at h
  norm_cast at h
  exact h

-- 二项式系数的交错和
theorem alternating_sum_binomial (n : ℕ) (hn : n > 0) :
    ∑ k in range (n + 1), (-1 : ℝ) ^ k * choose n k = 0 := by
  /- 在二项式定理中取 a = -1, b = 1 -/
  have h := binomial_theorem (-1 : ℝ) 1 n
  have h_zero : (-1 + 1 : ℝ) ^ n = 0 := by
    simp
    rw [zero_pow (by omega)]
  rw [h_zero] at h
  have h_eq : ∑ k in range (n + 1), choose n k * (-1) ^ k * (1 : ℝ) ^ (n - k) = 0 := by
    simpa using h
  /- 化简 -/
  simp at h_eq
  have : ∑ k in range (n + 1), (-1 : ℝ) ^ k * choose n k =
         ∑ k in range (n + 1), choose n k * (-1) ^ k := by
    apply sum_congr rfl
    intro k hk
    ring
  rw [this]
  exact h_eq

/-
## 第四部分：组合恒等式
-/

-- 范德蒙德卷积（简化版）
theorem vandermonde_identity (m n r : ℕ) (hr : r ≤ m + n) :
    choose (m + n) r = ∑ k in range (r + 1), choose m k * choose n (r - k) := by
  /- 组合解释：从m+n个元素中选r个
     = 从m个选k个，从n个选r-k个，对所有k求和 -/
  exact Nat.choose_add_choose m n r hr

-- 二项式系数的平方和
theorem sum_choose_square (n : ℕ) :
    ∑ k in range (n + 1), choose n k ^ 2 = choose (2 * n) n := by
  /- 利用范德蒙德卷积，取 m = n, r = n -/
  have h := vandermonde_identity n n n (by omega)
  /- 化简 -/
  have h1 : ∑ k in range (n + 1), choose n k * choose n (n - k) = choose (2 * n) n := by
    simpa using h
  /- 利用对称性 C(n,k) = C(n,n-k) -/
  have h2 : ∑ k in range (n + 1), choose n k ^ 2 =
            ∑ k in range (n + 1), choose n k * choose n (n - k) := by
    apply sum_congr rfl
    intro k hk
    have h_sym : choose n (n - k) = choose n k := by
      apply choose_symm
      simp at hk
      omega
    rw [h_sym]
    ring
  rw [h2, h1]

end BinomialTheorem

/-
## 数学意义

二项式定理的重要性：

1. **代数基础**：多项式展开的核心工具
2. **组合数学**：二项式系数有组合解释
3. **概率论**：二项分布的基础
4. **微积分**：泰勒展开的基础

## 历史背景

- 古代：二项式系数出现在帕斯卡三角
- 1665：牛顿推广到分数指数
- 现代：广泛应用于数学各领域

## 相关定理链接

- [费马小定理](./FermatLittleTheorem.lean) - 数论应用
- [拉格朗日插值](./07-拉格朗日插值.lean) - 多项式理论
- [泰勒定理](./09-罗尔定理.lean) - 分析学推广
-/
