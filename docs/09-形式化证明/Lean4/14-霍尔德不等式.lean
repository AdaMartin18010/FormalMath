/-
# 霍尔德不等式 / Hölder's Inequality

## Mathlib4对应
- **模块**: `Mathlib.Analysis.MeanInequalities`
- **核心定理**: `Real.inner_le_Lp_mul_Lq`
- **相关定义**:
  - `Lp`范数
  - ` NNReal`: 非负实数

## 定理陈述

### 离散形式
对于 p, q > 1 且 1/p + 1/q = 1，以及序列 aᵢ, bᵢ ≥ 0：

    ∑ |aᵢ·bᵢ| ≤ (∑ |aᵢ|ᵖ)^(1/p) · (∑ |bᵢ|^q)^(1/q)

### 积分形式
对于可测函数 f, g：

    ∫|f·g| dμ ≤ (∫|f|ᵖ dμ)^(1/p) · (∫|g|^q dμ)^(1/q)

## 数学意义

霍尔德不等式是分析学中最基本的不等式之一，是柯西-施瓦茨不等式的推广。

## 证明复杂度分析
- **难度等级**: P2 (本科高级)
- **证明行数**: ~180行
- **关键引理**: 4个
- **主要策略**: 杨氏不等式 + 凸函数方法
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HolderInequality

open Real Finset BigOperators

/-
## 第一部分：杨氏不等式

**定理**: 对于 a, b ≥ 0，p, q > 1，1/p + 1/q = 1：
    a·b ≤ aᵖ/p + b^q/q
-/

-- 杨氏不等式
theorem young_inequality (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1) :
    a * b ≤ (a^p)/p + (b^q)/q := by
  /- 使用Mathlib4的Real.geom_mean_le_arith_mean2_weighted -/
  by_cases ha0 : a = 0
  · rw [ha0]; simp; positivity
  by_cases hb0 : b = 0
  · rw [hb0]; simp; positivity
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < q := by linarith
  have h1 : a * b = (a^p) ^ (1/p) * (b^q) ^ (1/q) := by
    rw [← Real.rpow_mul, ← Real.rpow_mul]
    · field_simp
    · positivity
    · positivity
  rw [h1]
  have h2 : (a^p) ^ (1/p) * (b^q) ^ (1/q) ≤ (1/p) * (a^p) + (1/q) * (b^q) := by
    apply Real.geom_mean_le_arith_mean2_weighted
    · positivity
    · positivity
    · exact hpq
    · positivity
    · positivity
  have h3 : (1/p) * (a^p) + (1/q) * (b^q) = (a^p)/p + (b^q)/q := by ring
  linarith [h2, h3]

/-
## 第二部分：霍尔德不等式

**定理**: ∑ |aᵢ·bᵢ| ≤ (∑ |aᵢ|ᵖ)^(1/p) · (∑ |bᵢ|^q)^(1/q)
-/

-- 离散霍尔德不等式（归一化版本）
theorem holder_normalized {n : ℕ} (a b : Fin n → ℝ) 
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1)
    (ha : ∑ i, |a i| ^ p = 1) (hb : ∑ i, |b i| ^ q = 1) :
    ∑ i, |a i * b i| ≤ 1 := by
  /- 对每个 i 应用杨氏不等式，然后求和 -/
  calc
    ∑ i, |a i * b i| = ∑ i, |a i| * |b i| := by
      simp [abs_mul]
    _ ≤ ∑ i, ((|a i| ^ p)/p + (|b i| ^ q)/q) := by
      apply sum_le_sum
      intro i hi
      apply young_inequality
      · apply abs_nonneg
      · apply abs_nonneg
      · exact hp
      · exact hq
      · exact hpq
    _ = (∑ i, |a i| ^ p)/p + (∑ i, |b i| ^ q)/q := by
      simp [Finset.sum_add_distrib, Finset.sum_div]
    _ = 1/p + 1/q := by
      rw [ha, hb]
    _ = 1 := by
      exact hpq

-- 一般霍尔德不等式
theorem holder_inequality {n : ℕ} (a b : Fin n → ℝ)
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1) :
    ∑ i, |a i * b i| ≤ (∑ i, |a i| ^ p) ^ (1/p) * (∑ i, |b i| ^ q) ^ (1/q) := by
  /- 使用Mathlib4的Real.inner_le_Lp_mul_Lq -/
  have h := Real.inner_le_Lp_mul_Lq (Finset.univ) (fun i => |a i|) (fun i => |b i|) hp hq hpq
  simp at h ⊢
  have h_abs : ∑ i, |a i * b i| = ∑ i, |a i| * |b i| := by
    simp [abs_mul]
  rw [h_abs]
  exact h

/-
## 第三部分：柯西-施瓦茨不等式

霍尔德不等式在 p = q = 2 时就是柯西-施瓦茨不等式。
-/

-- 柯西-施瓦茨不等式（霍尔德的特例）
theorem cauchy_schwarz_from_holder {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, |a i * b i|) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
  /- 取 p = q = 2 -/
  have h := holder_inequality a b (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2) (by norm_num)
  /- 化简 |a_i|^2 = a_i^2 -/
  have h_simplify : ∀ a : ℝ, |a| ^ (2 : ℝ) = a ^ 2 := by
    intro a
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num]
    rw [Real.rpow_natCast, abs_pow, pow_two]
    simp
  have h_a : ∑ i, |a i| ^ (2 : ℝ) = ∑ i, (a i) ^ 2 := by
    simp [h_simplify]
  have h_b : ∑ i, |b i| ^ (2 : ℝ) = ∑ i, (b i) ^ 2 := by
    simp [h_simplify]
  rw [h_a, h_b] at h
  have h2 : ((∑ i, (a i) ^ 2) ^ (1 / (2 : ℝ))) ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    · norm_num
    · apply sum_nonneg
      intro i hi
      exact sq_nonneg (a i)
  have h3 : ((∑ i, (b i) ^ 2) ^ (1 / (2 : ℝ))) ^ 2 = ∑ i, (b i) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    · norm_num
    · apply sum_nonneg
      intro i hi
      exact sq_nonneg (b i)
  nlinarith [h, h2, h3, sq_nonneg (∑ i, |a i * b i|), sq_nonneg ((∑ i, (a i) ^ 2) ^ (1 / (2 : ℝ)) * (∑ i, (b i) ^ 2) ^ (1 / (2 : ℝ)))]

/-
## 第四部分：闵可夫斯基不等式

**定理**: L^p范数满足三角不等式

    ||f + g||_p ≤ ||f||_p + ||g||_p
-/

-- 闵可夫斯基不等式
theorem minkowski_inequality {n : ℕ} (a b : Fin n → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, |a i + b i| ^ p) ^ (1/p) ≤ (∑ i, |a i| ^ p) ^ (1/p) + (∑ i, |b i| ^ p) ^ (1/p) := by
  /- 使用Mathlib4的Lp范数三角不等式 -/
  by_cases hp1 : p = 1
  · rw [hp1]
    simp
    calc
      ∑ i, |a i + b i| ≤ ∑ i, (|a i| + |b i|) := by
        apply sum_le_sum
        intro i hi
        exact abs_add (a i) (b i)
      _ = ∑ i, |a i| + ∑ i, |b i| := by rw [Finset.sum_add_distrib]
  · have hp_gt : 1 < p := by
      have : p ≠ 1 := hp1
      by_contra h
      push_neg at h
      have : p = 1 := by linarith
      contradiction
    /- 使用Mathlib4的Real.Lp_add_le -/
    apply Real.Lp_add_le
    · intro i; exact abs_nonneg (a i + b i)
    · intro i; exact abs_nonneg (a i)
    · intro i; exact abs_nonneg (b i)
    · linarith

end HolderInequality

/-
## 数学意义

霍尔德不等式的重要性：

1. **函数空间理论**: L^p空间的基础
2. **傅里叶分析**: 卷积和变换的估计
3. **概率论**: 矩不等式
4. **偏微分方程**: 先验估计

## 推广

- **多重霍尔德不等式**: 多个函数的推广
- **弱L^p空间**: 调和分析中的应用
- **向量值函数**: 巴拿赫空间值函数

## 相关定理链接

- [柯西-施瓦茨不等式](./CauchySchwarz.lean) - p=q=2的特例
- [琴生不等式](./13-琴生不等式.lean) - 凸函数理论
- [Minkowski不等式](./14-霍尔德不等式.lean) - L^p空间三角不等式
-/
