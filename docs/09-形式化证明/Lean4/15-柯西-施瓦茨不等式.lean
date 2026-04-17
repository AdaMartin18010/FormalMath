/-
# 柯西-施瓦茨不等式 / Cauchy-Schwarz Inequality

## Mathlib4对应
- **模块**: `Mathlib.Analysis.InnerProductSpace.Basic`
- **核心定理**: `inner_mul_inner_self_le`
- **相关定义**:
  - `InnerProductSpace`: 内积空间
  - `Norm`: 范数

## 定理陈述

### 向量形式
对于内积空间中的向量 u, v：

    |⟨u, v⟩|² ≤ ⟨u, u⟩ · ⟨v, v⟩

或等价地：

    |⟨u, v⟩| ≤ ||u|| · ||v||

等号成立当且仅当 u 和 v 线性相关。

### 求和形式
对于实数 aᵢ, bᵢ：

    (∑ aᵢ·bᵢ)² ≤ (∑ aᵢ²) · (∑ bᵢ²)

## 数学意义

柯西-施瓦茨不等式是内积理论的基础定理，在几何、分析和概率论中无处不在。

## 证明复杂度分析
- **难度等级**: P1 (本科基础)
- **证明行数**: ~120行
- **关键引理**: 3个
- **主要策略**: 二次型非负性
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CauchySchwarz

open Real Finset

/-
## 第一部分：求和形式的柯西-施瓦茨不等式
-/

-- 柯西-施瓦茨不等式（求和形式）
theorem cauchy_schwarz_sum {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
  /- 使用Mathlib4的Finset.sum_mul_sq_le_sq_mul_sq -/
  exact Finset.sum_mul_sq_le_sq_mul_sq a b

/-
## 第二部分：内积空间版本
-/

-- 柯西-施瓦茨不等式（内积空间版本）
theorem cauchy_schwarz_inner {E : Type*} [InnerProductSpace ℝ E] (u v : E) :
    |⟪u, v⟫_ℝ| ^ 2 ≤ ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ := by
  /- 使用Mathlib4的标准定理 -/
  apply real_inner_mul_inner_self_le

-- 范数形式
theorem cauchy_schwarz_norm {E : Type*} [InnerProductSpace ℝ E] (u v : E) :
    |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  /- 从内积形式导出 -/
  have h := cauchy_schwarz_inner u v
  have h_norm : ‖u‖ ^ 2 = ⟪u, u⟫_ℝ := by
    simp [norm_sq_eq_inner]
  have h_norm_v : ‖v‖ ^ 2 = ⟪v, v⟫_ℝ := by
    simp [norm_sq_eq_inner]
  nlinarith [h, h_norm, h_norm_v, sq_nonneg (‖u‖ * ‖v‖ - |⟪u, v⟫_ℝ|)]

/-
## 第三部分：等号条件

**定理**: 等号成立 ⟺ u 和 v 线性相关
-/

-- 等号条件
theorem cauchy_schwarz_eq_iff {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 = (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) ↔
    ∃ c, ∀ i, a i = c * (b i) := by
  constructor
  · -- 等号成立 ⇒ 线性相关
    intro h_eq
    /- 使用Mathlib4的等号条件 -/
    rcases Finset.sum_mul_sq_eq_sq_mul_sq_iff a b |>.mp h_eq with ⟨c, hc⟩
    use c
    exact hc
  · -- 线性相关 ⇒ 等号成立
    rintro ⟨c, hc⟩
    /- 直接验证 -/
    exact Finset.sum_mul_sq_eq_sq_mul_sq_iff a b |>.mpr ⟨c, hc⟩

/-
## 第四部分：应用

### 应用1：三角不等式
-/

theorem triangle_inequality_from_cs {n : ℕ} (a b : Fin n → ℝ) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2) := by
  /- 利用柯西-施瓦茨证明范数的三角不等式 -/
  have h1 : ∑ i, (a i + b i) ^ 2 = ∑ i, (a i) ^ 2 + 2 * (∑ i, a i * b i) + ∑ i, (b i) ^ 2 := by
    simp [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have h2 : (∑ i, a i * b i) ≤ Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2) := by
    have h := cauchy_schwarz_sum a b
    have h3 : (Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2)) ^ 2 =
      (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
      rw [mul_pow]
      rw [Real.sq_sqrt (by apply sum_nonneg; intro i hi; exact sq_nonneg (a i))]
      rw [Real.sq_sqrt (by apply sum_nonneg; intro i hi; exact sq_nonneg (b i))]
    nlinarith [h, h3, Real.sqrt_nonneg (∑ i, (a i) ^ 2), Real.sqrt_nonneg (∑ i, (b i) ^ 2)]
  have h3 : Real.sqrt (∑ i, (a i + b i) ^ 2) ^ 2 ≤ (Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) ^ 2 := by
    rw [h1]
    nlinarith [h2, Real.sq_sqrt (by apply sum_nonneg; intro i hi; exact sq_nonneg (a i)),
      Real.sq_sqrt (by apply sum_nonneg; intro i hi; exact sq_nonneg (b i))]
  have h4 : Real.sqrt (∑ i, (a i + b i) ^ 2) ≥ 0 := Real.sqrt_nonneg _
  have h5 : Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2) ≥ 0 := by positivity
  nlinarith [h3, h4, h5]

/-
### 应用2：方差不等式
-/

theorem variance_inequality (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 ≤ n * (∑ i, (x i) ^ 2) := by
  /- 对 aᵢ = 1, bᵢ = xᵢ 应用柯西-施瓦茨 -/
  let a : Fin n → ℝ := fun _ => 1
  have h := cauchy_schwarz_sum a x
  simp [a] at h
  simpa using h

end CauchySchwarz

/-
## 数学意义

柯西-施瓦茨不等式的重要性：

1. **内积空间基础**: 定义角度的理论基础
2. **几何解释**: |cos θ| ≤ 1 的代数表达
3. **概率论**: 协方差不等式
4. **量子力学**: 不确定性原理

## 推广

- **积分形式**: 函数内积
- **矩阵形式**: 弗罗贝尼乌斯内积
- **概率形式**: 协方差不等式

## 历史背景

- 1821: 柯西提出
- 1859: 布尼亚科夫斯基推广到积分
- 1888: 施瓦茨推广到内积空间

## 相关定理链接

- [霍尔德不等式](./14-霍尔德不等式.lean) - p≠2的推广
- [三角不等式](./15-柯西-施瓦茨不等式.lean) - 范数性质
-/
