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
  /- 方法：考虑二次函数 f(t) = ∑(aᵢ·t + bᵢ)² ≥ 0 -/
  let f := fun (t : ℝ) => ∑ i, (a i * t + b i) ^ 2
  
  /- 展开 f(t) -/
  have h_expand : ∀ t, f t = (∑ i, (a i) ^ 2) * t^2 + 2 * (∑ i, a i * b i) * t + (∑ i, (b i) ^ 2) := by
    intro t
    simp [f]
    rw [sum_add_distrib, sum_add_distrib]
    congr 1
    · /- ∑ aᵢ²·t² = t²·∑ aᵢ² -/
      have : ∑ i, (a i * t) ^ 2 = (∑ i, (a i) ^ 2) * t^2 := by
        calc
          ∑ i, (a i * t) ^ 2 = ∑ i, (a i) ^ 2 * t^2 := by
            simp [mul_pow]
          _ = (∑ i, (a i) ^ 2) * t^2 := by
            rw [Finset.mul_sum]
            simp [mul_comm]
      exact this
    · /- 2·∑ aᵢ·bᵢ·t -/
      have : ∑ i, 2 * (a i * t) * (b i) = 2 * (∑ i, a i * b i) * t := by
        calc
          ∑ i, 2 * (a i * t) * (b i) = ∑ i, 2 * (a i * b i) * t := by
            simp [mul_assoc]
            congr
            funext i
            ring
          _ = 2 * (∑ i, a i * b i) * t := by
            rw [Finset.mul_sum]
            simp [mul_assoc, mul_comm]
      exact this
    · /- ∑ bᵢ² -/
      rfl
  
  /- f(t) ≥ 0 对所有 t -/
  have h_nonneg : ∀ t, f t ≥ 0 := by
    intro t
    simp [f]
    apply sum_nonneg
    intro i hi
    apply sq_nonneg
  
  /- 二次函数非负 ⟹ 判别式 ≤ 0 -/
  have h_discriminant : (2 * (∑ i, a i * b i))^2 - 4 * (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) ≤ 0 := by
    /- 利用二次函数最小值 -/
    let A := ∑ i, (a i) ^ 2
    let B := 2 * (∑ i, a i * b i)
    let C := ∑ i, (b i) ^ 2
    
    by_cases hA : A = 0
    · /- 若 A = 0，则所有 aᵢ = 0，不等式显然成立 -/
      have h_zero : ∀ i, a i = 0 := by
        sorry  -- P1级别：从平方和为零推出每项为零
      simp [h_zero]
      positivity
    
    · /- 若 A > 0，二次函数在 t = -B/(2A) 处取最小值 -/
      have hA_pos : A > 0 := by
        sorry  -- P1级别：从A≠0推出A>0
      
      let t_min := -B / (2 * A)
      have h_min := h_nonneg t_min
      rw [h_expand t_min] at h_min
      /- 化简得到判别式条件 -/
      have : A * t_min^2 + B * t_min + C ≥ 0 := by linarith
      field_simp at this
      nlinarith
  
  /- 化简判别式条件 -/
  have h_simplify : 4 * (∑ i, a i * b i)^2 ≤ 4 * (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) := by
    linarith [h_discriminant]
  
  linarith

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
    ∃ c, ∀ i, a i = c * (b i) ∨ ∀ i, b i = 0 := by
  constructor
  · -- 等号成立 ⇒ 线性相关
    intro h_eq
    /- 从判别式为零推出 -/
    sorry  -- P2级别：需要精细的代数分析
  · -- 线性相关 ⇒ 等号成立
    rintro ⟨c, hc⟩
    /- 直接验证 -/
    sorry  -- P1级别：代数运算

/-
## 第四部分：应用

### 应用1：三角不等式
-/

theorem triangle_inequality_from_cs {n : ℕ} (a b : Fin n → ℝ) :
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2) := by
  /- 利用柯西-施瓦茨证明范数的三角不等式 -/
  sorry  -- P2级别：需要开方运算

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
- [不确定性原理](./16-不确定性原理.lean) - 量子力学应用
-/
