/-
# 柯西-施瓦茨不等式的形式化证明 / Cauchy-Schwarz Inequality

## 领域
泛函分析 / 内积空间理论 (Functional Analysis / Inner Product Spaces)

## Mathlib4对应
- **模块**: `Mathlib.Analysis.InnerProductSpace.Basic`
- **核心定理**: `norm_inner_le_norm`
- **相关定义**:
  - `InnerProductSpace`
  - `inner`
  - `norm`

## MSC2020编码
- **Primary**: 46C05
- **Secondary**: 26D15

## 对齐课程
- MIT 18.102 (Introduction to Functional Analysis)
- Harvard Math 212a (Real Analysis)
- Princeton MAT 425 (Analysis III: Integration Theory and Hilbert Spaces)
- ETH 401-3461-00L (Functional Analysis I)

## 定理陈述
设 V 是实（或复）内积空间，对于任意向量 u, v ∈ V，有：
|⟨u, v⟩| ≤ ‖u‖ · ‖v‖

等号成立当且仅当 u 和 v 线性相关。

## 数学意义
柯西-施瓦茨不等式是内积空间理论的基石，连接了内积和范数两个核心概念。

## 历史背景
由Augustin-Louis Cauchy于1821年对 ℝⁿ 证明，Hermann Schwarz于1885年推广到积分情形，Viktor Bunyakovsky于1859年独立证明积分版本。
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Data.Real.Basic

universe u v

namespace CauchySchwarzInequality

open InnerProductSpace Real Complex

/-
## 核心概念

### 内积空间 (Inner Product Space)
向量空间 V 配备一个内积 ⟨·, ·⟩ : V × V → 𝕂，满足：
1. 对第一个变元线性
2. 共轭对称：⟨u, v⟩ = ⟨v, u⟩的共轭
3. 正定性：⟨v, v⟩ ≥ 0，且 ⟨v, v⟩ = 0 ⟺ v = 0

### 柯西-施瓦茨不等式
对于内积空间中的任意向量 u, v：
|⟨u, v⟩| ≤ ‖u‖ · ‖v‖
-/

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

-- 柯西-施瓦茨不等式：核心形式
theorem cauchy_schwarz_inequality (u v : E) :
    ‖inner u v‖ ≤ ‖u‖ * ‖v‖ := by
  /- 使用Mathlib4的柯西-施瓦茨不等式 -/
  exact norm_inner_le_norm u v

-- 等号成立条件
theorem cauchy_schwarz_eq_iff {u v : E} :
    ‖inner u v‖ = ‖u‖ * ‖v‖ ↔ ∃ (r : 𝕜), u = r • v := by
  /- 等号成立当且仅当两向量线性相关 -/
  constructor
  · intro h
    exact inner_eq_norm_mul_norm_iff.mp h
  · rintro ⟨r, hr⟩
    rw [hr]
    exact inner_eq_norm_mul_norm_iff.mpr ⟨r, rfl⟩

-- 实内积空间的柯西-施瓦茨不等式（不带绝对值）
theorem cauchy_schwarz_real {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (u v : F) :
    inner u v ≤ ‖u‖ * ‖v‖ := by
  /- 由 ‖⟨u,v⟩‖ ≤ ‖u‖‖v‖ 及 |x| ≥ x 可得 -/
  have h : ‖inner u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have h2 : inner u v ≤ ‖inner u v‖ := by
    apply le_abs_self
  linarith

-- 平方形式的柯西-施瓦茨不等式
theorem cauchy_schwarz_sq (u v : E) :
    ‖inner u v‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  /- 对不等式两边平方 -/
  have h := cauchy_schwarz_inequality u v
  nlinarith [norm_nonneg (inner u v), norm_nonneg u, norm_nonneg v]

-- 极化恒等式
theorem polarization_identity {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (u v : F) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * inner u v := by
  /- 使用Mathlib4的极化恒等式 -/
  rw [norm_add_sq_real]
  ring

/-
## 应用：ℝⁿ 中的柯西-施瓦茨不等式

对于向量 x = (x₁, ..., xₙ) 和 y = (y₁, ..., yₙ)：
(∑ xᵢyᵢ)² ≤ (∑ xᵢ²)(∑ yᵢ²)
-/

theorem cauchy_schwarz_rn {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * y i) ^ 2 ≤ (∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2) := by
  /- 使用Fin n → ℝ作为内积空间 -/
  have h := cauchy_schwarz_sq (𝕜 := ℝ) (E := Fin n → ℝ) x y
  simp [Finset.sum_mul_sum, inner, EuclideanSpace.inner_product_space] at h ⊢
  exact h

-- 连续函数空间 L² 中的柯西-施瓦茨不等式（axiom占位）
axiom cauchy_schwarz_l2 {α : Type*} [MeasureSpace α] (f g : Lp ℝ 2 α) :
    ‖∫ x, f x * g x‖ ≤ ‖f‖ * ‖g‖

end CauchySchwarzInequality

/-
## 应用示例

### 三角不等式

柯西-施瓦茨不等式是证明内积空间中三角不等式的关键步骤：
‖u + v‖² = ‖u‖² + ‖v‖² + 2⟨u, v⟩ ≤ ‖u‖² + ‖v‖² + 2‖u‖‖v‖ = (‖u‖ + ‖v‖)²

### 相关系数

在概率论中，柯西-施瓦茨不等式保证了相关系数的绝对值不超过1。

## 数学意义

柯西-施瓦茨不等式的重要性：

1. **内积与范数的桥梁**: 从内积导出范数的关键不等式
2. **三角不等式基础**: 证明 ‖u+v‖ ≤ ‖u‖ + ‖v‖
3. **最佳逼近**: 正交投影和最小二乘法的理论基础
4. **概率论应用**: 保证协方差矩阵的正半定性

## 推广形式

| 形式 | 内容 |
|------|------|
| 积分形式 | (∫fg)² ≤ (∫f²)(∫g²) |
| Hölder不等式 | 对共轭指数 p, q 的推广 |
| Minkowski不等式 | L^p范数的三角不等式 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Analysis.InnerProductSpace.Basic`: 内积空间理论
- `norm_inner_le_norm`: 柯西-施瓦茨不等式的核心实现
- `inner_eq_norm_mul_norm_iff`: 等号成立条件
- `norm_add_sq_real`: 实内积空间的极化恒等式
-/
