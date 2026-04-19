import Mathlib
/-
# 中值定理的形式化证明 / Formalization of Mean Value Theorem

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Calculus.MeanValue`
- **核心定理**: `exists_hasDerivAt_eq_slope`
- **相关定义**: 
  - `HasDerivAt`: 在某点可导
  - `deriv`: 导数
  - `HasDerivWithinAt`: 在某集合内可导

## 定理陈述
设函数 f 在闭区间 [a, b] 上连续，在开区间 (a, b) 内可导，
则存在 c ∈ (a, b) 使得：

    f'(c) = (f(b) - f(a)) / (b - a)

几何意义：曲线上存在一点，其切线斜率等于连接端点的割线斜率。

## 历史背景
中值定理由拉格朗日在1797年提出，是微分学的核心定理。
它是罗尔定理的推广，也是泰勒展开、洛必达法则等的基础。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Analysis.Calculus.MeanValue`
- 定理 / Theorem: `exists_hasDerivAt_eq_slope`
- 定理 / Theorem: `exists_deriv_eq_slope`
-/

#check exists_hasDerivAt_eq_slope
#check exists_deriv_eq_slope

-- Mean Value Theorem
theorem MeanValueTheorem {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope f f' hab hfc hfd

