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

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Rolle
import Mathlib.Topology.ContinuousOn

universe u v

namespace MeanValueTheorem

open Set Topology Real

/-
## 核心概念

### 导数 (Derivative)
函数 f 在点 x 的导数定义为：
f'(x) = lim_{h→0} (f(x+h) - f(x)) / h

### 连续函数 (Continuous Function)
函数 f 在点 x 连续，如果 lim_{y→x} f(y) = f(x)。

### 罗尔定理 (Rolle's Theorem)
中值定理的特殊情形，当 f(a) = f(b) 时，存在 c 使得 f'(c) = 0。
-

-- 罗尔定理
theorem rolle_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (heq : f a = f b) :
    ∃ c ∈ Ioo a b, f' c = 0 := by
  /- 证明思路：
     1. 由极值定理，f 在 [a, b] 上取得最大值和最小值
     2. 若最大值或最小值在内部取得，则导数为0
     3. 若都在端点取得，则 f 是常数，导数处处为0
  -/
  
  /- 应用Mathlib4的Rolle定理 -/
  rcases exists_hasDerivAt_eq_zero hab hcont (fun x hx => hdiff x hx) heq with ⟨c, hc, hderiv⟩
  use c, hc
  /- hderiv 给出 f'(c) = 0 -/
  simpa using hderiv

/-
## 中值定理主证明

**证明思路**:
1. 构造辅助函数 g(x) = f(x) - [(f(b)-f(a))/(b-a)](x-a) - f(a)
2. 验证 g(a) = g(b) = 0
3. 对 g 应用罗尔定理
4. 得到 g'(c) = 0，即 f'(c) = (f(b)-f(a))/(b-a)
-

-- 拉格朗日中值定理
theorem lagrange_mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  /- 构造辅助函数 g(x) = f(x) - [(f(b)-f(a))/(b-a)](x-a) - f(a) -/
  let g : ℝ → ℝ := fun x => f x - ((f b - f a) / (b - a)) * (x - a) - f a
  
  /- 验证 g(a) = 0 -/
  have h_ga : g a = 0 := by
    simp [g]
  
  /- 验证 g(b) = 0 -/
  have h_gb : g b = 0 := by
    simp [g]
    field_simp
    ring
  
  /- g 在 [a, b] 上连续 -/
  have h_g_cont : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact hcont
      · apply ContinuousOn.mul
        · exact continuousOn_const
        · apply continuousOn_id.sub
          exact continuousOn_const
    · exact continuousOn_const
  
  /- g 在 (a, b) 内可导 -/
  have h_g_diff : ∀ x ∈ Ioo a b, HasDerivAt g (f' x - (f b - f a) / (b - a)) x := by
    intro x hx
    simp [g]
    /- g'(x) = f'(x) - (f(b)-f(a))/(b-a) -/
    apply HasDerivAt.sub
    · apply HasDerivAt.sub
      · exact hdiff x hx
      · apply HasDerivAt.mul_const
        apply HasDerivAt.sub
        · exact hasDerivAt_id x
        · exact hasDerivAt_const x a
    · exact hasDerivAt_const x (f a)
  
  /- 对 g 应用罗尔定理 -/
  rcases rolle_theorem hab h_g_cont h_g_diff (h_ga.trans h_gb.symm) with ⟨c, hc, h_gc⟩
  
  use c, hc
  /- g'(c) = 0 推出 f'(c) = (f(b)-f(a))/(b-a) -/
  simp at h_gc
  linarith

-- 使用Mathlib4的定理
theorem lagrange_mean_value_mathlib {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope hab hcont
  intro x hx
  exact hdiff x hx

/-
## 柯西中值定理

**定理**: 设 f, g 在 [a, b] 上连续，在 (a, b) 内可导，
则存在 c ∈ (a, b) 使得：

    (f'(c)) / (g'(c)) = (f(b) - f(a)) / (g(b) - g(a))

**条件**: g'(c) ≠ 0 且 g(b) ≠ g(a)
-

-- 柯西中值定理
theorem cauchy_mean_value {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont_f : ContinuousOn f (Icc a b))
    (hcont_g : ContinuousOn g (Icc a b))
    (hdiff_f : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hdiff_g : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg_ne : ∀ x ∈ Ioo a b, g' x ≠ 0) :
    ∃ c ∈ Ioo a b, f' c / g' c = (f b - f a) / (g b - g a) := by
  /- 构造辅助函数 h(x) = f(x)(g(b)-g(a)) - g(x)(f(b)-f(a)) -/
  let h : ℝ → ℝ := fun x => f x * (g b - g a) - g x * (f b - f a)
  
  /- 验证 h(a) = h(b) -/
  have h_ha : h a = f a * (g b - g a) - g a * (f b - f a) := rfl
  have h_hb : h b = f b * (g b - g a) - g b * (f b - f a) := rfl
  have h_eq : h a = h b := by
    rw [h_ha, h_hb]
    ring
  
  /- h 在 [a, b] 上连续 -/
  have h_h_cont : ContinuousOn h (Icc a b) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact hcont_f
      · exact continuousOn_const
    · apply ContinuousOn.mul
      · exact hcont_g
      · exact continuousOn_const
  
  /- h 在 (a, b) 内可导 -/
  have h_h_diff : ∀ x ∈ Ioo a b, HasDerivAt h (f' x * (g b - g a) - g' x * (f b - f a)) x := by
    intro x hx
    simp [h]
    apply HasDerivAt.sub
    · apply HasDerivAt.mul_const
      exact hdiff_f x hx
    · apply HasDerivAt.mul_const
      exact hdiff_g x hx
  
  /- 对 h 应用罗尔定理 -/
  rcases rolle_theorem hab h_h_cont h_h_diff h_eq with ⟨c, hc, h_hc⟩
  
  use c, hc
  /- h'(c) = 0 推出 f'(c)(g(b)-g(a)) = g'(c)(f(b)-f(a)) -/
  simp at h_hc
  
  /- 证明 g(b) ≠ g(a) -/
  have h_gb_ga : g b - g a ≠ 0 := by
    by_contra h_zero
    have : g b = g a := by linarith
    /- 应用罗尔定理于 g -/
    rcases exists_hasDerivAt_eq_zero hab hcont_g (fun x hx => hdiff_g x hx) this with ⟨c', hc', h_gc'⟩
    have : g' c' = 0 := by simpa using h_gc'
    have : g' c' ≠ 0 := hg_ne c' hc'
    contradiction
  
  /- 整理得到结论 -/
  have h_eq' : f' c * (g b - g a) = g' c * (f b - f a) := by linarith
  field_simp [h_gb_ga, hg_ne c hc]
  linarith

/-
## 洛必达法则

**定理**: 设 f, g 在 x₀ 的某去心邻域内可导，且
lim_{x→x₀} f(x) = lim_{x→x₀} g(x) = 0（或 ±∞）
若 lim_{x→x₀} f'(x)/g'(x) 存在，则：

    lim_{x→x₀} f(x)/g(x) = lim_{x→x₀} f'(x)/g'(x)

**应用**: 计算不定型极限 0/0 或 ∞/∞
-

-- 洛必达法则（0/0型）
theorem lhopital_zero_over_zero {f g : ℝ → ℝ} {x₀ L : ℝ}
    (hf : Tendsto f (𝓝[≠] x₀) (𝓝 0))
    (hg : Tendsto g (𝓝[≠] x₀) (𝓝 0))
    (hderiv : ∀ᶠ x in 𝓝[≠] x₀, HasDerivAt f (f' x) x ∧ HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝[≠] x₀, g' x ≠ 0)
    (hlim : Tendsto (fun x => f' x / g' x) (𝓝[≠] x₀) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] x₀) (𝓝 L) := by
  /- 使用Mathlib4的洛必达法则 -/
  apply HasDerivAt.lhopital_zero_right hf hg hderiv hg' hlim
  · exact eventually_of_forall (by simp)

/-
## 泰勒定理与中值定理

泰勒定理是中值定理的高阶推广。

**泰勒定理**: 设 f 在 x₀ 的某邻域内有 n+1 阶导数，则：

    f(x) = f(x₀) + f'(x₀)(x-x₀) + f''(x₀)(x-x₀)²/2! + ... + f⁽ⁿ⁾(x₀)(x-x₀)ⁿ/n! + Rₙ(x)

其中 Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)(x-x₀)ⁿ⁺¹/(n+1)! 对某个 ξ 在 x₀ 和 x 之间。
-

-- 带拉格朗日余项的泰勒公式
theorem taylor_lagrange {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ}
    (hdiff : ContDiffOn ℝ (n + 1) f (Icc (min x₀ x) (max x₀ x))) :
    ∃ ξ ∈ Ioo (min x₀ x) (max x₀ x),
    f x = ∑ i ∈ Finset.range (n + 1), (iteratedDeriv i f x₀) * (x - x₀) ^ i / Nat.factorial i +
          iteratedDeriv (n + 1) f ξ * (x - x₀) ^ (n + 1) / Nat.factorial (n + 1) := by
  /- 使用Mathlib4的泰勒定理 -/
  have h : x₀ ≤ x ∨ x ≤ x₀ := le_total x₀ x
  rcases h with hle | hge
  · -- 情形 x₀ ≤ x
    rw [min_eq_left hle, max_eq_right hle] at hdiff
    have htaylor := taylor_mean_remainder_lagrange hdiff (by simp [hle]) n
    rcases htaylor with ⟨ξ, hξ, heq⟩
    use ξ
    constructor
    · exact hξ
    · rw [heq]
      field_simp
      <;> ring_nf <;> simp [mul_comm]
  · -- 情形 x ≤ x₀
    rw [min_eq_right (le_of_not_le hle), max_eq_left (le_of_not_le hle)] at hdiff
    have hge' : x ≤ x₀ := by linarith
    have htaylor := taylor_mean_remainder_lagrange hdiff (by simp [hge']) n
    rcases htaylor with ⟨ξ, hξ, heq⟩
    use ξ
    constructor
    · exact hξ
    · rw [heq]
      field_simp
      <;> ring_nf <;> simp [mul_comm]

end MeanValueTheorem

/-
## 应用示例

### 示例1：证明不等式

```lean
-- 证明：当 x > 0 时，sin(x) < x
example (x : ℝ) (hx : x > 0) : Real.sin x < x := by
  let f := fun t => t - Real.sin t
  have hcont : ContinuousOn f (Icc 0 x) := by continuity
  have hdiff : ∀ t ∈ Ioo 0 x, HasDerivAt f (1 - Real.cos t) t := by
    intro t ht
    simp [f]
    apply HasDerivAt.sub
    · exact hasDerivAt_id t
    · exact Real.hasDerivAt_sin t
  
  rcases lagrange_mean_value hx hcont hdiff with ⟨c, hc, h_eq⟩
  have h_pos : 0 < f x := by
    simp [f]
    /- f(x) = f(0) + f'(c)·x = 0 + (1-cos(c))·x -/
    have h_f0 : f 0 = 0 := by simp [f]
    have h_fx : f x = (1 - Real.cos c) * x := by
      field_simp at h_eq
      linarith [h_eq, h_f0]
    rw [h_fx]
    have h_cos_lt_1 : Real.cos c < 1 := by
      apply Real.cos_lt_one
      linarith [hc.1, hc.2, hx]
    nlinarith [h_cos_lt_1]
  
  simp [f] at h_pos
  linarith
```

## 数学意义

中值定理的重要性：

1. **理论基础**：建立了导数与函数变化率之间的联系
2. **不等式证明**：提供了证明不等式的有力工具
3. **极限计算**：洛必达法则的基础
4. **函数逼近**：泰勒展开的基石

## 与其他定理的关系

- **罗尔定理**：中值定理的特例
- **柯西中值定理**：中值定理的推广
- **泰勒定理**：中值定理的高阶形式
- **积分中值定理**：离散形式的中值定理

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `exists_hasDerivAt_eq_slope`: 拉格朗日中值定理
- `exists_ratio_hasDerivAt_eq_ratio_slope`: 柯西中值定理
- `HasDerivAt.lhopital_zero_right`: 洛必达法则
- `ContDiffOn`: 高阶可导性
-/
