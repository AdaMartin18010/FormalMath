/-
# 罗尔定理与微分中值定理 / Rolle's Theorem and Mean Value Theorem

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Calculus.MeanValue`
- **核心定理**: `Rolle`, `exists_hasDerivAt_eq_slope`
- **相关定义**:
  - `HasDerivAt`: 在某点可导
  - `HasDerivWithinAt`: 在某集合内可导
  - `deriv`: 导数

## 定理陈述

### 罗尔定理 (Rolle's Theorem)
设函数 f: [a, b] → ℝ 满足：
1. f 在 [a, b] 上连续
2. f 在 (a, b) 内可导
3. f(a) = f(b)

则存在 c ∈ (a, b)，使得 f'(c) = 0。

### 拉格朗日中值定理 (Lagrange Mean Value Theorem)
设函数 f: [a, b] → ℝ 满足：
1. f 在 [a, b] 上连续
2. f 在 (a, b) 内可导

则存在 c ∈ (a, b)，使得 f'(c) = (f(b) - f(a))/(b - a)。

### 柯西中值定理 (Cauchy Mean Value Theorem)
设函数 f, g: [a, b] → ℝ 满足：
1. f, g 在 [a, b] 上连续
2. f, g 在 (a, b) 内可导
3. g'(x) ≠ 0 对所有 x ∈ (a, b)

则存在 c ∈ (a, b)，使得 (f'(c))/(g'(c)) = (f(b) - f(a))/(g(b) - g(a))。

## 数学意义

中值定理是微分学的核心定理，连接了函数的局部性质（导数）和全局性质（函数值变化）。
它是证明许多重要不等式和定理的基础工具。

## 历史背景

- 罗尔定理：米歇尔·罗尔(Michel Rolle, 1691)
- 拉格朗日中值定理：约瑟夫-路易·拉格朗日(Joseph-Louis Lagrange, 1797)
- 柯西中值定理：奥古斯丁-路易·柯西(Augustin-Louis Cauchy, 1823)

## 证明复杂度分析
- **难度等级**: P2 (本科高级)
- **证明行数**: ~250行
- **关键引理**: 6个
- **主要策略**: 极值定理 + 费马引理
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic

universe u

namespace RolleTheorem

open Set Topology

/-
## 第一部分：费马引理

费马引理：若函数在某内点取得极值且可导，则该点导数为零。
-/

-- 费马引理：极值点导数为零
theorem fermat_lemma {f : ℝ → ℝ} {c : ℝ}
    (h_local_max : ∀ x in nhds c, f x ≤ f c)
    (h_differentiable : DifferentiableAt ℝ f c) :
    deriv f c = 0 := by
  /- 使用Mathlib4的极值点导数定理 -/
  have h_local_max' : IsLocalMax f c := h_local_max
  exact h_local_max'.deriv_eq_zero h_differentiable.hasDerivAt

-- 费马引理（最小值版本）
theorem fermat_lemma_min {f : ℝ → ℝ} {c : ℝ}
    (h_local_min : ∀ x in nhds c, f c ≤ f x)
    (h_differentiable : DifferentiableAt ℝ f c) :
    deriv f c = 0 := by
  /- 对 -f 应用最大值版本的费马引理 -/
  have h_local_min' : IsLocalMin f c := h_local_min
  exact h_local_min'.deriv_eq_zero h_differentiable.hasDerivAt

/-
## 第二部分：罗尔定理

**定理**: 若 f 在 [a,b] 连续，在 (a,b) 可导，且 f(a) = f(b)，
则存在 c ∈ (a,b) 使得 f'(c) = 0。

**证明思路**:
1. 由极值定理，f 在 [a,b] 上取得最大值和最小值
2. 若极值点在内部，由费马引理，导数为零
3. 若极值点都在端点，由于 f(a) = f(b)，f 为常数函数，导数处处为零
-/

-- 罗尔定理
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : DifferentiableOn ℝ f (Ioo a b))
    (h_eq : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  /- 使用Mathlib4的罗尔定理 -/
  have h := exists_deriv_eq_zero hab h_continuous h_differentiable h_eq
  rcases h with ⟨c, hc_mem, hc_deriv⟩
  exact ⟨c, hc_mem, hc_deriv.2⟩

/-
## 第三部分：拉格朗日中值定理

**定理**: 若 f 在 [a,b] 连续，在 (a,b) 可导，
则存在 c ∈ (a,b) 使得 f'(c) = (f(b) - f(a))/(b - a)。

**证明思路**:
1. 构造辅助函数 g(x) = f(x) - [(f(b) - f(a))/(b - a)](x - a)
2. 验证 g(a) = g(b) = f(a)
3. 对 g 应用罗尔定理
4. 得到 g'(c) = 0，即 f'(c) = (f(b) - f(a))/(b - a)
-/

-- 拉格朗日中值定理
theorem lagrange_mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  /- 使用Mathlib4的拉格朗日中值定理 -/
  have h := exists_hasDerivAt_eq_slope f hab h_continuous h_differentiable
  rcases h with ⟨c, hc_mem, hc_slope⟩
  use c, hc_mem
  rw [← hc_slope.2]
  simp

-- 拉格朗日中值定理的另一种形式
theorem lagrange_mean_value' {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  rcases lagrange_mean_value hab h_continuous h_differentiable with ⟨c, hc, hc_deriv⟩
  use c, hc
  field_simp at hc_deriv ⊢
  linarith

/-
## 第四部分：柯西中值定理

**定理**: 若 f, g 在 [a,b] 连续，在 (a,b) 可导，且 g'(x) ≠ 0，
则存在 c ∈ (a,b) 使得 (f'(c))/(g'(c)) = (f(b) - f(a))/(g(b) - g(a))。

**证明思路**:
1. 构造辅助函数 h(x) = f(x) - [(f(b) - f(a))/(g(b) - g(a))]g(x)
2. 验证 h(a) = h(b)
3. 对 h 应用罗尔定理
-/

-- 柯西中值定理
theorem cauchy_mean_value {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_f_continuous : ContinuousOn f (Icc a b))
    (h_g_continuous : ContinuousOn g (Icc a b))
    (h_f_differentiable : DifferentiableOn ℝ f (Ioo a b))
    (h_g_differentiable : DifferentiableOn ℝ g (Ioo a b))
    (h_g'_ne_zero : ∀ x ∈ Ioo a b, deriv g x ≠ 0) :
    ∃ c ∈ Ioo a b, deriv f c / deriv g c = (f b - f a) / (g b - g a) := by
  /- 首先证明 g(b) ≠ g(a) -/
  have h_gb_ga : g b ≠ g a := by
    by_contra h_eq
    /- 若 g(b) = g(a)，对 g 应用罗尔定理 -/
    rcases rolle hab h_g_continuous h_g_differentiable h_eq.symm with ⟨c, hc, hc_deriv⟩
    /- 得到 g'(c) = 0，与条件矛盾 -/
    have h_zero : deriv g c = 0 := hc_deriv
    have h_ne_zero := h_g'_ne_zero c hc
    contradiction
  
  /- 构造辅助函数 -/
  let h := fun x => f x - ((f b - f a) / (g b - g a)) * g x
  
  /- 验证 h 满足罗尔定理条件 -/
  have h_continuous : ContinuousOn h (Icc a b) := by
    apply ContinuousOn.sub
    · exact h_f_continuous
    · apply ContinuousOn.mul
      · exact continuousOn_const
      · exact h_g_continuous
  
  have h_differentiable : DifferentiableOn ℝ h (Ioo a b) := by
    intro x hx
    apply DifferentiableWithinAt.sub
    · apply h_f_differentiable x hx
    · apply DifferentiableWithinAt.mul
      · exact differentiableWithinAt_const _
      · apply h_g_differentiable x hx
  
  have h_eq : h a = h b := by
    simp [h]
    field_simp [(show g b - g a ≠ 0 by intro h'; apply h_gb_ga; linarith)]
    ring
  
  /- 对 h 应用罗尔定理 -/
  rcases rolle hab h_continuous h_differentiable h_eq with ⟨c, hc, hc_deriv⟩
  
  /- 计算 h'(c) -/
  have h_deriv : deriv h c = deriv f c - ((f b - f a) / (g b - g a)) * deriv g c := by
    simp [h, deriv_sub, deriv_mul, deriv_const, mul_comm]
    · apply h_f_differentiable.differentiableAt (isOpen_Ioo.mem_nhds hc)
    · apply h_g_differentiable.differentiableAt (isOpen_Ioo.mem_nhds hc)
  
  /- 由 h'(c) = 0 得到结论 -/
  rw [h_deriv] at hc_deriv
  use c, hc
  have h_ne_zero := h_g'_ne_zero c hc
  field_simp at hc_deriv ⊢
  linarith

/-
## 第五部分：中值定理的应用

### 应用1：导数恒为零的函数是常数
-/

-- 导数为零的函数是常数
theorem constant_of_deriv_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : DifferentiableOn ℝ f (Ioo a b))
    (h_deriv_zero : ∀ x ∈ Ioo a b, deriv f x = 0) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases hx with ⟨hxa, hxb⟩
  
  /- 对 [a, x] 应用中值定理 -/
  by_cases hax : a = x
  · /- 若 a = x，结论显然 -/
    rw [hax]
  · /- 若 a < x -/
    have hax' : a < x := by
      by_contra h
      push_neg at h
      have : a = x := by linarith [hxa]
      contradiction
    
    rcases lagrange_mean_value hax' 
        (ContinuousOn.mono h_continuous (Icc_subset_Icc_right hxb.le))
        (DifferentiableOn.mono h_differentiable (Ioo_subset_Ioo (le_refl _) hxb.le))
      with ⟨c, hc, hc_deriv⟩
    
    have h_zero : deriv f c = 0 := h_deriv_zero c (Ioo_subset_Ioo (le_refl _) hxb.le hc)
    rw [h_zero] at hc_deriv
    simp at hc_deriv
    linarith

-- 导数为零的函数在整个区间上为常数
theorem constant_of_deriv_zero_univ {f : ℝ → ℝ}
    (h_differentiable : Differentiable ℝ f)
    (h_deriv_zero : ∀ x, deriv f x = 0) :
    ∃ C, ∀ x, f x = C := by
  use f 0
  intro x
  by_cases hx0 : x = 0
  · rw [hx0]
  · wlog hx_pos : x > 0 generalizing x
    · /- 若 x < 0，在 [x, 0] 上应用中值定理 -/
      have : x < 0 := by
        by_contra h
        push_neg at h
        have : x = 0 := by linarith
        contradiction
      have h := constant_of_deriv_zero (by linarith : x < (0 : ℝ))
        (Continuous.continuousOn (Differentiable.continuous h_differentiable))
        (Differentiable.differentiableOn h_differentiable)
        (fun x _ => h_deriv_zero x)
      specialize h 0 (by simp)
      have h' := h x (by simp; linarith)
      linarith
    /- 在 [0, x] 上应用中值定理 -/
    have h := constant_of_deriv_zero hx_pos
      (Continuous.continuousOn (Differentiable.continuous h_differentiable))
      (Differentiable.differentiableOn h_differentiable)
      (fun x _ => h_deriv_zero x)
    specialize h x (by simp; linarith)
    linarith

/-
### 应用2：导数恒正的函数严格递增
-/

-- 导数为正的函数递增
theorem increasing_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : DifferentiableOn ℝ f (Ioo a b))
    (h_deriv_pos : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  rcases hx with ⟨hxa, hxb⟩
  rcases hy with ⟨hya, hyb⟩
  
  /- 对 [x, y] 应用中值定理 -/
  have hxy' : x < y := hxy
  rcases lagrange_mean_value hxy'
      (ContinuousOn.mono h_continuous (Icc_subset_Icc hxa.le hyb.le))
      (DifferentiableOn.mono h_differentiable (Ioo_subset_Ioo hxa.le hyb.le))
    with ⟨c, hc, hc_deriv⟩
  
  have h_pos : 0 < deriv f c := h_deriv_pos c (Ioo_subset_Ioo hxa.le hyb.le hc)
  rw [hc_deriv] at h_pos
  have : 0 < (f y - f x) / (y - x) := h_pos
  have : 0 < f y - f x := by
    apply div_pos_iff.mp at this
    cases this with
    | inl h => linarith
    | inr h => linarith
  linarith

/-
## 第六部分：泰勒定理

泰勒定理是中值定理的高阶推广。
-/

-- 泰勒定理（带拉格朗日余项）
theorem taylor_lagrange {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a < b)
    (h_continuous : ContinuousOn f (Icc a b))
    (h_differentiable : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (h_diff_n1 : DifferentiableOn ℝ (iteratedDeriv (n + 1) f) (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b = ∑ k in Finset.range (n + 1), 
      (iteratedDeriv k f a) / k.factorial * (b - a)^k +
      (iteratedDeriv (n + 1) f c) / (n + 1).factorial * (b - a)^(n + 1) := by
  sorry  -- P3级别：需要高阶导数的精细处理

end RolleTheorem

/-
## 数学意义

中值定理的重要性：

1. **局部与全局的联系**：连接导数（局部）和函数值变化（全局）
2. **不等式证明**：许多重要不等式的基础工具
3. **函数性态分析**：单调性、凸凹性的判定
4. **泰勒展开**：高阶近似和误差估计

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| 罗尔定理 | 拉格朗日中值定理的特例 |
| 泰勒定理 | 中值定理的高阶推广 |
| 洛必达法则 | 柯西中值定理的应用 |
| 积分中值定理 | 中值定理在积分形式下的对应 |

## 应用示例

### 例1：证明 eˣ > 1 + x 对 x > 0

```lean
example : ∀ x > 0, Real.exp x > 1 + x := by
  intro x hx
  have h := @lagrange_mean_value (fun t => Real.exp t) 0 x (by linarith)
    (Continuous.continuousOn Real.continuous_exp)
    (Differentiable.differentiableOn Real.differentiable_exp)
  rcases h with ⟨c, hc, hc_eq⟩
  have : deriv (fun t => Real.exp t) c = Real.exp c := by simp
  rw [this] at hc_eq
  have h_exp_pos : Real.exp c > 1 := by
    have : c > 0 := hc.1
    have : Real.exp c > Real.exp 0 := Real.exp_strictMono this
    simp at this
    linarith
  have : Real.exp x - 1 = Real.exp c * x := by
    field_simp at hc_eq
    linarith
  nlinarith
```

### 例2：洛必达法则的应用

柯西中值定理是洛必达法则的理论基础。

## 历史发展

| 年份 | 数学家 | 贡献 |
|------|--------|------|
| 1691 | 罗尔 | 罗尔定理 |
| 1797 | 拉格朗日 | 拉格朗日中值定理 |
| 1823 | 柯西 | 柯西中值定理 |
| 现代 | - | 推广到多元函数 |

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Analysis.Calculus.MeanValue`: 中值定理核心
- `Mathlib.Analysis.Calculus.Deriv.Basic`: 导数基础
- `Mathlib.Analysis.Calculus.Taylor`: 泰勒展开

## 相关定理链接

- [拉格朗日插值](./07-拉格朗日插值.lean) - 数值分析基础
- [隐函数定理](./ImplicitFunctionTheorem.lean) - 多元分析
- [反函数定理](./InverseFunctionTheorem.lean) - 局部可逆性
-/
