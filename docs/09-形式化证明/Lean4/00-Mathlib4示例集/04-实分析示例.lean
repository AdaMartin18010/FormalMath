import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real

/-! 
# 实分析示例

对应的FormalMath文档：
- docs/03-分析学/01-实分析/01-实分析-深度扩展版.md
- docs/03-分析学/01-实分析/02-Lebesgue积分-深度扩展版.md

对应的Mathlib4模块：
- Mathlib.Analysis.Calculus.Deriv.Basic
- Mathlib.Analysis.Calculus.MeanValue
- Mathlib.Analysis.SpecificLimits.Basic
- Mathlib.MeasureTheory.Integral.Bochner
- Mathlib.MeasureTheory.Integral.FundThmCalculus

## 核心定义
-/ 

/-! 
## 极限

极限是分析的基石概念。在Mathlib4中，极限使用滤子（Filter）框架定义。
-/

section Limits

-- 数列极限
example (f : ℕ → ℝ) (L : ℝ) : Prop := 
  Filter.Tendsto f Filter.atTop (nhds L)

-- 简写形式
example (f : ℕ → ℝ) (L : ℝ) : Prop := 
  Tendsto f atTop (𝓝 L)

-- 常数列的极限
example (c : ℝ) : Tendsto (fun n => c) atTop (𝓝 c) := by
  exact tendsto_const_nhds

-- 极限的四则运算
example (f g : ℕ → ℝ) (L M : ℝ) (hf : Tendsto f atTop (𝓝 L)) 
    (hg : Tendsto g atTop (𝓝 M)) : 
    Tendsto (fun n => f n + g n) atTop (𝓝 (L + M)) := by
  apply Tendsto.add
  · exact hf
  · exact hg

-- 夹逼定理
example (f g h : ℕ → ℝ) (L : ℝ) (hf : Tendsto f atTop (𝓝 L)) 
    (hh : Tendsto h atTop (𝓝 L)) (hg : ∀ n, f n ≤ g n ∧ g n ≤ h n) : 
    Tendsto g atTop (𝓝 L) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh
  · intro n
    exact (hg n).left
  · intro n
    exact (hg n).right

-- 重要极限：1/n → 0
example : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_0_nat

end Limits

/-! 
## 连续性

连续函数的多种等价定义。
-/

section Continuity

-- 在一点连续
example (f : ℝ → ℝ) (x : ℝ) : Prop := ContinuousAt f x

-- 在整个空间连续
example (f : ℝ → ℝ) : Prop := Continuous f

-- 连续函数的性质
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) : 
    Continuous (fun x => f x + g x) := by
  apply Continuous.add
  · exact hf
  · exact hg

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) : 
    Continuous (fun x => f x * g x) := by
  apply Continuous.mul
  · exact hf
  · exact hg

-- 复合函数的连续性
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) : 
    Continuous (g ∘ f) := by
  apply Continuous.comp
  · exact hg
  · exact hf

-- 多项式函数连续
example (p : Polynomial ℝ) : Continuous (fun x => p.eval x) := by
  apply Polynomial.continuous

end Continuity

/-! 
## 导数

导数的定义和基本性质。
-/

section Derivatives

-- 在某点可导
example (f : ℝ → ℝ) (x : ℝ) : Prop := DifferentiableAt ℝ f x

-- 在某点的导数值
example (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv f x

-- 导数的定义（使用极限）
example (f : ℝ → ℝ) (x : ℝ) (h : DifferentiableAt ℝ f x) : 
    Tendsto (fun h' => (f (x + h') - f x) / h') (𝓝[≠] 0) (𝓝 (deriv f x)) := by
  simpa using h.hasDerivAt

-- 基本函数的导数
example : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  funext x
  simp [deriv_pow]

example : deriv (fun x : ℝ => Real.exp x) = fun x => Real.exp x := by
  funext x
  simp [Real.deriv_exp]

example : deriv Real.sin = Real.cos := by
  funext x
  simp [Real.deriv_sin]

example : deriv Real.cos = fun x => -Real.sin x := by
  funext x
  simp [Real.deriv_cos]

-- 导数的线性性质
example (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) 
    (hg : DifferentiableAt ℝ g x) : 
    deriv (fun y => f y + g y) x = deriv f x + deriv g x := by
  simp [deriv_add, hf, hg]

-- 乘积法则
example (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) 
    (hg : DifferentiableAt ℝ g x) : 
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  simp [deriv_mul, hf, hg]

-- 链式法则
example (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f (g x)) 
    (hg : DifferentiableAt ℝ g x) : 
    deriv (f ∘ g) x = deriv f (g x) * deriv g x := by
  rw [deriv_comp x hf hg]

end Derivatives

/-! 
## 中值定理

微分学的核心定理。
-/

section MeanValueTheorem

-- Rolle定理
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) 
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hfa : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  apply exists_deriv_eq_zero
  all_goals assumption

-- Lagrange中值定理
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) 
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope
  all_goals assumption

-- Cauchy中值定理
example (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b) 
    (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hg' : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x) :
    ∃ c ∈ Set.Ioo a b, deriv f c * (g b - g a) = deriv g c * (f b - f a) := by
  apply exists_ratio_hasDerivAt_eq_ratio_slope
  all_goals assumption

end MeanValueTheorem

/-! 
## 积分

Riemann积分和Lebesgue积分。
-/

section Integration

-- Lebesgue积分（Bochner积分）
example {X : Type*} [MeasureSpace X] (f : X → ℝ) : ℝ := ∫ x, f x

-- 积分的基本性质
example {X : Type*} [MeasureSpace X] {f g : X → ℝ} 
    (hf : Integrable f) (hg : Integrable g) :
    ∫ x, (f x + g x) = ∫ x, f x + ∫ x, g x := by
  rw [integral_add hf hg]

example {X : Type*} [MeasureSpace X] {f : X → ℝ} (c : ℝ) 
    (hf : Integrable f) :
    ∫ x, c * f x = c * ∫ x, f x := by
  rw [integral_smul]

-- 区间积分
example (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, f x

-- 微积分基本定理（第一部分）
example (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.interval a b)) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f b) b := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact hf
  · apply intervalIntegrable_of_continuousOn
    exact hf

-- 微积分基本定理（第二部分）
example (f : ℝ → ℝ) (F : ℝ → ℝ) (a b : ℝ) 
    (hF : ∀ x ∈ Set.interval a b, HasDerivAt F (f x) x)
    (hf : IntervalIntegrable f MeasureSpace.volume a b) :
    ∫ x in a..b, f x = F b - F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt hF hf

end Integration

/-! 
## 级数

无穷级数的收敛性。
-/

section Series

-- 级数收敛
example (f : ℕ → ℝ) : Prop := Summable f

-- 级数求和
example (f : ℕ → ℝ) : ℝ := ∑' n : ℕ, f n

-- 几何级数
example (r : ℝ) (hr : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by
  rw [tsum_geometric_of_abs_lt_one hr]

-- 调和级数发散
example : ¬ Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
  rw [summable_nat_add_iff 1]
  exact Real.not_summable_nat_cast_inv

end Series

/-! 
## 指数函数和对数函数

重要的超越函数。
-/

section ExpAndLog

-- 指数函数
#check Real.exp

-- 指数函数的性质
example (x : ℝ) : Real.exp x > 0 := by
  apply Real.exp_pos

example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  rw [Real.exp_add]

-- 自然对数
#check Real.log

-- 对数的性质
example (x : ℝ) (hx : x > 0) : Real.log (Real.exp x) = x := by
  rw [Real.log_exp]

example (x y : ℝ) (hx : x > 0) (hy : y > 0) : 
    Real.log (x * y) = Real.log x + Real.log y := by
  rw [Real.log_mul (by linarith) (by linarith)]

-- e的定义
example : Real.exp 1 = Real.e := by
  rfl

-- e的级数表示
example : Real.e = ∑' n : ℕ, (1 : ℝ) / n.factorial := by
  rw [Real.exp_eq_exp_1]
  simp [Real.exp]

end ExpAndLog

/-! 
## 紧致性与连续性

Heine-Borel定理相关内容。
-/

section Compactness

-- 紧致集
example (K : Set ℝ) : Prop := IsCompact K

-- 闭区间是紧致的（Heine-Borel）
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  apply isCompact_Icc

-- 紧致集上的连续函数达到最大值
example (f : ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K) 
    (hf : ContinuousOn f K) (hne : K.Nonempty) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  apply IsCompact.exists_isMaxOn hK hne hf

end Compactness

/-! 
## 练习

1. 证明：如果f在[a,b]上连续，在(a,b)内可导，且f(a) = f(b) = 0，
   那么存在c ∈ (a,b)使得f'(c) = 0。

2. 计算积分 ∫₀¹ x² dx = 1/3。

3. 证明：如果级数 Σ|aₙ| 收敛，则 Σaₙ 也收敛（绝对收敛蕴含条件收敛）。

4. 证明：对于任意x > 0，有 ln(x) ≤ x - 1。

5. 使用Taylor展开证明：e = lim_{n→∞} (1 + 1/n)^n。

-/ 

section Exercises

-- 练习2的提示
example : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  simp [intervalIntegral.integral_const, add_zero]
  norm_num

-- 练习4的提示
example (x : ℝ) (hx : x > 0) : Real.log x ≤ x - 1 := by
  apply Real.log_le_sub_one_of_pos
  exact hx

end Exercises
