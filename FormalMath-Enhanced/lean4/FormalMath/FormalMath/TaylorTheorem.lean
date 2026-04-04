/- 
# 泰勒定理（Taylor's Theorem）

## 数学背景

泰勒定理是微积分中的核心定理，它表明一个光滑函数可以用多项式来局部逼近。
对于n+1阶可导的函数f，在某点a附近有：

f(x) = f(a) + f'(a)(x-a) + f''(a)(x-a)²/2! + ... + f⁽ⁿ⁾(a)(x-a)ⁿ/n! + Rₙ(x)

其中Rₙ(x)是余项，可以表示为拉格朗日形式或柯西形式。

## Mathlib4对应
- `Mathlib.Analysis.Calculus.Taylor`
- `Mathlib.Analysis.Calculus.Deriv`
- `Mathlib.Analysis.Calculus.ContDiff`

## 证明思路
1. 构造泰勒多项式
2. 定义余项函数
3. 应用柯西中值定理
4. 通过归纳法得到一般形式
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace TaylorTheorem

open Real Polynomial

variable {f : ℝ → ℝ} {a x : ℝ} {n : ℕ}

/- 
## 泰勒多项式定义

n阶泰勒多项式在点a处的定义：
T_n(x) = Σ(k=0 to n) [f⁽ᵏ⁾(a) / k!] · (x-a)ᵏ

这是一个关于(x-a)的n次多项式。
-/
def taylorPolynomial (f : ℝ → ℝ) (a : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k in Finset.range (n + 1), 
    (C (iteratedDeriv k f a) / C (Nat.factorial k : ℝ)) * (X - C a) ^ k

/- 
## 拉格朗日余项

泰勒公式的拉格朗日余项形式：
Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ) / (n+1)! · (x-a)ⁿ⁺¹

其中ξ是介于a和x之间的某个点。
-/
def lagrangeRemainder (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) (ξ : ℝ) : ℝ :=
  iteratedDeriv (n + 1) f ξ / Nat.factorial (n + 1) * (x - a) ^ (n + 1)

/-
## 泰勒定理（带拉格朗日余项）

**定理陈述**：设函数f在区间[a,x]上有连续的n+1阶导数，则存在ξ∈(a,x)使得：

f(x) = Σ(k=0 to n)[f⁽ᵏ⁾(a)/k!]·(x-a)ᵏ + Rₙ(x)

其中余项Rₙ(x) = f⁽ⁿ⁺¹⁾(ξ)/(n+1)!·(x-a)ⁿ⁺¹

**证明要点**：
1. 构造辅助函数g(t) = f(x) - Σ(k=0 to n)[f⁽ᵏ⁾(t)/k!]·(x-t)ᵏ
2. 计算g(a) = Rₙ(x)和g(x) = 0
3. 应用柯西中值定理
4. 通过递推得到余项表达式
-/
theorem taylor_theorem_lagrange 
    (hf : ContDiffOn ℝ (n + 1) f (Icc a x))
    (hax : a ≤ x) :
    ∃ ξ ∈ Icc a x, 
      f x = (taylorPolynomial f a n).eval x + lagrangeRemainder f a x n ξ := by
  -- 使用Mathlib中已经证明的泰勒定理
  have h := taylor_mean_remainder_lagrange hf hax (by linarith)
  rcases h with ⟨ξ, hξ_mem, hξ_eq⟩
  use ξ, hξ_mem
  -- 余项形式的转换
  simp only [taylorPolynomial, lagrangeRemainder, eval_sum, eval_mul, eval_C, 
             eval_sub, eval_X, eval_pow]
  rw [hξ_eq]
  field_simp
  ring

/-
## 泰勒定理（带积分余项）

积分形式的余项：
Rₙ(x) = ∫ₐˣ [f⁽ⁿ⁺¹⁾(t)/n!]·(x-t)ⁿ dt

这种形式在某些应用中更为方便。
-/
def integralRemainder (f : ℝ → ℝ) (a x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in a..x, iteratedDeriv (n + 1) f t / Nat.factorial n * (x - t) ^ n

/-
## 积分余项形式

**定理陈述**：若f⁽ⁿ⁺¹⁾在[a,x]上连续，则：

f(x) = Σ(k=0 to n)[f⁽ᵏ⁾(a)/k!]·(x-a)ᵏ + ∫ₐˣ[f⁽ⁿ⁺¹⁾(t)/n!]·(x-t)ⁿdt
-/
theorem taylor_theorem_integral
    (hf : ContDiffOn ℝ (n + 1) f (Icc a x))
    (hax : a ≤ x) :
    f x = (taylorPolynomial f a n).eval x + integralRemainder f a x n := by
  -- 应用积分形式的泰勒定理
  rw [integralRemainder]
  have h := taylor_series_remainder_integral hf hax
  simpa using h

/-
## 泰勒展开的收敛性

当n→∞时，若余项趋于0，则得到泰勒级数展开：
f(x) = Σ(k=0 to ∞)[f⁽ᵏ⁾(a)/k!]·(x-a)ᵏ

**收敛条件**：
- f必须是解析函数（analytic）
- 余项在n→∞时趋于0
-/
theorem taylor_series_convergence
    {f : ℝ → ℝ} {a : ℝ} {r : NNReal}
    (hf : AnalyticOnNhd ℝ f (ball a r))
    (hx : x ∈ ball a r) :
    HasSum (fun k ↦ iteratedDeriv k f a / Nat.factorial k * (x - a) ^ k) (f x) := by
  -- 解析函数的泰勒级数收敛到函数本身
  exact hf.hasSum_taylorSeries hx

end TaylorTheorem
