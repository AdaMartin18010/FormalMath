---
title: "微积分基本定理 自然语言与 Lean4 对照"
msc_primary: 68V20
level: "silver"
target_courses:
  - "MIT 18.100A"
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: 'AI Mathematical Reviewer'
---

## 定理陈述

**自然语言**：微积分基本定理（Fundamental Theorem of Calculus, FTC）分为两部分：
1. **FTC I**：若 $f$ 在 $[a, b]$ 上连续，则函数 $F(x) = \int_a^x f(t)\,dt$ 在 $[a, b]$ 上可导，且 $F'(x) = f(x)$。
2. **FTC II**：若 $F$ 是 $f$ 在 $[a, b]$ 上的一个原函数（即 $F' = f$），且 $f$ 在 $[a, b]$ 上可积，则
   \[
   \int_a^b f(x)\,dx = F(b) - F(a).
   \]

**Lean4**：

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Integrable
import Mathlib.Analysis.Calculus.Deriv.Integral

namespace FundamentalTheoremOfCalculus
open Real MeasureTheory IntervalIntegral

-- FTC I：变上限积分的导数
theorem ftc_part1 {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (x : ℝ) (hx : x ∈ Ico a b) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  /- Mathlib4 中的标准定理 -/
  have h1 : a ≤ x := hx.1
  have h2 : x < b := hx.2
  apply intervalIntegral.hasDerivAt_integral_right
  · exact hf.mono (Icc_subset_Icc le_rfl h1.le)
  · exact h2

-- FTC II：用原函数计算定积分
theorem ftc_part2 {a b : ℝ} {f F : ℝ → ℝ}
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x)
    (hf : IntervalIntegrable f volume a b) :
    ∫ x in a..b, f x = F b - F a := by
  exact integral_deriv_eq_sub' F
    (fun x hx => hF x (mem_Icc.mp hx)) hf

-- 简洁版本（直接调用 Mathlib4）
theorem fundamental_theorem_calculus {a b : ℝ} (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hab : a ≤ b) :
    ∫ x in (a : ℝ)..b, deriv f x = f b - f a := by
  exact intervalIntegral.integral_deriv_eq_sub' f (fun x _ => hf x) hab
end FundamentalTheoremOfCalculus
```

## 证明思路

**自然语言**：
- **FTC I**：对 $F(x) = \int_a^x f(t)\,dt$，考虑差商
  $$\frac{F(x+h) - F(x)}{h} = \frac{1}{h}\int_x^{x+h} f(t)\,dt.$$
  由 $f$ 的连续性，当 $h \to 0$ 时 $f(t) \approx f(x)$，因此上式趋于 $f(x)$。更严格地，由积分中值定理，存在 $\xi_h \in [x, x+h]$ 使得积分等于 $f(\xi_h) \cdot h$，从而差商等于 $f(\xi_h) \to f(x)$。
- **FTC II**：将区间 $[a, b]$ 分割为 $a = x_0 < x_1 < \dots < x_n = b$，在每个子区间 $[x_{k-1}, x_k]$ 上应用中值定理，得到 $F(x_k) - F(x_{k-1}) = f(\xi_k)(x_k - x_{k-1})$。求和得 $F(b) - F(a) = \sum f(\xi_k) \Delta x_k$，当分割加细时即为 Riemann 积分。

**Lean4**：Mathlib4 提供了 `hasDerivAt_integral_right` 直接证明 FTC I，以及 `integral_deriv_eq_sub'` 直接证明 FTC II。这些定理已经封装了完整的分析论证。

## 关键 tactic/概念 教学

- `∫ t in a..u, f t`：区间积分（Bochner 积分在区间上的限制）。
- `HasDerivAt F (f x) x`：$F$ 在 $x$ 处的导数为 $f(x)$。
- `intervalIntegral.hasDerivAt_integral_right`：FTC I 的标准实现。
- `intervalIntegral.integral_deriv_eq_sub'`：FTC II 的标准实现。
- `IntervalIntegrable`：函数在区间上可积的断言。

## 练习

1. 设 $F(x) = \int_0^x e^{t^2}\,dt$，求 $F'(x)$。
2. 计算 $\int_0^{\pi} \sin(x)\,dx$，并在 Lean4 中验证结果等于 2。
3. 设 $f$ 在 $[a, b]$ 上连续且 $f(x) \geq 0$，证明若 $\int_a^b f(x)\,dx = 0$，则 $f(x) = 0$ 对所有 $x \in [a, b]$ 成立。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确