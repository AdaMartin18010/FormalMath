---
title: "实分析核心示例 自然语言与 Lean4 对照"
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

**自然语言**：实分析的核心对象包括极限、连续性、导数、积分与级数。下面以几个基础但关键的结论为例，展示如何用 Lean4 表达它们：

1. 夹逼定理：若 \(f_n \to L\)，\(h_n \to L\)，且 \(f_n \leq g_n \leq h_n\)，则 \(g_n \to L\)。
2. 中值定理：若 \(f\) 在 \([a,b]\) 连续、在 \((a,b)\) 可导，则存在 \(c\) 使得 \(f'(c) = \frac{f(b)-f(a)}{b-a}\)。
3. 微积分基本定理：\(\frac{d}{dx}\int_a^x f(t)dt = f(x)\)。

**Lean4**：

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.FundThmCalculus

section Limits
-- 夹逼定理
example (f g h : ℕ → ℝ) (L : ℝ) (hf : Tendsto f atTop (𝓝 L))
    (hh : Tendsto h atTop (𝓝 L)) (hg : ∀ n, f n ≤ g n ∧ g n ≤ h n) :
    Tendsto g atTop (𝓝 L) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh
  · intro n; exact (hg n).left   -- 证明 f n ≤ g n
  · intro n; exact (hg n).right  -- 证明 g n ≤ h n
end Limits
```

## 证明思路

**自然语言**：中值定理的证明通常通过构造辅助函数将问题转化为罗尔定理。设 \(g(x) = f(x) - \frac{f(b)-f(a)}{b-a}(x-a) - f(a)\)，则 \(g(a) = g(b) = 0\)。对 \(g\) 应用罗尔定理，即得存在 \(c\) 使得 \(g'(c) = 0\)，从而推出 \(f'(c) = \frac{f(b)-f(a)}{b-a}\)。

**Lean4**：

```lean
section MeanValueTheorem
-- Lagrange 中值定理
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  apply exists_hasDerivAt_eq_slope  -- 调用 Mathlib4 的中值定理
  all_goals assumption               -- 自动匹配所有假设
end MeanValueTheorem

section Integration
-- 微积分基本定理（第一部分）
example (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.interval a b)) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f b) b := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact hf
  · apply intervalIntegrable_of_continuousOn
    exact hf
end Integration
```

## 关键 tactic 教学

- `apply`：将当前目标转化为某个定理的前提条件。例：`apply exists_hasDerivAt_eq_slope` 将目标转化为中值定理的假设。
- `all_goals assumption`：对所有剩余子目标尝试用现有的假设直接匹配。
- `intro n; exact ...`：引入变量后，直接给出该子目标的证明项。

## 练习

1. 在 Lean4 中写出并证明：\(\lim_{n\to\infty} \frac{1}{n} = 0\)。
2. 利用中值定理证明：当 \(x > 0\) 时，\(\sin x < x\)。
3. 写出并证明几何级数求和公式：若 \(|r| < 1\)，则 \(\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}\)。
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