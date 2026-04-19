---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 单调收敛定理 (Monotone Convergence Theorem)
---
# 单调收敛定理 (Monotone Convergence Theorem)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.Bochner

namespace MonotoneConvergence

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Levi单调收敛定理 -/
theorem monotone_convergence {f : ℕ → X → E} (hf : ∀ n, Integrable (f n) μ)
    (hmono : ∀ n, ∀ᵐ x ∂μ, f n x ≤ f (n+1) x)
    (hbdd : ∃ g, Integrable g μ ∧ ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x) :
    Tendsto (λ n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, limsup f atTop x ∂μ)) := by
  -- 构造极限函数
  sorry

/-- 非负函数的单调收敛 -/
theorem monotone_convergence_nn {f : ℕ → X → ℝ≥0} (hf : ∀ n, Measurable (f n))
    (hmono : ∀ n, ∀ᵐ x ∂μ, f n x ≤ f (n+1) x) :
    Tendsto (λ n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, ⨆ n, f n x ∂μ)) := by
  sorry

end MonotoneConvergence
```

## 数学背景

单调收敛定理由Beppo Levi在1906年证明，是测度论中关于递增函数列积分极限的基本结果。它是证明控制收敛定理的基础，也是建立 $L^p$ 空间完备性的关键工具。

## 形式化表述

设 $f_n \uparrow f$ a.e.，$f_n \geq 0$。则 $\int f_n \to \int f$。

## 应用

- 控制收敛定理的证明
- $L^p$ 空间的完备性
- Fatou引理

---

*最后更新：2026-04-03 | 版本：v1.0.0*
