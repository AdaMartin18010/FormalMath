---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Fatou引理 (Fatou's Lemma)
---
# Fatou引理 (Fatou's Lemma)

## Mathlib4 引用

```lean
import Mathlib.MeasureTheory.Integral.Bochner

namespace FatouLemma

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fatou引理：积分的下半连续性 -/
theorem fatou_lemma {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf f atTop x ∂μ ≤ liminf (λ n => ∫⁻ x, f n x ∂μ) atTop := by
  -- liminf的可测性和单调收敛
  sorry

/-- 控制收敛定理的特殊情形 -/
theorem fatou_implication {f : ℕ → X → E} {g : X → ℝ≥0∞} (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, ∃ l, Tendsto (λ n => f n x) atTop (𝓝 l)) :
    ‖∫ x, lim f atTop x ∂μ‖ ≤ liminf (λ n => ‖∫ x, f n x ∂μ‖) atTop := by
  -- 应用Fatou到范数
  sorry

end FatouLemma
```

## 数学背景

Fatou引理由Pierre Fatou在1906年证明，是测度论中关于函数列下极限积分的基本不等式。它是证明单调收敛定理和控制收敛定理的基础工具。

## 应用

- 控制收敛定理的证明
- 下半连续性结果
- 变分法中的极小化序列

---

*最后更新：2026-04-03 | 版本：v1.0.0*
