---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Sard定理 (Sard's Theorem)
---
# Sard定理 (Sard's Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace SardTheorem

variable {M N : Type*} [SmoothManifoldWithCorners (𝓡 m) M] [SmoothManifoldWithCorners (𝓡 n) N]
variable {f : M → N} [ContMDiff ℝ ∞ f]

/-- Sard定理：光滑映射临界值的测度为零 -/
theorem sard_theorem (hmn : m ≤ n) :
    MeasureZero (HausdorffMeasure n) (CriticalValues f) := by
  -- 局部化和Fubini论证
  sorry

/-- 光滑映射的正则值稠密 -/
theorem regular_values_dense :
    Dense (RegularValues f) := by
  -- Sard定理的推论
  sorry

end SardTheorem
```

## 数学背景

Sard定理由Arthur Sard在1942年证明，是微分拓扑的基本结果。它表明光滑映射的临界值（像测度为零）"很小"，因此正则值稠密。这是横截性理论和微分拓扑中许多存在性结果的基础。

## 应用

- 横截性定理
- Whitney嵌入定理
- Morse理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
