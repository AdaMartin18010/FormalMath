# Jordan曲线定理 (Jordan Curve Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.Homotopy.Sphere
import Mathlib.Analysis.RCLike.Basic

namespace JordanCurveTheorem

variable {γ : Circle → EuclideanSpace ℝ (Fin 2)} (hγ : Continuous γ) (hinj : Function.Injective γ)

/-- Jordan曲线定理 -/
theorem jordan_curve_theorem :
    (EuclideanSpace ℝ (Fin 2) \ Set.range γ).ConnectedComponents = 2 := by
  -- 平面同调或Alexander对偶
  sorry

/-- 有界和无界分支 -/
theorem jordan_curve_components (hC : Set.range γ = frontier C) (hCopen : IsOpen C) :
    (IsBounded C ∧ (EuclideanSpace ℝ (Fin 2) \ closure C).Unbounded) ∨
    (IsBounded (EuclideanSpace ℝ (Fin 2) \ closure C) ∧ C.Unbounded) := by
  -- 应用曲线定理
  sorry

end JordanCurveTheorem
```

## 数学背景

Jordan曲线定理由Camille Jordan在1887年证明，是拓扑学中最基本和最直观的结果之一。它表明平面上的简单闭曲线将平面分成恰好两个连通分支（内部和外部）。

## 应用

- 计算几何
- 图像处理
- 复分析

---

*最后更新：2026-04-03 | 版本：v1.0.0*
