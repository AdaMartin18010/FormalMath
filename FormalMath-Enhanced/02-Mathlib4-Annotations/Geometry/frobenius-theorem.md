---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: Frobenius定理 (Frobenius Theorem)
---
# Frobenius定理 (Frobenius Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Manifold.Distribution
import Mathlib.Geometry.Manifold.Frobenius

namespace FrobeniusTheorem

variable {M : Type*} [SmoothManifoldWithCorners (𝓡 n) M]
variable {D : Distribution M k} (hinvolutive : D.IsInvolutive)

/-- Frobenius定理：可积分布存在积分叶状结构 -/
theorem frobenius_theorem (x : M) :
    ∃ (U : OpenNhds x) (F : Foliation U k),
      ∀ y ∈ U, TangentSpace (Leaf F y) y = D y := by
  -- 归纳法和常秩定理
  sorry

/-- 全局形式 -/
theorem frobenius_global [M.Compact] :
    ∃ F : Foliation M k, ∀ x, TangentSpace (Leaf F x) x = D x := by
  -- 局部结果拼接
  sorry

end FrobeniusTheorem
```

## 数学背景

Frobenius定理由Ferdinand Georg Frobenius在1877年证明，是微分几何中关于分布可积性的基本结果。它表明流形上的光滑分布可积（存在积分叶状结构）当且仅当它是可积的（对Lie括号封闭）。这是偏微分方程理论和Lie群论的基础。

## 应用

- 偏微分方程的可积性条件
- Lie群和Lie代数
- 控制理论
- 杨-Mills理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
