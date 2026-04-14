---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Moser同痕定理 (Moser Isotopy Theorem)
---
# Moser同痕定理 (Moser Isotopy Theorem)

## Mathlib4 引用

```lean
import Mathlib.Geometry.Symplectic.Basic
import Mathlib.Geometry.Manifold.Isotopy

namespace MoserIsotopy

variable {M : Type*} [SmoothManifoldWithCorners (𝓡 (2n)) M]

/-- Moser同痕定理：同调辛形式间的同痕 -/
theorem moser_isotopy {ω₀ ω₁ : SymplecticForm M} (hcohom : ∃ α, d α = ω₁ - ω₀)
    (hcompact : IsCompact M) :
    ∃ φ : Isotopy (Diffeomorphism M M) 0 1,
      φ 0 = id ∧ ∀ t, (φ t)* ω₀ = (1-t) • ω₀ + t • ω₁ := by
  -- Moser技巧：构造向量场
  sorry

/-- Darboux定理的Moser证明 -/
theorem darboux_via_moser (ω : SymplecticForm M) (x : M) :
    ∃ (U : OpenNhds x) (φ : U ≃ᵐ OpenBall 0 1), φ* ω = ω_std := by
  -- 应用Moser技巧
  sorry

end MoserIsotopy
```

## 数学背景

Moser同痕定理由Jürgen Moser在1965年证明，是辛几何中关于辛形式形变的基本结果。它表明同调的两个辛形式可以通过微分同胚同痕联系。这是证明Darboux定理和理解辛拓扑"柔性"的关键工具。

## 直观解释

Moser定理告诉我们：**如果两个辛形式在"拓扑上"相同（同调），那么它们在"几何上"也相同（同痕）**。

这显示了辛结构的刚性：不是每个闭2-形式都能变成辛形式，但一旦是辛形式，其同调类决定了局部几何。

## 形式化表述

设 $\omega_0, \omega_1$ 是辛形式，$[\omega_0] = [\omega_1] \in H^2_{dR}(M)$。

则存在微分同胚同痕 $\phi_t$ 使得 $\phi_1^* \omega_0 = \omega_1$。

## 应用

- Darboux定理的证明
- 辛结构的稳定性
- 辛拓扑的形变理论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
