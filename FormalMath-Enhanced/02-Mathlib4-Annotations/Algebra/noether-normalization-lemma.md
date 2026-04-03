---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Noether正规化引理 (Noether Normalization Lemma)

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.Localization.Basic

namespace NoetherNormalizationLemma

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- Noether正规化引理 -/
theorem noether_normalization [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (y : Fin n → A),
      Algebra.Independent k y ∧ Algebra.IsIntegral (MvPolynomial (Fin n) k) A := by
  -- 对生成元个数归纳
  sorry

/-- 几何解释：仿射代数的有限映射 -/
theorem geometric_interpretation [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (φ : Spec A → AffineSpace k n),
      IsFinite φ ∧ IsSurjective φ := by
  -- 对应Noether正规化
  sorry

end NoetherNormalizationLemma
```

## 数学背景

Noether正规化引理由Emmy Noether在1926年证明，是交换代数和代数几何的基本结构定理。它表明有限生成代数在适当坐标变换后，可表示为多项式环上的整扩张。

## 应用

- Hilbert零点定理的证明
- 维数理论
- 代数几何的参数化

---

*最后更新：2026-04-03 | 版本：v1.0.0*
