---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Gauss引理 (Gauss's Lemma)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Content

namespace GaussLemma

variable {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]

/-- Gauss引理：本原多项式的乘积仍本原 -/
theorem gauss_lemma_primitive {p q : Polynomial R} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  -- 反证法：假设有素因子
  sorry

/-- 多项式可约性在分式域和原环的关系 -/
theorem irreducible_of_fraction_field {p : Polynomial R} (hp : p.IsPrimitive) :
    Irreducible p ↔ Irreducible (map (algebraMap R (FractionRing R)) p) := by
  sorry

end GaussLemma
```

## 数学背景

Gauss引理由Carl Friedrich Gauss证明，是多项式理论的基本结果。它表明本原多项式（系数的最大公因子为单位）的乘积仍是本原的，并建立了整环上的可约性与其分式域上的可约性之间的关系。

## 应用

- Eisenstein判别法的证明
- 唯一分解整环上的多项式环仍是UFD
- 代数数论中的整性判定

---

*最后更新：2026-04-03 | 版本：v1.0.0*
