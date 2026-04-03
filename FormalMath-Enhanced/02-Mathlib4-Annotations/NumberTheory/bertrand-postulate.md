---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Bertrand假设 (Bertrand's Postulate)

## Mathlib4 引用

```lean
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand

namespace BertrandPostulate

/-- Bertrand假设：n和2n之间必有素数 -/
theorem bertrand_postulate (n : ℕ) (hn : 1 < n) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p < 2 * n := by
  -- Chebyshev估计和二项式系数分析
  sorry

/-- 强化形式 -/
theorem stronger_bertrand (n : ℕ) (hn : 25 ≤ n) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p < (6/5) * n := by
  -- 更精细的估计
  sorry

end BertrandPostulate
```

## 数学背景

Bertrand假设由Joseph Bertrand在1845年猜想，Pafnuty Chebyshev在1850年证明。它表明对任意 $n > 1$，在 $n$ 和 $2n$ 之间总存在素数。虽然这已被证明是素数定理的推论，但Chebyshev的初等证明仍然很有价值。

## 应用

- 素数分布的精细结果
- 算法分析
- 组合数论

---

*最后更新：2026-04-03 | 版本：v1.0.0*
