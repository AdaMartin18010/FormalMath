/-
# 确界原理与 Archimedean 性质 / Supremum Principle and Archimedean Property

## Mathlib4 对应
- **模块**: `Mathlib.Data.Real.Basic`, `Mathlib.Order.CompleteLattice`
- **核心定理**: `Real.exists_isLUB`, `Real.exists_isGLB`, `Archimedean.arch`

## 定理陈述
1. **确界原理**: 任何非空有上界的实数集必有上确界（最小上界）。
2. **Archimedean 性质**: 对任意正实数 $x$ 和 $y$，存在自然数 $n$ 使得 $n \cdot x > y$。

## 数学意义
确界原理是实数完备性的核心体现，是分析学中极限理论、闭区间套定理、紧致性等概念的基石。
Archimedean 性质则保证了实数中没有无穷大或无穷小的元素。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice

namespace SupremumPrinciple

open Real Set

-- 确界原理：非空有上界的实数集必有上确界
theorem supremum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ s : ℝ, IsLUB S s := by
  /- 这是实数完备性的直接推论，Mathlib4 中由 Real 的完备格结构保证 -/
  exact Real.exists_isLUB S hne hbdd

-- 下确界原理：非空有下界的实数集必有下确界
theorem infimum_principle (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S) :
    ∃ s : ℝ, IsGLB S s := by
  exact Real.exists_isGLB S hne hbdd

-- Archimedean 性质
theorem archimedean_property (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ∃ n : ℕ, y < n * x := by
  /- 利用实数的 Archimedean 结构 -/
  rcases Archimedean.arch y hx with ⟨n, hn⟩
  use n
  exact hn

-- 等价表述：对任意实数 x，存在自然数 n 使得 n > x
theorem archimedean_nat (x : ℝ) : ∃ n : ℕ, x < n := by
  rcases exists_nat_gt x with ⟨n, hn⟩
  use n
  exact hn

-- 有理数在实数中稠密（由 Archimedean 性质导出）
theorem rationals_dense (x y : ℝ) (hxy : x < y) :
    ∃ q : ℚ, x < q ∧ q < y := by
  exact exists_rat_btwn hxy

end SupremumPrinciple
