import Mathlib
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

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Data.Real.Basic`
- 模块 / Module: `Mathlib.Order.CompleteLattice`
- 定理 / Theorem: `Real.exists_isLUB`
-/

#check Real.exists_isLUB

-- Supremum Principle: every nonempty bounded above set of reals has a supremum
theorem SupremumPrinciple {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    ∃ x : ℝ, IsLUB S x := by
  exact Real.exists_isLUB hne hbdd

