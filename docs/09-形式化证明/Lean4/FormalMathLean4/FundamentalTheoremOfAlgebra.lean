import Mathlib
-- Framework for FundamentalTheoremOfAlgebra

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Analysis.Complex.Polynomial`
- 模块 / Module: `Mathlib.FieldTheory.IsAlgClosed.Basic`
- 定理 / Theorem: `Complex.exists_root`
- 定理 / Theorem: `Complex.isAlgebraicallyClosed`
-/

#check Complex.exists_root

-- Fundamental Theorem of Algebra: every non-constant complex polynomial has a root
-- 代数基本定理：每个次数大于0的复系数多项式在复数域中至少有一个根
-- Mathlib4 已经完整证明了这个定理，使用Liouville定理的分析证明方法。
theorem FundamentalTheoremOfAlgebra {n : ℕ} (hn : n > 0) (p : Polynomial ℂ) (hdeg : p.natDegree = n) :
    ∃ z : ℂ, p.IsRoot z := by
  have hp : p ≠ 0 := by
    by_contra h
    rw [h] at hdeg
    simp at hdeg
    linarith
  have hdeg' : 0 < p.degree := by
    rw [Polynomial.degree_eq_natDegree hp, hdeg]
    exact_mod_cast hn
  exact Complex.exists_root hdeg'
