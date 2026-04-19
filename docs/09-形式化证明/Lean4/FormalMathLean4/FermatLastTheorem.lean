import Mathlib
-- Framework stub for FermatLastTheorem

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.NumberTheory.FLT.Basic`
- 定理 / Theorem: `FermatLastTheorem`
-/

#check FermatLastTheorem

-- Fermat's Last Theorem: not yet fully formalized in mathlib4
theorem FermatLastTheorem_formal {n : ℕ} (hn : n > 2) (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ n + b ^ n ≠ c ^ n := by sorry

