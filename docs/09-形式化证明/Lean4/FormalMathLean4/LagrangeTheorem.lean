import Mathlib
/-
# 拉格朗日定理的形式化证明 / Formalization of Lagrange's Theorem

## Mathlib4对应
- **模块**: `Mathlib.GroupTheory.Index`
- **核心定理**: `Subgroup.index_mul_card`
- **相关定义**: 
  - `Subgroup.index`: 子群的指数
  - `leftCoset`: 左陪集
  - `QuotientGroup`: 商群

## 定理陈述
设 G 是有限群，H 是 G 的子群，则 |H| 整除 |G|，且 |G| = [G:H] · |H|

其中 [G:H] 称为子群 H 在 G 中的指数，等于左陪集的个数。

## 历史背景
拉格朗日定理是群论中最基本的定理之一，由约瑟夫·拉格朗日在1771年证明。
该定理表明子群的阶总是整除群的阶，这是有限群分类理论的基础。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.GroupTheory.Index`
- 模块 / Module: `Mathlib.GroupTheory.Coset.Card`
- 定理 / Theorem: `Subgroup.index_mul_card`
-/

#check Subgroup.index_mul_card

-- Lagrange's Theorem: |G| = [G:H] · |H|
theorem LagrangeTheorem {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card G = H.index * Nat.card H := by
  rw [Subgroup.index_mul_card]

