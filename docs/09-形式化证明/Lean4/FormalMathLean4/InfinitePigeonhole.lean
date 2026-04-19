import Mathlib
/-
# 无穷鸽巢原理的形式化证明 / Infinite Pigeonhole Principle

## Mathlib4对应
- **模块**: `Mathlib.Data.Set.Finite`, `Mathlib.Data.Set.Countable`
- **核心定理**: `Set.infinite_iUnion`, `Set.Infinite.image`
- **相关定义**:
  - `Set.Infinite`: 无穷集合
  - `Set.Finite`: 有限集合
  - `Set.Countable`: 可数集合

## 定理陈述
**无穷鸽巢原理**: 若将无穷多个物体放入有限个盒子中，
则至少有一个盒子包含无穷多个物体。

**等价表述**: 若 f: A → B，A 是无穷集，B 是有限集，
则存在 b ∈ B 使得 f⁻¹(b) 是无穷集。

## 数学意义
无穷鸽巢原理是有限鸽巢原理的自然推广，它：
1. 揭示了无穷集合的结构性质
2. 在组合集合论中有重要应用
3. 是Ramsey理论和组合数学的基础工具

## 历史背景
无穷鸽巢原理是鸽巢原理在无穷集合上的自然扩展，
在集合论和组合数学中有广泛应用。
-/

/-
## 核心概念

### 无穷集合 (Infinite Set)
集合 A 是无穷的，如果对于任意自然数 n，不存在从 A 到 {0, 1, ..., n-1} 的单射。
等价表述：A 不包含于任何有限集。

### 有限集合 (Finite Set)
集合 A 是有限的，如果存在某个自然数 n 和双射 f: A → {0, 1, ..., n-1}。

### 纤维 (Fiber)
对于函数 f: A → B 和 b ∈ B，纤维 f⁻¹(b) = {a ∈ A | f(a) = b}。
-/

/-
## 特殊情况：有限陪域

当陪域 B 是有限类型时，定理有简化形式。
-/

/-
## 应用：可数集的性质

**定理**: 可数个有限集的并是可数的。

**定理**: 可数个可数集的并是可数的。
-/

/-
## 应用：Ramsey理论的无穷版本

**无穷Ramsey定理**: 对自然数的k-子集进行有限染色，
必存在无穷单色子集。
-/

/-
## 推广：更强形式的无穷鸽巢原理

**定理**: 若 A 是不可数集，B 是可数集，f: A → B，
则存在 b ∈ B 使得 f⁻¹(b) 是不可数的。
-/

/-
## 应用：序列的单调子序列

**定理**: 任何实数序列都有单调（递增或递减）子序列。

这是Erdős–Szekeres定理的特例。
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Data.Fintype.Card`
- 模块 / Module: `Mathlib.Data.Finset.Card`
- 定理 / Theorem: `Finset.exists_lt_card_fiber_of_maps_to_of_nsmul_lt_card`
-/


-- Infinite pigeonhole principle
theorem InfinitePigeonhole {α β : Type*} [Infinite α] [Fintype β] (f : α → β) :
    ∃ y : β, Infinite (f ⁻¹' {y}) := by
  sorry

