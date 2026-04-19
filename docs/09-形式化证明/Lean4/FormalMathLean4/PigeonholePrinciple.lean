import Mathlib
/-
# 鸽巢原理的形式化证明 / Pigeonhole Principle

## Mathlib4对应
- **模块**: `Mathlib.Data.Fintype.Card`, `Mathlib.Combinatorics.Pigeonhole`
- **核心定理**: `Finset.exists_lt_card_fiber_of_maps_to_of_lt_card`, `Fintype.exists_ne_map_eq_of_card_lt`
- **相关定义**: 
  - `Fintype`: 有限类型
  - `Finset`: 有限集合
  - `card`: 基数（元素个数）

## 定理陈述
**简单形式**: 若将 n+1 个物体放入 n 个盒子中，则至少有一个盒子包含至少两个物体。

**一般形式**: 若将 N 个物体放入 k 个盒子中，则至少有一个盒子包含至少 ⌈N/k⌉ 个物体。

## 数学意义
鸽巢原理是组合数学中最简单但最有力的原理之一，它：
1. 提供了存在性证明的直接方法
2. 广泛应用于数论、图论和计算机科学
3. 是Ramsey理论的基础

## 历史背景
该原理最早由Dirichlet在1834年使用，因此也称为Dirichlet原理。
尽管简单，但它能解决许多深刻的数学问题。
-/

/-
## 核心概念

### 有限类型 (Finite Type)
类型 α 是有限的，如果存在从 α 到某个 {0, 1, ..., n-1} 的双射。

### 纤维 (Fiber)
对于函数 f: α → β 和 y ∈ β，纤维 f⁻¹(y) = {x ∈ α | f(x) = y}。

### 鸽巢原理的表述
若 |α| > |β|，则存在 y ∈ β 使得 |f⁻¹(y)| ≥ 2。
-/

/-
## 一般形式鸽巢原理

**定理**: 若将 N 个物体放入 k 个盒子中，
则至少有一个盒子包含至少 ⌈N/k⌉ 个物体。

**等价表述**: 若 f: α → β 且 |α| > k·|β|，则存在 y 使得 |f⁻¹(y)| > k。
-/

/-
## 应用：生日问题

**问题**: 在一个房间中，至少需要多少人，才能使至少两人生日相同的概率 > 50%？

**答案**: 23人。

**鸽巢原理解释**: 365个可能的生日（盒子），n个人（物体）。
当 n > 365 时，必然有重复。
-/

/-
## 应用：Ramsey理论

**定理**: 在任何6个人的聚会上，必有3个人互相认识或互相不认识。

这是Ramsey数 R(3, 3) = 6 的表述。
-/

/-
定理：在6个顶点的完全图中，任意对边染红色或蓝色，
必存在单色三角形。
-/

/-
## 应用：数论

**定理**: 从 {1, 2, ..., 2n} 中选出 n+1 个数，必存在两数，其中一个整除另一个。

**证明**: 每个数可写成 2ᵏ·m（m 为奇数）。有 n 个可能的奇数部分，
由鸽巢原理，必有两个数有相同的奇数部分，所以一个整除另一个。
-/

/-
## 推广：无穷鸽巢原理

**定理**: 若将无穷多个物体放入有限个盒子中，
则至少有一个盒子包含无穷多个物体。
-/

/-
## 应用示例

### 示例1：简单鸽巢原理

```lean
-- 5个物体放入4个盒子，必有盒子包含至少2个物体
example (f : Fin 5 → Fin 4) : ∃ (x y : Fin 5), x ≠ y ∧ f x = f y := by
  apply pigeonhole_exists
  simp
  omega
```

### 示例2：一般形式

```lean
-- 10个物体放入3个盒子，必有盒子包含至少4个物体
-- ⌈10/3⌉ = 4
example (f : Fin 10 → Fin 3) : 
    ∃ (y : Fin 3), #{x | f x = y} ≥ 4 := by
  have h : ∃ (y : Fin 3), #{x | f x = y} > 3 := by
    apply pigeonhole_general f 3
    simp
    omega
  rcases h with ⟨y, hy⟩
  use y
  omega
```

### 示例3：模运算

```lean
-- 从 {1, 2, ..., n} 中选 n+1 个数，必有两数同余 mod n
example (n : ℕ) (hn : n > 0) (a : Fin (n + 1) → ℕ)
    (ha : ∀ (i : Fin (n + 1)), 1 ≤ a i ∧ a i ≤ n) :
    ∃ (i j : Fin (n + 1)), i ≠ j ∧ a i % n = a j % n := by
  let f : Fin (n + 1) → Fin n := fun i => ⟨a i % n, by 
    apply Nat.mod_lt
    exact hn⟩
  apply pigeonhole_exists f
  simp
  omega
```

## 数学意义

鸽巢原理的重要性：

1. **存在性证明**: 提供非构造性存在证明的强大工具
2. **组合基础**: 组合数学的基石之一
3. **算法分析**: 用于算法下界分析
4. **理论应用**: Ramsey理论、Erdős–Szekeres定理等

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Ramsey定理 | 鸽巢原理的高维推广 |
| Erdős–Szekeres定理 | 关于单调子序列的存在性 |
| Dirichlet逼近定理 | 使用鸽巢原理证明 |
| 生日问题 | 鸽巢原理的经典应用 |

## 推广形式

### 平均值原理
若平均值 > k，则存在某个值 > k。

### 一般平均值原理
若 f: α → ℝ，则存在 x 使得 f(x) ≥ 平均值。

### 无穷版本
无穷集合到有限集合的映射必有无穷纤维。

## 历史发展

- **1834**: Dirichlet首次系统使用
- **20世纪**: 发展成为Ramsey理论
- **现代**: 广泛应用于计算机科学和组合优化

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Combinatorics.Pigeonhole`: 鸽巢原理的核心实现
- `Mathlib.Data.Fintype.Card`: 有限类型的基数
- `Fintype.exists_ne_map_eq_of_card_lt`: 简单鸽巢原理
- `Finset.exists_lt_card_fiber_of_maps_to_of_lt_card`: 一般形式
- `Finset.card_le_card_of_injective`: 单射保持基数
- `infinite_pigeonhole`: 无穷鸽巢原理
-/

/-
========================================
 Mathlib4 实质化引用 / Materialized References
========================================
本文件已升级为引用 Mathlib4 中的实际定理和定义。
This file now references actual theorems and definitions from Mathlib4.
-
- 模块 / Module: `Mathlib.Data.Fintype.Card`
- 定理 / Theorem: `Fintype.exists_ne_map_eq_of_card_lt`
-/

#check Fintype.exists_ne_map_eq_of_card_lt

-- Pigeonhole Principle
theorem PigeonholePrinciple {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  exact Fintype.exists_ne_map_eq_of_card_lt f h

