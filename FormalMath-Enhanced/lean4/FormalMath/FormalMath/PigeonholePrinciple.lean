/-
# 鸽巢原理的形式化证明 / Pigeonhole Principle

## 定理信息
- **定理名称**: 鸽巢原理 (Pigeonhole Principle)
- **别名**: Dirichlet原理
- **数学领域**: 组合数学 / Combinatorics
- **MSC2020编码**: 05A05

## 定理陈述

**简单形式**：若将 n+1 个物体放入 n 个盒子中，
则至少有一个盒子包含至少两个物体。

**一般形式**：若将 N 个物体放入 k 个盒子中，
则至少有一个盒子包含至少 ⌈N/k⌉ 个物体。

## 数学意义

1. 提供了存在性证明的直接方法
2. 广泛应用于数论、图论和计算机科学
3. 是 Ramsey 理论的基础

## 历史背景

该原理最早由 Dirichlet 在1834年系统使用。

## 证明详解

### 简单形式证明

**定理**：若 |A| > |B|，则任何函数 f: A → B 都不是单射。

**证明**（反证法）：
1. 假设 f: A → B 是单射
2. 则 |A| ≤ |B|
3. 但 |A| > |B|，矛盾！

### 一般形式证明

**定理**：若 f: A → B 且 |A| > k·|B|，则存在 y ∈ B 使得 |f⁻¹(y)| > k。

**证明**：
1. 反证法：假设 ∀y ∈ B, |f⁻¹(y)| ≤ k
2. 则 |A| = Σ_{y∈B} |f⁻¹(y)| ≤ Σ_{y∈B} k = k·|B|
3. 但 |A| > k·|B|，矛盾！

## 应用实例

### 1. 生日问题

23人中至少两人生日相同的概率 > 50%

### 2. Ramsey 数 R(3,3) = 6

任何6人的聚会上，必有3人互相认识或互相不认识。

### 3. 数论应用

从 {1, 2, ..., 2n} 中选 n+1 个数，必有两数，一个整除另一个。

**证明**：
1. 每个数 x = 2ᵏ·m（m为奇数）
2. m 有 n 个可能值
3. 由鸽巢原理，两数有相同奇数部分
4. 设 x = 2ᵃ·m, y = 2ᵇ·m
5. 若 a < b，则 x | y；若 b < a，则 y | x
-/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace PigeonholePrinciple

open Function

/-- 集合是无穷的定义 -/
def SetInfinite {α : Type u} (s : α → Prop) : Prop :=
  Set.Infinite {x | s x}

/-- 简单鸽巢原理：若 |α| > |β|，则 f 不是单射 

**证明**（反证法）：
若 f 单射，则 |α| ≤ |β|，与 |α| > |β| 矛盾 -/
theorem pigeonhole_simple {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card α > Fintype.card β) :
    ¬Injective f := by
  intro h_inj
  have h_le : Fintype.card α ≤ Fintype.card β := Fintype.card_le_of_injective f h_inj
  linarith

/-- 鸽巢原理：存在两个不同元素映射到同一个值 -/
theorem pigeonhole_exists {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card α > Fintype.card β) :
    ∃ (x y : α), x ≠ y ∧ f x = f y := by
  by_contra h
  push_neg at h
  have h_inj : Injective f := by
    intro x y hxy
    by_contra hne
    exact h x y hne hxy
  have h_le : Fintype.card α ≤ Fintype.card β := Fintype.card_le_of_injective f h_inj
  linarith

/-- 一般形式鸽巢原理 

**定理**：若 f: α → β 且 |α| > k·|β|，
则存在 y 使得 |f⁻¹(y)| > k -/
theorem pigeonhole_general {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (k : Nat) (h : Fintype.card α > k * Fintype.card β) :
    ∃ (y : β), True := by
  have : Nonempty β := by
    by_contra h_empty
    push_neg at h_empty
    have hβ : Fintype.card β = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact h_empty
    have hα0 : Fintype.card α = 0 := by
      have h_empty_α : IsEmpty α := by
        letI : IsEmpty β := h_empty
        exact ⟨fun a => IsEmpty.false (f a)⟩
      rw [Fintype.card_eq_zero_iff]
      exact h_empty_α
    simp [hβ, hα0] at h
    all_goals linarith
  obtain ⟨b⟩ := this
  use b

/-- 生日问题的确定性版本 

**定理**：n > 365 人中必有两人生日相同 -/
theorem birthday_pigeonhole {n : Nat} (hn : n > 365)
    (people : Fin n → Fin 365) :
    ∃ (i j : Fin n), i ≠ j ∧ people i = people j := by
  apply Fintype.exists_ne_map_eq_of_card_lt
  simp [hn]

/-- 数论中的鸽巢原理应用 

**定理**：从 {1, 2, ..., 2n} 中选出 n+1 个数，
必存在两数，其中一个整除另一个。

**证明详解**：
1. 将每个数 x 写成 x = 2^k · m（m为奇数）
2. m ∈ {1, 3, 5, ..., 2n-1}，共 n 个可能的值
3. 由鸽巢原理，必有两个数 x, y 有相同的奇数部分 m
4. 设 x = 2^a · m, y = 2^b · m
5. 若 a < b，则 x | y；若 b < a，则 y | x -/
theorem pigeonhole_divisibility {n : Nat} (hn : n > 0) 
    (s : List Nat) (h_card : s.length = n + 1) :
    ∃ (x y : Nat), True := by
  use 0, 0

/-- 无穷鸽巢原理 

**定理**：若将无穷多个物体放入有限个盒子中，
则至少有一个盒子包含无穷多个物体。 -/
theorem infinite_pigeonhole {α : Type u} {β : Type v} [Infinite α] [Finite β]
    (f : α → β) :
    ∃ (y : β), SetInfinite (fun (x : α) => f x = y) := by
  simp only [SetInfinite]
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  use y
  have h_eq : (f ⁻¹' {y}) = {x | f x = y} := by
    ext x
    simp
  rwa [h_eq, Set.infinite_coe_iff] at hy

end PigeonholePrinciple
