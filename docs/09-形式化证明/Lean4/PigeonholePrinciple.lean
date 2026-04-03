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

import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

universe u v

namespace PigeonholePrinciple

open Finset Fintype Function

/-
## 核心概念

### 有限类型 (Finite Type)
类型 α 是有限的，如果存在从 α 到某个 {0, 1, ..., n-1} 的双射。

### 纤维 (Fiber)
对于函数 f: α → β 和 y ∈ β，纤维 f⁻¹(y) = {x ∈ α | f(x) = y}。

### 鸽巢原理的表述
若 |α| > |β|，则存在 y ∈ β 使得 |f⁻¹(y)| ≥ 2。
-/

-- 简单鸽巢原理：若 |α| > |β|，则 f 不是单射
theorem pigeonhole_simple {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : card α > card β) :
    ¬Injective f := by
  /- 证明思路：若 f 单射，则 |α| ≤ |β|，矛盾 -/
  intro h_inj
  have h_le : card α ≤ card β := by
    apply card_le_card_of_injective f h_inj
  linarith

-- 鸽巢原理：存在两个不同元素映射到同一个值
theorem pigeonhole_exists {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (h : card α > card β) :
    ∃ (x y : α), x ≠ y ∧ f x = f y := by
  /- 使用Mathlib4的鸽巢原理 -/
  apply Fintype.exists_ne_map_eq_of_card_lt
  exact h

/-
## 一般形式鸽巢原理

**定理**: 若将 N 个物体放入 k 个盒子中，
则至少有一个盒子包含至少 ⌈N/k⌉ 个物体。

**等价表述**: 若 f: α → β 且 |α| > k·|β|，则存在 y 使得 |f⁻¹(y)| > k。
-/

-- 一般形式鸽巢原理
theorem pigeonhole_general {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : ℕ) (h : card α > k * card β) :
    ∃ (y : β), #{x | f x = y} > k := by
  /- 证明思路（反证法）：
     假设对所有 y，|f⁻¹(y)| ≤ k
     则 |α| = Σ|f⁻¹(y)| ≤ k·|β|，矛盾
  -/
  by_contra h_all
  push_neg at h_all
  
  /- 计算总元素数 -/
  have h_sum : ∑ y : β, #{x | f x = y} = card α := by
    /- 这是纤维分解 -/
    sorry
  
  /- 每个纤维大小 ≤ k -/
  have h_le : ∑ y : β, #{x | f x = y} ≤ k * card β := by
    sorry
  
  /- 矛盾 -/
  linarith [h_sum, h_le, h]

-- 鸽巢原理的平均形式
theorem pigeonhole_average {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → β) :
    ∃ (y : β), #{x | f x = y} * card β ≥ card α := by
  /- 平均纤维大小为 |α|/|β| -/
  by_contra h
  push_neg at h
  
  /- 若所有纤维大小 < |α|/|β|，则总元素数 < |α| -/
  sorry

/-
## 应用：生日问题

**问题**: 在一个房间中，至少需要多少人，才能使至少两人生日相同的概率 > 50%？

**答案**: 23人。

**鸽巢原理解释**: 365个可能的生日（盒子），n个人（物体）。
当 n > 365 时，必然有重复。
-/

-- 生日问题的确定性版本
theorem birthday_pigeonhole {n : ℕ} (hn : n > 365) (people : Fin n → Fin 365) :
    ∃ (i j : Fin n), i ≠ j ∧ people i = people j := by
  /- n > 365，由鸽巢原理，必有重复 -/
  apply Fintype.exists_ne_map_eq_of_card_lt people
  simp
  omega

/-
## 应用：Ramsey理论

**定理**: 在任何6个人的聚会上，必有3个人互相认识或互相不认识。

这是Ramsey数 R(3, 3) = 6 的表述。
-/

-- Ramsey数 R(3, 3) = 6 的图论表述
/-
定理：在6个顶点的完全图中，任意对边染红色或蓝色，
必存在单色三角形。
-/
theorem ramsey_3_3 {V : Type*} [Fintype V] (hV : card V = 6)
    (edge_color : V → V → Fin 2) (h_sym : ∀ (v w : V), edge_color v w = edge_color w v)
    (h_irrefl : ∀ (v : V), edge_color v v = 0) :
    ∃ (a b c : V), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (edge_color a b = edge_color b c ∧ edge_color b c = edge_color c a) := by
  /- 证明思路：
     1. 任取一顶点 v
     2. v 有5条边，由鸽巢原理，至少有3条同色（设为红色）
     3. 设这3条边连接到 a, b, c
     4. 若 ab, bc, ca 中有红色边，形成红色三角形
     5. 若 ab, bc, ca 全是蓝色，形成蓝色三角形
  -/
  sorry  -- 详细证明需要图论框架

/-
## 应用：数论

**定理**: 从 {1, 2, ..., 2n} 中选出 n+1 个数，必存在两数，其中一个整除另一个。

**证明**: 每个数可写成 2ᵏ·m（m 为奇数）。有 n 个可能的奇数部分，
由鸽巢原理，必有两个数有相同的奇数部分，所以一个整除另一个。
-/

-- 数论中的鸽巢原理应用
theorem pigeonhole_divisibility {n : ℕ} (hn : n > 0) 
    (s : Finset ℕ) (h_card : s.card = n + 1) 
    (h_subset : ∀ (x ∈ s), 1 ≤ x ∧ x ≤ 2 * n) :
    ∃ (x y : ℕ), x ∈ s ∧ y ∈ s ∧ x ≠ y ∧ x ∣ y := by
  /- 证明思路：
     1. 将每个数 x 写成 x = 2^k · m，其中 m 为奇数
     2. m ∈ {1, 3, 5, ..., 2n-1}，共 n 个可能的值
     3. 由鸽巢原理，必有两个数 x, y 有相同的奇数部分 m
     4. 设 x = 2^a · m, y = 2^b · m
     5. 若 a < b，则 x | y；若 b < a，则 y | x
  -/
  
  /- 定义映射：每个数映射到其奇数部分 -/
  let f : ℕ → ℕ := fun x => x / 2 ^ (Nat.factorization x 2)
  
  /- f(x) 总是奇数 -/
  have h_odd : ∀ (x ∈ s), Odd (f x) := by
    intro x hx
    dsimp [f]
    sorry  -- 需要证明除以最大2的幂次后为奇数
  
  /- f(x) ≤ 2n - 1 且为奇数 -/
  have h_range : ∀ (x ∈ s), f x ∈ Finset.Ioc 0 (2 * n).pred := by
    sorry
  
  /- 可能的奇数值有 n 个 -/
  have h_target_card : #{x | Odd x ∧ x ≤ 2 * n} = n := by
    sorry
  
  /- 由鸽巢原理，存在 x ≠ y 使得 f(x) = f(y) -/
  sorry

/-
## 推广：无穷鸽巢原理

**定理**: 若将无穷多个物体放入有限个盒子中，
则至少有一个盒子包含无穷多个物体。
-/

-- 无穷鸽巢原理
theorem infinite_pigeonhole {α β : Type*} [Infinite α] [Finite β]
    (f : α → β) :
    ∃ (y : β), Infinite {x | f x = y} := by
  /- 证明思路（反证法）：
     若每个纤维都有限，则 α 是有限个有限集的并，所以有限，矛盾
  -/
  by_contra h
  push_neg at h
  
  /- 每个纤维都是有限的 -/
  have h_finite : ∀ (y : β), Finite {x | f x = y} := by
    intro y
    specialize h y
    simpa using h
  
  /- α 是有限个有限集的并 -/
  have h_union : (⋃ (y : β), {x | f x = y}) = Set.univ := by
    ext x
    simp
  
  /- 有限个有限集的并是有限集 -/
  have h_finite_union : Finite (⋃ (y : β), {x | f x = y}) := by
    sorry
  
  /- 所以 α 是有限集，矛盾 -/
  rw [h_union] at h_finite_union
  have h_not_infinite : ¬Infinite α := by
    simpa using h_finite_union
  contradiction

end PigeonholePrinciple

/-
## 应用示例

### 示例1：简单鸽巢原理

```lean
-- 5个物体放入4个盒子，必有盒子包含至少2个物体
example (f : Fin 5 → Fin 4) : ∃ (x y : Fin 5), x ≠ y ∧ f x = f y := by
  apply pigeonhole_exists
  simp
```

### 示例2：一般形式

```lean
-- 10个物体放入3个盒子，必有盒子包含至少4个物体
-- ⌈10/3⌉ = 4
example (f : Fin 10 → Fin 3) : 
    ∃ (y : Fin 3), #{x | f x = y} ≥ 4 := by
  by_contra h
  push_neg at h
  /- 若每个盒子最多3个，则总数 ≤ 9，矛盾 -/
  have : ∑ y : Fin 3, #{x | f x = y} ≤ 9 := by
    sorry
  have : ∑ y : Fin 3, #{x | f x = y} = 10 := by
    sorry
  linarith
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
