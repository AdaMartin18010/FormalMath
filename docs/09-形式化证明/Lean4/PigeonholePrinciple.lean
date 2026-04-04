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
import Mathlib.Data.Nat.ModEq

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
theorem pigeonhole_general {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (f : α → β) (k : ℕ) (h : card α > k * card β) :
    ∃ (y : β), #{x | f x = y} > k := by
  /- 使用Mathlib4的鸽巢原理 -/
  have h' : ∃ (y : β), #{x | f x = y} > k := by
    apply Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := Finset.univ) (t := Finset.univ)
    · intro x _
      exact Finset.mem_univ (f x)
    · simpa using h
  exact h'

-- 鸽巢原理的平均形式
theorem pigeonhole_average {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] [DecidableEq α]
    (f : α → β) :
    ∃ (y : β), #{x | f x = y} * card β ≥ card α := by
  /- 使用Mathlib4的鸽巢原理 -/
  have h : ∃ (y : β), #{x | f x = y} * card β ≥ card α := by
    apply Finset.exists_card_fiber_ge_of_nsmul_le_card_of_maps_to (s := Finset.univ) (t := Finset.univ)
    · intro x _
      exact Finset.mem_univ (f x)
    · simp
  exact h

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
  have h_nonempty : Nonempty V := by
    have : card V > 0 := by rw [hV]; norm_num
    exact Fintype.card_pos_iff.mp this
  
  rcases h_nonempty with ⟨v⟩
  
  /- 考虑从v到其他顶点的边的颜色 -/
  let other_vertices : Finset V := Finset.univ.erase v
  have h_card_other : other_vertices.card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    simp [hV]
  
  /- 按颜色分类 -/
  let red_neighbors : Finset V := Finset.filter (fun w => edge_color v w = 1) other_vertices
  let blue_neighbors : Finset V := Finset.filter (fun w => edge_color v w = 0) other_vertices
  
  have h_partition : other_vertices.card = red_neighbors.card + blue_neighbors.card := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
  
  rw [h_card_other] at h_partition
  
  /- 至少一种颜色有3个或更多邻居 -/
  have h_large_color : red_neighbors.card ≥ 3 ∨ blue_neighbors.card ≥ 3 := by
    by_contra h
    push_neg at h
    have h1 : red_neighbors.card ≤ 2 := by linarith
    have h2 : blue_neighbors.card ≤ 2 := by linarith
    have : red_neighbors.card + blue_neighbors.card ≤ 4 := by linarith
    linarith
  
  cases h_large_color with
  | inl h_red =>
    /- 至少有3个红色邻居，应用Ramsey论证 -/
    have h_card : red_neighbors.card ≥ 3 := h_red
    have h3 : ∃ (a b c : V), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ red_neighbors ∧ b ∈ red_neighbors ∧ c ∈ red_neighbors := by
      have h_pos : red_neighbors.card ≥ 3 := h_card
      rcases Finset.three_le h_pos with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩
    
    rcases h3 with ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩
    
    /- 检查 a, b, c 之间的边 -/
    by_cases h_ab : edge_color a b = 1
    · by_cases h_bc : edge_color b c = 1
      · /- 红色三角形 a-b-c -/
        use a, b, c, hab, hac, hbc
        constructor
        · exact h_ab
        · exact h_bc.symm.trans (h_sym b c)
      · /- bc 是蓝色 -/
        have h_bc_blue : edge_color b c = 0 := by
          have : edge_color b c = 0 ∨ edge_color b c = 1 := by
            fin_cases edge_color b c <;> simp
          tauto
        by_cases h_ac : edge_color a c = 1
        · /- 红色三角形 a-c-v -/
          use a, c, v, hac, by_contra hcv; rw [←hcv] at hac; contradiction, by_contra hva; rw [←hva] at hac; contradiction
          constructor
          · exact h_ac
          · have : edge_color c v = 1 := by
              simp [red_neighbors] at hc
              exact hc.2
            rw [h_sym c v]
            exact this
        · /- ac 是蓝色，蓝色三角形 a-b-c -/
          use a, b, c, hab, hac, hbc
          constructor
          · have : edge_color a b = 0 := by
              have : edge_color a b = 0 ∨ edge_color a b = 1 := by
                fin_cases edge_color a b <;> simp
              tauto
            linarith
          · exact h_bc_blue
    · /- ab 是蓝色 -/
      have h_ab_blue : edge_color a b = 0 := by
        have : edge_color a b = 0 ∨ edge_color a b = 1 := by
          fin_cases edge_color a b <;> simp
        tauto
      by_cases h_bc : edge_color b c = 1
      · by_cases h_ac : edge_color a c = 1
        · /- 红色三角形 a-c-v -/
          use a, c, v, hac, by_contra hcv; rw [←hcv] at hac; contradiction, by_contra hva; rw [←hva] at hac; contradiction
          constructor
          · exact h_ac
          · have : edge_color c v = 1 := by
              simp [red_neighbors] at hc
              exact hc.2
            rw [h_sym c v]
            exact this
        · /- ac 是蓝色，蓝色三角形 a-b-c -/
          use a, b, c, hab, hac, hbc
          constructor
          · exact h_ab_blue
          · exact h_bc
      · /- bc 是蓝色，蓝色三角形 a-b-c -/
        use a, b, c, hab, hac, hbc
        constructor
        · exact h_ab_blue
        · exact h_bc
  | inr h_blue =>
    /- 至少有3个蓝色邻居，类似论证 -/
    have h_card : blue_neighbors.card ≥ 3 := h_blue
    have h3 : ∃ (a b c : V), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ blue_neighbors ∧ b ∈ blue_neighbors ∧ c ∈ blue_neighbors := by
      have h_pos : blue_neighbors.card ≥ 3 := h_card
      rcases Finset.three_le h_pos with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩
    
    rcases h3 with ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩
    
    /- 检查 a, b, c 之间的边 -/
    by_cases h_ab : edge_color a b = 0
    · by_cases h_bc : edge_color b c = 0
      · /- 蓝色三角形 a-b-c -/
        use a, b, c, hab, hac, hbc
        constructor
        · exact h_ab
        · exact h_bc.symm.trans (h_sym b c)
      · /- bc 是红色 -/
        have h_bc_red : edge_color b c = 1 := by
          have : edge_color b c = 0 ∨ edge_color b c = 1 := by
            fin_cases edge_color b c <;> simp
          tauto
        by_cases h_ac : edge_color a c = 0
        · /- 蓝色三角形 a-c-v -/
          use a, c, v, hac, by_contra hcv; rw [←hcv] at hac; contradiction, by_contra hva; rw [←hva] at hac; contradiction
          constructor
          · exact h_ac
          · have : edge_color c v = 0 := by
              simp [blue_neighbors] at hc
              exact hc.2
            rw [h_sym c v]
            exact this
        · /- ac 是红色，红色三角形 a-b-c -/
          use a, b, c, hab, hac, hbc
          constructor
          · have : edge_color a b = 1 := by
              have : edge_color a b = 0 ∨ edge_color a b = 1 := by
                fin_cases edge_color a b <;> simp
              tauto
            linarith
          · exact h_bc_red
    · /- ab 是红色 -/
      have h_ab_red : edge_color a b = 1 := by
        have : edge_color a b = 0 ∨ edge_color a b = 1 := by
          fin_cases edge_color a b <;> simp
        tauto
      by_cases h_bc : edge_color b c = 0
      · by_cases h_ac : edge_color a c = 0
        · /- 蓝色三角形 a-c-v -/
          use a, c, v, hac, by_contra hcv; rw [←hcv] at hac; contradiction, by_contra hva; rw [←hva] at hac; contradiction
          constructor
          · exact h_ac
          · have : edge_color c v = 0 := by
              simp [blue_neighbors] at hc
              exact hc.2
            rw [h_sym c v]
            exact this
        · /- ac 是红色，红色三角形 a-b-c -/
          use a, b, c, hab, hac, hbc
          constructor
          · exact h_ab_red
          · exact h_bc
      · /- bc 是红色，红色三角形 a-b-c -/
        use a, b, c, hab, hac, hbc
        constructor
        · exact h_ab_red
        · have : edge_color b c = 1 := by
            have : edge_color b c = 0 ∨ edge_color b c = 1 := by
              fin_cases edge_color b c <;> simp
            tauto
          linarith

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
  let oddPart (x : ℕ) : ℕ := x / 2 ^ (Nat.factorization x 2)
  
  /- 奇数部分的范围 -/
  have h_odd_range : ∀ x ∈ s, oddPart x ∈ Finset.Ioc 0 (2 * n) := by
    intro x hx
    simp [oddPart]
    have h1 : 1 ≤ x := (h_subset x hx).1
    have h2 : x ≤ 2 * n := (h_subset x hx).2
    have h_odd : Odd (x / 2 ^ (Nat.factorization x 2)) := by
      apply Nat.div_pow_factorization_is_pos_and_odd
      · linarith
      · linarith
    rcases h_odd with ⟨k, hk⟩
    constructor
    · linarith [hk]
    · have : x / 2 ^ (Nat.factorization x 2) ≤ x := by
        apply Nat.div_le_self
      linarith
  
  /- 奇数部分的集合的基数最多为 n -/
  have h_target_card : #(Finset.image oddPart s) ≤ n := by
    have h_subset : Finset.image oddPart s ⊆ Finset.filter Odd (Finset.Ioc 0 (2 * n)) := by
      intro m hm
      simp at hm ⊢
      rcases hm with ⟨x, hx, rfl⟩
      have h1 : 1 ≤ x := (h_subset x hx).1
      have h2 : x ≤ 2 * n := (h_subset x hx).2
      have h_odd : Odd (oddPart x) := by
        apply Nat.div_pow_factorization_is_pos_and_odd
        · linarith
        · linarith
      have h_pos : oddPart x > 0 := by
        apply Nat.div_pos
        · apply pow_pos
          linarith
        · linarith
      simp [h_pos, h_odd]
    have h_card_target : #(Finset.filter Odd (Finset.Ioc 0 (2 * n))) = n := by
      /- {1, 3, ..., 2n-1} 中有 n 个奇数 -/
      rw [Finset.filter_card_add_filter_neg_card_eq_card (p := Odd) (s := Finset.Ioc 0 (2 * n))]
      have h_even : #(Finset.filter (fun x => ¬Odd x) (Finset.Ioc 0 (2 * n))) = n := by
        /- {2, 4, ..., 2n} 中有 n 个偶数 -/
        rw [Finset.card_Ioc]
        simp [show 2 * n - 0 = 2 * n by simp]
        /- 在 {1, ..., 2n} 中，奇数和偶数各 n 个 -/
        omega
      rw [h_even]
      have h_total : #(Finset.Ioc 0 (2 * n)) = 2 * n := by
        rw [Finset.card_Ioc]
        simp
      omega
    exact Nat.le_trans (Finset.card_le_card h_subset) (by linarith)
  
  /- 由鸽巢原理，存在 x ≠ y 使得 oddPart(x) = oddPart(y) -/
  have h_pigeonhole : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ oddPart x = oddPart y := by
    by_contra h
    push_neg at h
    have h_inj : Set.InjOn oddPart s.toSet := by
      intro x hx y hy h_eq
      by_cases hxy : x = y
      · exact hxy
      · exfalso
        exact h x hx y hy hxy h_eq
    have h_card_eq : #(Finset.image oddPart s) = s.card := by
      rw [Finset.card_image_iff.mpr h_inj]
    rw [h_card_eq] at h_target_card
    rw [h_card] at h_target_card
    omega
  
  rcases h_pigeonhole with ⟨x, hx, y, hy, hxy, h_eq⟩
  
  /- 设 x = 2^a · m, y = 2^b · m，其中 m = oddPart(x) = oddPart(y) -/
  let a := Nat.factorization x 2
  let b := Nat.factorization y 2
  let m := oddPart x
  
  have hx_eq : x = 2 ^ a * m := by
    rw [Nat.div_mul_cancel]
    apply Nat.ord_proj_dvd
  
  have hy_eq : y = 2 ^ b * m := by
    have : oddPart y = m := by
      rw [h_eq]
    rw [Nat.div_mul_cancel]
    apply Nat.ord_proj_dvd
  
  /- 比较 a 和 b -/
  by_cases hab : a ≤ b
  · use x, y, hx, hy, hxy
    rw [hx_eq, hy_eq]
    use 2 ^ (b - a)
    rw [pow_mul]
    congr
    omega
  · use y, x, hy, hx, hxy.symm
    rw [hx_eq, hy_eq]
    use 2 ^ (a - b)
    rw [pow_mul]
    ring_nf
    congr
    omega

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
    apply Finite.Set.finite_iUnion
    · exact Fintype.ofFinite β
    · intro y
      exact h_finite y
  
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
