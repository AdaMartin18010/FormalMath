---
title: "群论核心示例 自然语言与 Lean4 对照"
level: "silver"
target_courses:
  - "MIT 18.701"
---

## 定理陈述

**自然语言**：群论是研究代数结构“群”的学科。一个群 \((G, \cdot)\) 满足结合律、存在单位元、每个元素存在逆元。以下是 MIT 18.701 中的几个核心定理：

1. 逆元的逆元是自身：\((a^{-1})^{-1} = a\)。
2. Lagrange 定理：有限群的子群的阶整除群的阶。
3. 指数为 2 的子群必为正规子群。

**Lean4**：

```lean
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Sylow

namespace GroupTheoryExamples
open Group Subgroup

section InverseProperties
variable {G : Type*} [Group G]
-- 逆元的逆元是自身
example (a : G) : (a⁻¹)⁻¹ = a := by
  rw [inv_inv]

-- 乘积的逆元
example (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [mul_inv_rev]
end InverseProperties

section LagrangeTheorem
open Fintype
variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G)

-- Lagrange 定理：|H| 整除 |G|
example : card H ∣ card G := by
  exact ⟨H.index, by rw [Subgroup.index_mul_card]⟩

-- |G| = [G:H] · |H|
example : card G = H.index * card H := by
  rw [Subgroup.index_mul_card]
end LagrangeTheorem
```

## 证明思路

**自然语言**：Lagrange 定理的证明思路非常清晰：

1. 群 \(G\) 可以分解为子群 \(H\) 的互不相交的左陪集的并。
2. 每个左陪集的大小都等于 \(|H|\)（因为左乘一个固定元素是双射）。
3. 若左陪集个数为 \([G:H]\)，则 \(|G| = [G:H] \cdot |H|\)，故 \(|H|\) 整除 \(|G|\)。

**Lean4**：Mathlib4 的 `Subgroup.index_mul_card` 直接给出了分解等式。以下展示 Sylow 定理的存在性部分以及指数为 2 的子群是正规子群的结论：

```lean
section SylowTheorems
variable {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)

-- Sylow p-子群存在
example : Nonempty (Sylow p G) := by
  infer_instance

-- 指数为 2 的子群是正规子群
example (H : Subgroup G) (h : H.index = 2) : H.Normal := by
  have := Subgroup.normal_of_index_two H
  apply this
  exact h
end SylowTheorems
end GroupTheoryExamples
```

## 关键 tactic 教学

- `exact ⟨...⟩`：对存在量词目标提供构造性的见证。Lagrange 定理中 `⟨H.index, by rw [Subgroup.index_mul_card]⟩` 构造了整除关系所需的商。
- `infer_instance`：让 Lean 自动查找并应用类型类实例，如 `Nonempty (Sylow p G)`。
- `apply this`：当本地环境中已经有一个几乎匹配的定理时，用它来推进证明。

## 练习

1. 在 Lean4 中证明：对有限群 \(G\) 中的任意元素 \(a\)，有 \(a^{|G|} = 1\)。
2. 解释为什么指数为 2 的子群一定是正规子群（从陪集分解的角度）。
3. 写出并证明：若 \(|G| = p\) 为素数，则 \(G\) 是循环群。
