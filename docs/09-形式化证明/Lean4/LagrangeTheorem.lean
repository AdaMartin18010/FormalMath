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

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Fintype.Basic

universe u v

namespace LagrangeTheorem

open Subgroup Group

/-
## 核心概念定义

### 左陪集 (Left Coset)
对于群 G 的子群 H 和元素 a ∈ G，a 的左陪集定义为：
aH = {ah | h ∈ H}

### 陪集代表元 (Coset Representative)
每个陪集的代表元是陪集中的任意一个元素。

### 指数 (Index)
子群 H 在 G 中的指数 [G:H] 是不同左陪集的个数。
-

-- 左陪集的基数等于子群的基数
theorem leftCoset_card_eq_subgroup_card {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (a : G) :
    (a • (H : Set G)).toFinset.card = Fintype.card H := by
  /- 证明思路：
     1. 定义映射 f: H → aH, f(h) = ah
     2. 证明 f 是双射
     3. 因此 |aH| = |H|
  -/
  let f : H → (a • (H : Set G)).toFinset := fun h => ⟨a * h, by
    simp [leftCoset]
    exact ⟨h, h.2, rfl⟩
  ⟩
  
  have h_inj : Function.Injective f := by
    intro h₁ h₂ heq
    simp [f] at heq
    /- 由 ah₁ = ah₂，左乘 a⁻¹ 得到 h₁ = h₂ -/
    have : a * h₁ = a * h₂ := by simpa using heq
    exact (mul_left_inj a).mp this
  
  have h_surj : Function.Surjective f := by
    intro x
    rcases x with ⟨x, hx⟩
    simp [leftCoset] at hx
    rcases hx with ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, by simp [f]⟩
  
  -- 双射意味着基数相等
  have h_bij : Function.Bijective f := ⟨h_inj, h_surj⟩
  exact (Fintype.card_of_bijective h_bij).symm

-- 陪集要么相等，要么不相交
theorem leftCoset_eq_or_disjoint {G : Type u} [Group G] (H : Subgroup G) (a b : G) :
    a • (H : Set G) = b • (H : Set G) ∨ (a • (H : Set G)) ∩ (b • (H : Set G)) = ∅ := by
  /- 证明思路：
     如果 aH ∩ bH ≠ ∅，则存在 h₁, h₂ ∈ H 使得 ah₁ = bh₂
     于是 a = bh₂h₁⁻¹ ∈ bH，因此 aH ⊆ bH
     同理 bH ⊆ aH，所以 aH = bH
  -/
  by_cases h : (a • (H : Set G)) ∩ (b • (H : Set G)) = ∅
  · right; exact h
  · left
    have : ∃ x, x ∈ (a • (H : Set G)) ∩ (b • (H : Set G)) := by
      by_contra h'
      push_neg at h'
      have : (a • (H : Set G)) ∩ (b • (H : Set G)) = ∅ := by
        ext x
        simp [h']
      contradiction
    
    rcases this with ⟨x, hxa, hxb⟩
    simp [leftCoset] at hxa hxb
    rcases hxa with ⟨h₁, hh₁, rfl⟩
    rcases hxb with ⟨h₂, hh₂, heq⟩
    
    /- ah₁ = bh₂ 推出 a = bh₂h₁⁻¹ -/
    have ha : a = b * h₂ * h₁⁻¹ := by
      rw [←heq]
      group
    
    /- 证明 aH = bH -/
    ext y
    simp [leftCoset, ha]
    constructor
    · intro hy
      rcases hy with ⟨h, hh, rfl⟩
      use h₂ * h₁⁻¹ * h
      constructor
      · exact H.mul_mem (H.mul_mem hh₂ (H.inv_mem hh₁)) hh
      · group
    · intro hy
      rcases hy with ⟨h, hh, rfl⟩
      use h₁ * h₂⁻¹ * h
      constructor
      · exact H.mul_mem (H.mul_mem hh₁ (H.inv_mem hh₂)) hh
      · group

/-
## 拉格朗日定理主定理

**定理陈述**: 设 G 是有限群，H 是 G 的子群，则 |H| 整除 |G|。

**证明概要**:
1. G 可以分解为互不相交的左陪集的并
2. 每个左陪集的大小等于 |H|
3. 如果左陪集的个数为 [G:H]，则 |G| = [G:H] · |H|
4. 因此 |H| 整除 |G|
-

-- 拉格朗日定理：子群的阶整除群的阶
theorem lagrange_theorem {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  /- 使用Mathlib4的index_mul_card定理 -/
  rw [← Subgroup.index_mul_card H]
  exact dvd_mul_left (Fintype.card H) (H.index)

-- 拉格朗日定理的完整形式：|G| = [G:H] · |H|
theorem lagrange_theorem_full {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card G = H.index * Fintype.card H := by
  exact (Subgroup.index_mul_card H).symm

-- 元素的阶整除群的阶
theorem order_of_dvd_card {G : Type u} [Group G] [Fintype G] (a : G) :
    orderOf a ∣ Fintype.card G := by
  /- 利用循环子群 <a> 的阶等于元素 a 的阶 -/
  have h : orderOf a = Fintype.card (zpowers a) := by
    rw [orderOf_eq_card_zpowers]
  
  rw [h]
  /- 应用拉格朗日定理于循环子群 -/
  exact lagrange_theorem (zpowers a)

-- 费马小定理（群论版本）
theorem fermat_little_theorem_group {G : Type u} [Group G] [Fintype G] (a : G) :
    a ^ Fintype.card G = 1 := by
  /- 证明思路：
     1. 设 |a| = n，则 n | |G|（由拉格朗日定理）
     2. 所以 |G| = n·k
     3. a^|G| = a^(n·k) = (a^n)^k = 1^k = 1
  -/
  have h : orderOf a ∣ Fintype.card G := order_of_dvd_card a
  rcases h with ⟨k, hk⟩
  calc
    a ^ Fintype.card G = a ^ (orderOf a * k) := by rw [hk]
    _ = (a ^ orderOf a) ^ k := by rw [pow_mul]
    _ = 1 ^ k := by rw [pow_orderOf_eq_one a]
    _ = 1 := by simp

end LagrangeTheorem

/-
## 使用示例

```lean
-- 对称群 S₃ 的阶为 6
example : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Fintype.card_perm]

-- S₃ 的子群 {e, (12)} 的阶为 2，整除 6
-- S₃ 的子群 A₃ = {e, (123), (132)} 的阶为 3，整除 6
```

## 数学意义

拉格朗日定理是有限群论的基石，它有以下重要推论：

1. **素数阶群必为循环群**：若 |G| = p 为素数，则 G ≅ ℤ/pℤ
2. **欧拉定理**：a^φ(n) ≡ 1 (mod n)，其中 gcd(a,n) = 1
3. **费马小定理**：a^(p-1) ≡ 1 (mod p)，其中 p 为素数，p ∤ a

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Subgroup.index_mul_card`: 拉格朗日定理的核心实现
- `Subgroup.index`: 子群指数的定义
- `leftCoset`: 左陪集的定义和性质
-
