import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-! 
# 集合论示例

对应的FormalMath文档：
- docs/01-基础数学/集合论/01-集合论基础-深度扩展版.md
- docs/01-基础数学/集合论/03-函数与映射-深度扩展版.md
- docs/01-基础数学/集合论/04-关系与等价-深度扩展版.md
- docs/01-基础数学/集合论/05-基数与序数-深度扩展版.md

对应的Mathlib4模块：
- Mathlib.Data.Set.Basic
- Mathlib.Logic.Function.Basic
- Mathlib.SetTheory.Cardinal.Basic
- Mathlib.SetTheory.Ordinal.Basic

## 核心定义
-/ 

/-! 
## 集合的基本运算

集合论是数学的基础语言。
-/

section SetOperations
variable {α : Type*} (A B C : Set α)

-- 并集
#check A ∪ B

-- 交集
#check A ∩ B

-- 补集
#check Aᶜ

-- 差集
#check A \ B

-- 全集和空集
#check Set.univ : Set α
#check (∅ : Set α)

-- 包含关系
example : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

-- 德摩根定律
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp [Set.mem_compl_iff, Set.mem_union, Set.mem_inter]

example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp [Set.mem_compl_iff, Set.mem_union, Set.mem_inter]

-- 分配律
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp [Set.mem_inter, Set.mem_union]
  tauto

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp [Set.mem_inter, Set.mem_union]
  tauto

-- 幂集
example : Set (Set α) := Set.powerset A

end SetOperations

/-! 
## 函数与映射

函数是集合之间的特殊关系。
-/

section Functions
variable {α β γ : Type*}

-- 单射
example (f : α → β) : Prop := Function.Injective f

-- 满射
example (f : α → β) : Prop := Function.Surjective f

-- 双射
example (f : α → β) : Prop := Function.Bijective f

-- 单射的定义
example (f : α → β) : Function.Injective f ↔ 
    ∀ x y, f x = f y → x = y := by
  rfl

-- 满射的定义
example (f : α → β) : Function.Surjective f ↔ 
    ∀ y, ∃ x, f x = y := by
  rfl

-- 复合函数
example (f : α → β) (g : β → γ) : α → γ := g ∘ f

-- 单射的复合
example (f : α → β) (g : β → γ) (hf : Function.Injective f) 
    (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  apply Function.Injective.comp
  · exact hg
  · exact hf

-- 满射的复合
example (f : α → β) (g : β → γ) (hf : Function.Surjective f) 
    (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
  apply Function.Surjective.comp
  · exact hg
  · exact hf

-- 恒等映射
example : α → α := id

-- 逆函数
example (f : α → β) (hf : Function.Bijective f) : β → α := 
  Function.invFun f

end Functions

/-! 
## 等价关系与商集

等价关系划分集合为等价类。
-/

section EquivalenceRelations
variable {α : Type*} (r : α → α → Prop)

-- 等价关系类型
#check Equivalence r

-- 等价关系的性质
example : Equivalence r ↔ 
    (∀ x, r x x) ∧ (∀ x y, r x y → r y x) ∧ (∀ x y z, r x y → r y z → r x z) := by
  constructor
  · intro h
    exact ⟨h.refl, h.symm, h.trans⟩
  · rintro ⟨hrefl, hsymm, htrans⟩
    exact { refl := hrefl, symm := hsymm, trans := htrans }

-- 商集
example (r : Setoid α) : Type _ := Quotient r

-- 等价类
example (r : Setoid α) (a : α) : Set α := 
  {x | r.rel x a}

-- 商映射
example (r : Setoid α) : α → Quotient r := Quotient.mk r

-- 商映射的泛性质
example {α β : Type*} (r : Setoid α) (f : α → β) 
    (h : ∀ x y, r.rel x y → f x = f y) : Quotient r → β := 
  Quotient.lift f h

end EquivalenceRelations

/-! 
## 有限集与可数集

集合的基数分类。
-/

section Cardinality
variable {α : Type*}

-- 有限集
example : Prop := Finite α

-- 可数集
example : Prop := Countable α

-- 有限集的性质
example {α : Type*} [Finite α] (A : Set α) : Finite A := by
  infer_instance

-- 可数集的性质
example {α β : Type*} [Countable α] [Countable β] : Countable (α × β) := by
  infer_instance

example {α β : Type*} [Countable α] [Countable β] : Countable (α ⊕ β) := by
  infer_instance

-- ℕ是可数集
example : Countable ℕ := by
  infer_instance

-- ℚ是可数集
example : Countable ℚ := by
  infer_instance

-- ℝ是不可数集
example : ¬ Countable ℝ := by
  apply Cardinal.not_countable_real

end Cardinality

/-! 
## 基数

基数的算术。
-/

section Cardinals

-- 基数类型
example : Type _ := Cardinal

-- 集合的基数
example (α : Type*) : Cardinal := Cardinal.mk α

-- 基数的比较
example (α β : Type*) : Prop := Cardinal.mk α ≤ Cardinal.mk β

-- 基数的加法和乘法
example (a b : Cardinal) : Cardinal := a + b
example (a b : Cardinal) : Cardinal := a * b

-- 基数的幂
example (a b : Cardinal) : Cardinal := a ^ b

-- 重要基数
#check Cardinal.aleph0  -- ℵ₀
#check Cardinal.continuum  -- 𝔠 = 2^ℵ₀

-- ℵ₀是最小的无限基数
example : Cardinal.aleph0 = Cardinal.mk ℕ := by
  rfl

-- 连续统的基数
example : Cardinal.continuum = Cardinal.mk ℝ := by
  rw [Cardinal.continuum]
  simp

-- Cantor定理：对于任意集合A，|A| < |P(A)|
example (α : Type*) : Cardinal.mk α < Cardinal.mk (Set α) := by
  apply Cardinal.mk_lt_mk_powerset

-- 2^ℵ₀ = 𝔠
example : (2 : Cardinal) ^ Cardinal.aleph0 = Cardinal.continuum := by
  rw [Cardinal.continuum]

end Cardinals

/-! 
## 序数

良序集的序型。
-/

section Ordinals

-- 序数类型
example : Type _ := Ordinal

-- 自然数作为序数
example : Ordinal := (0 : Ordinal)
example : Ordinal := (1 : Ordinal)
example : Ordinal := (2 : Ordinal)

-- 第一个无限序数 ω
example : Ordinal := ω

-- 序数的加法和乘法
example (α β : Ordinal) : Ordinal := α + β
example (α β : Ordinal) : Ordinal := α * β

-- 序数运算不满足交换律
example : (1 : Ordinal) + ω = ω := by
  simp

example : ω + (1 : Ordinal) ≠ ω := by
  intro h
  have h1 : ω < ω + 1 := by
    apply Ordinal.lt_add_right
    exact Ordinal.one_ne_zero
  rw [h] at h1
  exact (lt_irrefl ω h1).elim

-- 极限序数
example : Prop := Ordinal.IsLimit ω

-- ω是极限序数
example : Ordinal.IsLimit ω := by
  apply Ordinal.omega_isLimit

end Ordinals

/-! 
## Zorn引理

集合论中的重要选择原理。
-/

section ZornsLemma
variable {α : Type*} [Preorder α]

-- 链（全序子集）
example (C : Set α) : Prop := IsChain (· ≤ ·) C

-- 上界
example (C : Set α) (u : α) : Prop := ∀ c ∈ C, c ≤ u

-- Zorn引理
example (h : ∀ C, IsChain (· ≤ ·) C → ∃ u, ∀ c ∈ C, c ≤ u) : 
    ∃ m, ∀ x, m ≤ x → x ≤ m := by
  apply zorn_le
  intro c hc
  exact h c hc

end ZornsLemma

/-! 
## 示例：Cantor对角线论证

著名的不可数性证明。
-/

section CantorDiagonalArgument

-- 定理：不存在从ℕ到(ℕ → Bool)的满射
theorem not_surjective_nat_to_bool_sequence : 
    ¬ ∃ f : ℕ → (ℕ → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  -- 构造对角线反例
  let g : ℕ → Bool := fun n => !(f n n)
  -- 证明g不在f的值域中
  have h : ∀ n, f n ≠ g := by
    intro n h_eq
    have h1 := congr_fun h_eq n
    simp [g] at h1
    contradiction
  -- 与满射性矛盾
  have h2 : ∃ n, f n = g := hf g
  obtain ⟨n, hn⟩ := h2
  exact h n hn

-- 推论：|ℕ| < |P(ℕ)|
example : Cardinal.mk ℕ < Cardinal.mk (Set ℕ) := by
  apply Cardinal.mk_lt_mk_powerset

end CantorDiagonalArgument

/-! 
## 练习

1. 证明：如果f: A → B是单射，且g: B → C是单射，那么g∘f是单射。

2. 证明：对于任意集合A,B,C，有 A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)。

3. 证明：如果R是等价关系，那么等价类构成集合的一个划分。

4. 证明：有限个可数集的并集是可数的。

5. 证明：对于任意基数κ，有 κ < 2^κ（Cantor定理）。

-/ 

section Exercises
variable {α β γ : Type*}

-- 练习2的提示
example (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp [Set.mem_inter, Set.mem_union]
  tauto

-- 练习5的提示（已在上文Cantor定理中证明）
example (α : Type*) : Cardinal.mk α < Cardinal.mk (Set α) := by
  apply Cardinal.mk_lt_mk_powerset

end Exercises
