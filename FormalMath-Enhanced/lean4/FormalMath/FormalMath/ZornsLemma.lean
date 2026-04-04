/-
# Zorn引理 (Zorn's Lemma)

## 数学背景

Zorn引理是集合论中最重要、最常用的存在性原理之一。它与选择公理等价，
是现代代数学、泛函分析、拓扑学等领域中证明存在性定理的标准工具。

## 定理陈述

设 (P, ≤) 是一个偏序集。若P中的每个链（全序子集）在P中都有上界，
则P中存在极大元。

形式地：
∀ 偏序集 P, (∀ 链 C ⊆ P, ∃ 上界 ub ∈ P, ∀ x ∈ C, x ≤ ub) → ∃ 极大元 m ∈ P

## 历史背景

- 1922年：Kazimierz Kuratowski首次证明了该结果
- 1935年：Max Zorn独立发现并推广，由此得名
- 等价形式：选择公理、良序定理、Zorn引理三者等价

## 应用

1. 线性代数：任何向量空间都有基（Hamel基）
2. 域论：任何域都有代数闭包
3. 泛函分析：Hahn-Banach定理
4. 拓扑学：Tychonoff定理（吉洪诺夫定理）
5. 交换代数：任何真理想都包含于某个极大理想

## 参考
- Zorn, "A Remark on Method in Transfinite Algebra" (1935)
- Halmos, "Naive Set Theory"
- Kunen, "Set Theory"
- 张锦文,《公理集合论导引》

## Mathlib4对应
- `Mathlib.Order.Zorn`

Mathlib中已有Zorn引理的完整实现。
-/

import Mathlib.Order.Zorn
import Mathlib.Order.Chain
import Mathlib.Data.Set.Basic

namespace ZornsLemma

open Set Order Classical

universe u v

/-
## 基本定义

### 偏序集与链

偏序集（partially ordered set, poset）是配备了一个自反、反对称、
传递二元关系的集合。

链（chain）是偏序集的全序子集，即其中任意两个元素都可比较。
-/

/-- 链的定义：全序子集 -/
def IsChain' {α : Type*} [Preorder α] (C : Set α) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x

/-- 上界的定义 -/
def UpperBound {α : Type*} [Preorder α] (S : Set α) (ub : α) : Prop :=
  ∀ x ∈ S, x ≤ ub

/-- 极大元的定义 -/
def IsMaximal {α : Type*} [Preorder α] (m : α) : Prop :=
  ∀ x, m ≤ x → x = m

/-
## Zorn引理的陈述

这是Zorn引理的标准形式。
-/

/-- Zorn引理

设 (P, ≤) 是偏序集，若P中每个链都有上界，则P中存在极大元。
-/
theorem zorn_lemma {α : Type u} [PartialOrder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ x ∈ c, x ≤ ub) :
    ∃ m : α, IsMaximal m := by
  -- 证明：Mathlib中的zorn定理可以直接使用
  -- zorn定理返回一个极大元
  have h_max := zorn_lemma₀ (α := α) (fun x y h_le ↦ h_le)
  · -- 从zorn_lemma₀的结论构造极大元
    obtain ⟨m, hm⟩ := h_max
    exact ⟨m, fun x h_le ↦ by apply hm; exact h_le⟩
  · -- 证明条件满足：每个链有上界
    intro c hc_chain
    -- 利用假设条件
    obtain ⟨ub, hub⟩ := h c hc_chain
    exact ⟨ub, fun x hx _ h_le ↦ hub x hx⟩

/-
## 等价形式

### 与选择公理的等价性

Zorn引理与选择公理在ZF公理系统中互相等价。

选择公理（Axiom of Choice）：
对任何非空集合的集族，存在选择函数。
-/

/-- 选择公理的形式陈述 -/
axiom AxiomOfChoice : ∀ {α : Type u} {β : α → Type v},
  (∀ a, Nonempty (β a)) → Nonempty ((a : α) → β a)

/-
**定理**：选择公理 ⟹ Zorn引理

这是Zorn引理的证明中最困难的方向。
证明思路：
1. 利用选择公理构造一个"极大链"
2. 证明这个链的上界就是极大元

**证明概要**：
- 假设没有极大元
- 对每个链C，选择一个严格大于其上界的元素
- 利用选择公理，构造一个严格递增的序列
- 这与基数的性质矛盾（Hartogs定理）
-/

theorem AC_implies_Zorn (AC : ∀ {α : Type u} {β : α → Type v},
    (∀ a, Nonempty (β a)) → Nonempty ((a : α) → β a)) :
    ∀ {α : Type u} [PartialOrder α],
    (∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ x ∈ c, x ≤ ub) →
    ∃ m : α, IsMaximal m := by
  -- Zorn引理在Mathlib中已经证明
  -- 这里我们直接使用Mathlib的定理
  intros α _ h_chain_condition
  apply zorn_lemma
  exact h_chain_condition

/-
**定理**：Zorn引理 ⟹ 选择公理

这是相对容易的方向。
证明思路：
1. 构造适当的偏序集：部分选择函数的集合，按包含序排列
2. 证明任何链的并集仍是部分选择函数（有上界）
3. 应用Zorn引理得到极大元
4. 证明这个极大元就是全选择函数
-/

theorem Zorn_implies_AC (zorn : ∀ {α : Type u} [PartialOrder α],
    (∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ x ∈ c, x ≤ ub) →
    ∃ m : α, IsMaximal m) :
    ∀ {α : Type u} {β : α → Type v},
    (∀ a, Nonempty (β a)) → Nonempty ((a : α) → β a) := by
  intros α β h_nonempty
  -- 构造偏序集：部分选择函数的集合
  -- 定义为定义域为α的子集的选择函数
  let P := { f : Set ((a : α) × β a) |
    ∀ x : α, ∀ y₁ y₂ : β x, (⟨x, y₁⟩ : (a : α) × β a) ∈ f ∧ ⟨x, y₂⟩ ∈ f → y₁ = y₂ }
  -- 按包含关系排序
  have h_chain : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ ub : P, ∀ x ∈ c, x ≤ ub := by
    intros c hc_chain
    -- 链的并集是上界
    let ub := ⋃₀ c
    -- 验证ub是部分选择函数
    have hub : ub ∈ P := by
      simp [P] at *
      intro x y₁ y₂ hy₁ hy₂
      -- 找到包含y₁和y₂的函数
      obtain ⟨f₁, hf₁_mem, hf₁_in⟩ := hy₁
      obtain ⟨f₂, hf₂_mem, hf₂_in⟩ := hy₂
      -- 由于c是链，f₁和f₂可比较
      have h_comp : f₁ ≤ f₂ ∨ f₂ ≤ f₁ := by
        apply hc_chain f₁ hf₁_mem f₂ hf₂_mem
      cases h_comp with
      | inl h_le =>
        have hf₂_y₁ : (⟨x, y₁⟩ : (a : α) × β a) ∈ f₂ := h_le hf₁_in
        exact f₂.prop x y₁ y₂ ⟨hf₂_y₁, hf₂_in⟩
      | inr h_le =>
        have hf₁_y₂ : (⟨x, y₂⟩ : (a : α) × β a) ∈ f₁ := h_le hf₂_in
        exact f₁.prop x y₁ y₂ ⟨hf₁_in, hf₁_y₂⟩
    -- 返回上界
    exact ⟨⟨ub, hub⟩, fun f hf_mem x hx ↦ Set.mem_sUnion_of_mem hx hf_mem⟩
  -- 应用Zorn引理
  obtain ⟨m, hm_max⟩ := zorn (α := { f : Set ((a : α) × β a) |
    ∀ x : α, ∀ y₁ y₂ : β x, (⟨x, y₁⟩ : (a : α) × β a) ∈ f ∧ ⟨x, y₂⟩ ∈ f → y₁ = y₂ }) h_chain
  -- 证明m是完整的选择函数
  -- 即m的定义域是整个α
  have h_full : ∀ a : α, ∃ y : β a, (⟨a, y⟩ : (a : α) × β a) ∈ m.1 := by
    by_contra h_not_full
    push_neg at h_not_full
    obtain ⟨a₀, ha₀_none⟩ := h_not_full
    -- 利用非空性，选择某个y₀
    have h_y₀ : Nonempty (β a₀) := h_nonempty a₀
    cases h_y₀ with
    | intro y₀ =>
      -- 构造更大的部分选择函数
      let m' := m.1 ∪ {⟨a₀, y₀⟩}
      have hm'_in_P : m' ∈ P := by
        simp [P, m']
        intro x y₁ y₂ hy₁ hy₂
        rcases hy₁ with (h₁ | h₁) <;> rcases hy₂ with (h₂ | h₂)
        · -- 两者都在原m中
          exact m.prop x y₁ y₂ ⟨h₁, h₂⟩
        · -- y₁在m中，y₂是y₀
          exfalso
          have : x = a₀ := by
            simp at h₂
            exact h₂.1.symm
          rw [this] at h₁
          apply ha₀_none
          exact ⟨y₁, h₁⟩
        · -- y₂在m中，y₁是y₀
          exfalso
          have : x = a₀ := by
            simp at h₁
            exact h₁.1.symm
          rw [this] at h₂
          apply ha₀_none
          exact ⟨y₂, h₂⟩
        · -- 两者都是y₀
          simp at h₁ h₂
          rw [h₁.1.symm] at h₂
          exact h₂.2.symm
      -- m'严格包含m，与极大性矛盾
      have h_strict : m.1 ⊂ m' := by
        apply Set.ssubset_iff_subset_ne.mpr
        constructor
        · exact Set.subset_union_left
        · intro h_eq
          apply ha₀_none
          have : (⟨a₀, y₀⟩ : (a : α) × β a) ∈ m.1 := by
            rw [←h_eq]
            simp [m']
          exact ⟨y₀, this⟩
      have h_le : m ≤ ⟨m', hm'_in_P⟩ := by
        intro x hx
        simp [m']
        left
        exact hx
      have h_eq : m = ⟨m', hm'_in_P⟩ := hm_max ⟨m', hm'_in_P⟩ h_le
      have h_ne : m ≠ ⟨m', hm'_in_P⟩ := by
        apply Subtype.ext_iff.mp.mt
        exact Set.ssubset_iff_subset_ne.mp h_strict |>.2
      contradiction
  -- 构造完整的选择函数
  exact ⟨fun a ↦ Classical.choose (h_full a), fun a ↦ Classical.choose_spec (h_full a) |>.1⟩

/-
### 与良序定理的等价性

良序定理（Well-ordering Theorem）：
任何集合都可以被良序化，即存在一个全序使得每个非空子集都有最小元。
-/

/-- 良序定理 -/
theorem well_ordering_theorem (α : Type u) :
    ∃ r : α → α → Prop, IsWellOrder α r := by
  -- 利用选择公理构造良序
  -- 或者使用Mathlib中的现成定理
  apply nonempty_linearOrder_toWellOrderLTNondempty
  -- 这里使用Zorn引理证明
  -- 构造偏序集：部分良序的集合
  sorry -- 完整的证明较为复杂，需要超限递归

/-
## 典型应用

### 应用1：向量空间的基存在性

**定理**：任何向量空间都有基（Hamel基）。

证明思路：
1. 考虑线性无关集的集合，按包含序排列
2. 证明任何链的并集仍是线性无关的（有上界）
3. 应用Zorn引理得到极大线性无关集
4. 极大线性无关集就是基
-/

variable {V : Type*} [Field V] [AddCommGroup V] [Module V V]

/-- 线性无关集 -/
def LinearlyIndependentSet (S : Set V) : Prop :=
  ∀ (F : Finset S), ∑ v in F, v.1 • v.2 = 0 → ∀ v ∈ F, v.2 = 0

/-- 生成集 -/
def SpanningSet (S : Set V) : Prop :=
  ∀ v : V, v ∈ Submodule.span V S

/-- 基：极大线性无关集 -/
def Basis' (S : Set V) : Prop :=
  LinearlyIndependentSet S ∧ SpanningSet S

/-- 任何向量空间都有基 -/
theorem vector_space_has_basis :
    ∃ B : Set V, Basis' B := by
  -- 构造偏序集：线性无关集的集合
  let P := { S : Set V | LinearlyIndependentSet S }
  -- 证明任何链有上界
  have h_chain : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ ub : P, ∀ x ∈ c, x ≤ ub := by
    intros c hc_chain
    -- 链的并集是线性无关的
    let ub : Set V := ⋃₀ c
    have hub_in_P : ub ∈ P := by
      simp [P, ub, LinearlyIndependentSet]
      intro F hF_subset hF_sum
      -- 由于F有限，存在某个S ∈ c包含整个F
      sorry -- 需要有限集的紧致性论证
    exact ⟨⟨ub, hub_in_P⟩, fun S hS_mem x hx ↦ Set.mem_sUnion_of_mem hx hS_mem⟩
  -- 应用Zorn引理
  obtain ⟨B, hB_max⟩ := zorn_lemma (α := P) h_chain
  -- 证明B是基
  constructor
  · -- B线性无关
    exact B.2
  · -- B是生成集
    sorry -- 需要证明极大线性无关集必为生成集

/-
### 应用2：极大理想存在性

**定理**：任何真理想都包含于某个极大理想。

这在交换代数和环论中是基本结果。
-/

variable {R : Type*} [CommRing R]

/-- 极大理想 -/
def IsMaximalIdeal (I : Ideal R) : Prop :=
  I ≠ ⊤ ∧ ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤

/-- 真理想包含于极大理想 -/
theorem ideal_contained_in_maximal {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ M : Ideal R, IsMaximalIdeal M ∧ I ≤ M := by
  -- 构造偏序集：包含I的真理想的集合
  let P := { J : Ideal R | I ≤ J ∧ J ≠ ⊤ }
  have h_chain : ∀ c : Set P, IsChain (· ≤ ·) c → ∃ ub : P, ∀ x ∈ c, x ≤ ub := by
    intros c hc_chain
    -- 链的并集是理想
    let ub : Ideal R := {
      carrier := ⋃ J ∈ c, (J.1 : Set R)
      -- 需要验证理想结构
      sorry
    }
    sorry -- 验证ub ∈ P
  obtain ⟨M, hM_max⟩ := zorn_lemma (α := P) h_chain
  sorry -- 验证M是极大理想

/-
## 超限归纳法

Zorn引理是超限归纳法的变体。通过Zorn引理，可以证明涉及超限构造的定理。
-/

/-- 超限递归原理 -/
theorem transfinite_recursion {α : Type*} [WellFoundedLT α]
    {β : Type*} (f : (∀ a : α, β) → β) :
    ∃ g : α → β, ∀ a, g a = f (fun x _ ↦ g x) := by
  -- 利用良基归纳
  sorry

/-
## 总结

Zorn引理是现代数学中最强大、最通用的存在性原理之一。
它与选择公理和良序定理等价，构成了ZFC公理系统的核心部分。

主要应用：
1. 代数：基的存在性、代数闭包、极大理想
2. 泛函分析：Hahn-Banach定理、Riesz表示定理
3. 拓扑学：Tychonoff定理、紧性定理
-/

end ZornsLemma
