/-
# Data.Finset.Basic - Stub

有限集合基础
-/

import FormalMath.Mathlib

/-- A finite set. -/
structure Finset (α : Type*) where
  val : List α
  nodup : val.Nodup

namespace Finset

/-- The cardinality of a finite set. -/
def card {α : Type*} (s : Finset α) : ℕ :=
  s.val.length

/-- The universal finite set. -/
def univ {α : Type*} [Fintype α] : Finset α :=
  sorry

/-- Membership in a finite set. -/
instance : Membership α (Finset α) where
  mem s a := a ∈ s.val

/-- Check if an element is in the universal set. -/
theorem mem_univ {α : Type*} [Fintype α] (a : α) : a ∈ @univ α _ :=
  sorry

/-- The image of a finset under a function. -/
def image {α β : Type*} (f : α → β) (s : Finset α) : Finset β :=
  sorry

/-- Filter a finset by a predicate. -/
def filter {α : Type*} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset α :=
  sorry

/-- The set of elements satisfying a predicate has cardinality related to the original set. -/
theorem filter_card_add_filter_neg_card_eq_card {α : Type*} (p : α → Prop) [DecidablePred p]
    (s : Finset α) : card (filter p s) + card (filter (fun a => ¬p a) s) = card s :=
  sorry

/-- The half-open interval [a, b). -/
def Ioc {α : Type*} [Preorder α] (a b : α) : Finset α :=
  sorry

/-- The closed interval [0, n]. -/
def Iic {α : Type*} [Preorder α] [LocallyFiniteOrder α] (n : α) : Finset α :=
  sorry

/-- Cardinality of Ioc. -/
theorem card_Ioc {α : Type*} [Preorder α] [LocallyFiniteOrder α] (a b : α) :
    card (Ioc a b) = Nat.ofNat (Set.encard (Set.Ioc a b)) :=
  sorry

/-- Erase an element from a finset. -/
def erase {α : Type*} [DecidableEq α] (s : Finset α) (a : α) : Finset α :=
  sorry

/-- Cardinality after erasing an element. -/
theorem card_erase_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (h : a ∈ s) : card (erase s a) = card s - 1 :=
  sorry

/-- If three elements are in a finset with cardinality ≥ 3, they are distinct. -/
theorem three_le {α : Type*} {s : Finset α} (h : s.card ≥ 3) :
    ∃ a b c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  sorry

/-- The product of a finset. -/
def prod {α β : Type*} [CommMonoid β] (s : Finset α) (f : α → β) : β :=
  sorry

/-- dvd property for finset product. -/
theorem dvd_prod_of_mem {α β : Type*} [CommMonoid β] {s : Finset α} {a : α} (ha : a ∈ s)
    (f : α → β) : f a ∣ prod s f :=
  sorry

/-- Set difference for finsets. -/
instance : SDiff (Finset α) where
  sdiff s t := filter (fun a => a ∉ t) s

/-- The underlying set of a finset. -/
def toSet {α : Type*} (s : Finset α) : Set α :=
  {a | a ∈ s}

/-- Image of a finset under a function (as a set operation). -/
def image' {α β : Type*} (f : α → β) (s : Finset α) : Finset β :=
  image f s

/-- Cardinality of image under injective function. -/
theorem card_image_iff {α β : Type*} {f : α → β} {s : Finset α} :
    Set.InjOn f s.toSet ↔ card (image f s) = card s :=
  sorry

/-- Cardinality comparison for subsets. -/
theorem card_le_card {α : Type*} {s t : Finset α} (h : s ⊆ t) : card s ≤ card t :=
  sorry

end Finset

/-- Locally finite order typeclass. -/
class LocallyFiniteOrder (α : Type*) [Preorder α] where
  /-- The finset of elements in the closed interval [a, b]. -/
  finsetIcc : α → α → Finset α
  /-- The finset of elements in the half-open interval [a, b). -/
  finsetIco : α → α → Finset α
  /-- The finset of elements in the half-open interval (a, b]. -/
  finsetIoc : α → α → Finset α
  /-- The finset of elements in the open interval (a, b). -/
  finsetIoo : α → α → Finset α
