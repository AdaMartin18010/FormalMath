/-
# Data.Fintype.Card - Stub

有限类型的基数
-/

import FormalMath.Mathlib.Data.Fintype.Basic
import FormalMath.Mathlib.Data.Finset.Basic

namespace Fintype

/-- The cardinality of a finite type. -/
def card (α : Type*) [Fintype α] : ℕ :=
  sorry

/-- There exist two distinct elements that map to the same value when the domain is larger than the codomain. -/
theorem exists_ne_map_eq_of_card_lt {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (h : card α < card β) : ∃ x y : α, x ≠ y ∧ f x = f y :=
  sorry

/-- Cardinality is preserved under injective maps. -/
theorem card_le_card_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (h : Function.Injective f) : card α ≤ card β :=
  sorry

end Fintype
