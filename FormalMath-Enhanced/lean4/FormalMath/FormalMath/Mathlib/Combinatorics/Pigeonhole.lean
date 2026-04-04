/-
# Combinatorics.Pigeonhole - Stub

鸽巢原理
-/

import FormalMath.Mathlib.Data.Fintype.Card
import FormalMath.Mathlib.Data.Finset.Basic

namespace Finset

/-- Pigeonhole principle: if more elements than buckets, some bucket has multiple elements. -/
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to {α β : Type*} [DecidableEq α]
    {s : Finset α} {t : Finset β} {f : α → β} {n : ℕ}
    (hf : ∀ a ∈ s, f a ∈ t) (h : n * t.card < s.card) :
    ∃ b ∈ t, n < {a ∈ s | f a = b}.card :=
  sorry

/-- General pigeonhole principle variant. -/
theorem exists_lt_card_fiber_of_maps_to_of_lt_card {α β : Type*} [DecidableEq α]
    {s : Finset α} {t : Finset β} {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) (h : t.card < s.card) :
    ∃ b ∈ t, 1 < {a ∈ s | f a = b}.card :=
  sorry

/-- Average form of pigeonhole principle. -/
theorem exists_card_fiber_ge_of_nsmul_le_card_of_maps_to {α β : Type*} [DecidableEq α]
    {s : Finset α} {t : Finset β} {f : α → β} [Nonempty β]
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∃ b ∈ t, s.card ≤ {a ∈ s | f a = b}.card * t.card :=
  sorry

end Finset
