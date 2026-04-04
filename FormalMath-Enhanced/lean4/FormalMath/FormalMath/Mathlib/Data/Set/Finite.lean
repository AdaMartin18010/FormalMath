/-
# Data.Set.Finite - Stub

有限集合
-/

import FormalMath.Mathlib

namespace Set

/-- A set is finite if it is equivalent to a finset. -/
def Finite {α : Type*} (s : Set α) : Prop :=
  ∃ (t : Finset α), s = t.toSet

/-- A set is infinite if it is not finite. -/
def Infinite {α : Type*} (s : Set α) : Prop :=
  ¬Finite s

/-- The set of all elements. -/
def univ {α : Type*} : Set α :=
  {a | True}

end Set

namespace Finite

namespace Set

/-- A finite union of finite sets is finite. -/
theorem finite_iUnion {α ι : Type*} [Fintype ι] {f : ι → Set α}
    (h : ∀ i, Finite (f i)) : Finite (⋃ i, f i) :=
  sorry

end Set

end Finite
