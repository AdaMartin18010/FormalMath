/-
# SetTheory.Cardinal.Basic - Stub

基数理论
-/

import FormalMath.Mathlib

universe u v

/-- The cardinal number of a type. -/
def Cardinal.mk (α : Type u) : Cardinal :=
  sorry

/-- Notation for cardinal.mk -/
notation "#" α => Cardinal.mk α

/-- `Cardinal` is the type of cardinal numbers. -/
def Cardinal : Type (u + 1) :=
  sorry

namespace Cardinal

/-- The cardinal power operation. -/
def power (a b : Cardinal) : Cardinal :=
  sorry

/-- Notation for cardinal power. -/
instance : Pow Cardinal Cardinal where
  pow := power

/-- The sum of a family of cardinals. -/
def sum {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  sorry

/-- The product of a family of cardinals. -/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  sorry

/-- Cantor's theorem: for every cardinal `κ`, `κ < 2^κ`. -/
theorem cantor (κ : Cardinal) : κ < 2 ^ κ :=
  sorry

/-- König's theorem: the sum of cardinals is less than the product of larger cardinals. -/
theorem sum_lt_prod {ι : Type u} (κ λ : ι → Cardinal) (h : ∀ i, κ i < λ i) : sum κ < prod λ :=
  sorry

/-- Addition of infinite cardinals: `κ + λ = max κ λ` when `ℵ₀ ≤ κ` and `λ ≤ κ`. -/
theorem add_eq_max {κ λ : Cardinal} (h : ℵ₀ ≤ κ) : κ + λ = max κ λ :=
  sorry

/-- Multiplication of infinite cardinals: `κ * λ = max κ λ` when `ℵ₀ ≤ κ` and `0 < λ`. -/
theorem mul_eq_max {κ λ : Cardinal} (h₁ : ℵ₀ ≤ κ) (h₂ : 0 < λ) : κ * λ = max κ λ :=
  sorry

/-- The aleph function gives the infinite cardinal numbers. -/
def aleph (o : Ordinal) : Cardinal :=
  sorry

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph0 : Cardinal :=
  sorry

/-- Notation for ℵ₀ -/
notation "ℵ₀" => Cardinal.aleph0

/-- The order type of a cardinal as an ordinal. -/
def ord (c : Cardinal) : Ordinal :=
  sorry

/-- The successor of an ordinal. -/
def Ordinal.succ (o : Ordinal) : Ordinal :=
  sorry

/-- The underlying ordinal of a cardinal's order type. -/
def Ordinal.out (o : Ordinal) : Ordinal :=
  sorry

/-- The first projection of an ordinal. -/
def Ordinal.out.1 (o : Ordinal) : ℕ :=
  sorry

/-- The cardinality of the universal set. -/
theorem mk_univ (α : Type u) : #(Set.univ : Set α) = #α :=
  sorry

/-- The cardinality of the power set. -/
theorem mk_set (α : Type u) : #(Set α) = 2 ^ #α :=
  sorry

/-- Cardinal inequality for power sets. -/
theorem power_le_power_right {a b c : Cardinal} (h : b ≤ c) : a ^ b ≤ a ^ c :=
  sorry

/-- A set is countable iff its cardinality is ≤ ℵ₀. -/
theorem le_aleph0_iff_set_countable {α : Type u} (s : Set α) : #s ≤ ℵ₀ ↔ Countable s :=
  sorry

end Cardinal

/-- The ordinal type. -/
def Ordinal : Type (u + 1) :=
  sorry
