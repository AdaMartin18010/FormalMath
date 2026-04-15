/-
# Nat.ModEq - Stub

模同余关系
-/

import FormalMath.MathlibStub

namespace Nat

/-- Modular equality: `a ≡ b [MOD n]` means `a % n = b % n`. -/
def ModEq (a b : ℕ) (n : ℕ) : Prop :=
  a % n = b % n

/-- Notation for modular equality. -/
notation:50 a " ≡ " b " [MOD " n "]" => ModEq a b n

namespace ModEq

/-- Transitivity of modular equality. -/
theorem trans {a b c n : ℕ} (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  unfold ModEq at *
  rw [h1, h2]

/-- Symmetry of modular equality. -/
theorem symm {a b n : ℕ} (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  unfold ModEq at *
  rw [h]

end ModEq

end Nat
