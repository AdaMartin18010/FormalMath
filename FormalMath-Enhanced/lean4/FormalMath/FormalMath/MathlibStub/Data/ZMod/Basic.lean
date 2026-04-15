/-
# ZMod Basic - Stub

This is a minimal stub for Mathlib's ZMod.Basic module.
-/

import FormalMath.MathlibStub

/-- ZMod n is the type of integers modulo n. -/
def ZMod (n : ℕ) : Type :=
  Fin n

namespace ZMod

/-- The Chinese Remainder Theorem as a ring isomorphism. -/
def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  sorry

end ZMod
