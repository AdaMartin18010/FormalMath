/-
# Data.Nat.Prime - Stub

自然数素性判定
-/

import FormalMath.Mathlib

namespace Nat

/-- A natural number is prime if it has exactly two divisors: 1 and itself. -/
def Prime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- Two numbers are coprime if their gcd is 1. -/
def Coprime (m n : ℕ) : Prop :=
  Nat.gcd m n = 1

namespace Coprime

/-- Bezout's identity: if m and n are coprime, there exist s and t such that s*m + t*n = 1. -/
theorem exists_int_coeffs {m n : ℕ} (h : Coprime m n) : ∃ s t : ℤ, s * m + t * n = 1 :=
  sorry

end Coprime

/-- The gcd of two numbers computed using the extended Euclidean algorithm. -/
def gcdA (m n : ℕ) : ℤ :=
  sorry

/-- The second coefficient from the extended Euclidean algorithm. -/
def gcdB (m n : ℕ) : ℤ :=
  sorry

/-- The extended Euclidean algorithm gives the gcd as a linear combination. -/
theorem gcd_eq_gcd_ab (m n : ℕ) : (gcdA m n) * m + (gcdB m n) * n = Nat.gcd m n :=
  sorry

/-- A prime p divides m or n if it divides their product. -/
theorem dvd_prime {p m n : ℕ} (hp : Prime p) (h : p ∣ m * n) : p ∣ m ∨ p ∣ n :=
  sorry

/-- A prime's only divisors are 1 and itself. -/
theorem dvd_prime_iff {p m : ℕ} (hp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  sorry

/-- The gcd of two numbers. -/
def gcd (m n : ℕ) : ℕ :=
  sorry

end Nat
