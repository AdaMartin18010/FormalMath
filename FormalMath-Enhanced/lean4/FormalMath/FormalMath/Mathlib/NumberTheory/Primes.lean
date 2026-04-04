/-
# NumberTheory.Primes - Stub

素数理论
-/

import FormalMath.Mathlib.Data.Nat.Prime

namespace Nat

/-- The set of prime numbers is infinite. -/
theorem infinite_setOf_prime : Set.Infinite {p : ℕ | Nat.Prime p} :=
  sorry

/-- For any n, there exists a prime p > n. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p : ℕ, Nat.Prime p ∧ p > n :=
  sorry

/-- Every number > 1 has a prime divisor. -/
theorem exists_prime_and_dvd {n : ℕ} (hn : n > 1) : ∃ p : ℕ, Nat.Prime p ∧ p ∣ n :=
  sorry

end Nat
