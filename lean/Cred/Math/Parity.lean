/-
  Cred Math: Parity (issue #644, phase 1)

  The single parity fact the classical irrationality-of-sqrt(2) argument
  rests on: if `p*p` is even then `p` is even. We reuse Mathlib's prime
  divisibility (`Nat.Prime.dvd_of_dvd_pow` for the prime 2), recasting the
  square `p*p` as `p^2`. No measure theory; pure arithmetic.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Cred.Math

/-- If `p*p` is even then `p` is even. The seed parity step of the classical
    sqrt(2) argument, derived from `Nat.Prime.dvd_of_dvd_pow` with prime 2. -/
theorem even_square_implies_even (p : ℕ) : 2 ∣ p * p → 2 ∣ p := by
  intro h
  have hpow : (2 : ℕ) ∣ p ^ 2 := by
    rw [pow_two]; exact h
  exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hpow

end Cred.Math
