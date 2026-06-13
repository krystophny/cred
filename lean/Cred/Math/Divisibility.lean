/-
  Cred Math: Divisibility (issue #644)

  The divisibility steps of the classical irrationality argument for sqrt(2),
  stated over `ℕ`. Given `p*p = 2*(q*q)`:
  - `p` is even (the left side is even, so apply the parity seed),
  - then `q` is even (substitute `p = 2k`, cancel a factor of 2),
  - and two even numbers with `1 < p` are not coprime (both divisible by 2).

  Reuses `Cred.Math.even_square_implies_even` and Mathlib's `Nat.Coprime`.
-/

import Cred.Math.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Cred.Math

/-- From `p*p = 2*(q*q)` the left-hand square is even, so `p` is even. -/
theorem sqrt2_core_even_p (p q : ℕ) (h : p * p = 2 * (q * q)) : 2 ∣ p := by
  apply even_square_implies_even
  rw [h]
  exact ⟨q * q, rfl⟩

/-- From `p*p = 2*(q*q)` together with `2 ∣ p`, the number `q` is even.
    Writing `p = 2k` gives `4*k*k = 2*q*q`, hence `q*q = 2*(k*k)`, so `q*q`
    is even and `q` is even by the parity seed. -/
theorem sqrt2_core_even_q (p q : ℕ) (h : p * p = 2 * (q * q)) (hp : 2 ∣ p) :
    2 ∣ q := by
  obtain ⟨k, hk⟩ := hp
  apply even_square_implies_even
  -- substitute p = 2k: p*p = 4*(k*k) = 2*(q*q), so q*q = 2*(k*k)
  have hexp : p * p = 4 * (k * k) := by rw [hk]; ring
  have hqq : q * q = 2 * (k * k) := by omega
  rw [hqq]
  exact ⟨k * k, rfl⟩

/-- Two even numbers with `1 < p` are not coprime: 2 divides both, so their
    gcd is at least 2, contradicting coprimality (`gcd = 1`). -/
theorem not_coprime_if_both_even (p q : ℕ) (hp : 2 ∣ p) (hq : 2 ∣ q)
    (_hpos : 1 < p) : ¬ Nat.Coprime p q := by
  intro hco
  -- 2 divides gcd p q, but coprimality forces gcd = 1
  have hdvd : (2 : ℕ) ∣ Nat.gcd p q := Nat.dvd_gcd hp hq
  rw [Nat.Coprime] at hco
  rw [hco] at hdvd
  -- 2 ∣ 1 is impossible
  omega

end Cred.Math
