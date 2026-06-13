/-
  Cred Examples: the sqrt(3) dependency chain (math-library seed, past sqrt2)

  Second irrationality-style benchmark with the same provenance flavour as
  `Sqrt2Branch`. The arithmetic core of "sqrt(3) is irrational": no coprime
  pair `(p, q)` with `q ≠ 0` satisfies `p*p = 3*(q*q)`. The descent is

      p*p = 3*(q*q)  ⇒  3 ∣ p  ⇒  3 ∣ q  ⇒  ¬ coprime p q  (contradiction).

  Each divisibility step reuses Mathlib's `Nat.Prime.dvd_of_dvd_pow` with the
  prime 3, and the final coprimality block reuses
  `Cred.Math.not_coprime_of_common_prime`. The dependency chain is recorded with
  a small LOCAL inductive, deliberately NOT importing any ProofTheory branch
  type. Fully proved, no axioms beyond Mathlib.
-/

import Cred.Math.Order
import Mathlib.Tactic

namespace Cred.Examples.MathSeed

open Cred.Math

/-! ## Prime-3 divisibility steps -/

/-- `3` is prime (Mathlib fact, recorded for the chain). -/
theorem prime_three : Nat.Prime 3 := by norm_num

/-- If `3 ∣ p*p` then `3 ∣ p`, via `Nat.Prime.dvd_of_dvd_pow` with prime 3. -/
theorem three_dvd_of_dvd_square (p : ℕ) (h : 3 ∣ p * p) : 3 ∣ p := by
  have hpow : (3 : ℕ) ∣ p ^ 2 := by rw [pow_two]; exact h
  exact Nat.Prime.dvd_of_dvd_pow prime_three hpow

/-- From `p*p = 3*(q*q)` the left square is divisible by 3, so `3 ∣ p`. -/
theorem sqrt3_core_dvd_p (p q : ℕ) (h : p * p = 3 * (q * q)) : 3 ∣ p := by
  apply three_dvd_of_dvd_square
  rw [h]
  exact ⟨q * q, rfl⟩

/-- From `p*p = 3*(q*q)` together with `3 ∣ p`, also `3 ∣ q`.
    Writing `p = 3k` gives `9*k*k = 3*q*q`, hence `q*q = 3*(k*k)`, so `3 ∣ q*q`
    and `3 ∣ q` by the prime-3 step. -/
theorem sqrt3_core_dvd_q (p q : ℕ) (h : p * p = 3 * (q * q)) (hp : 3 ∣ p) :
    3 ∣ q := by
  obtain ⟨k, hk⟩ := hp
  apply three_dvd_of_dvd_square
  have hexp : p * p = 9 * (k * k) := by rw [hk]; ring
  have hqq : q * q = 3 * (k * k) := by omega
  rw [hqq]
  exact ⟨k * k, rfl⟩

/-! ## The core contradiction -/

/-- The arithmetic core of "sqrt(3) is irrational": a coprime pair `(p, q)` with
    `q ≠ 0` cannot satisfy `p*p = 3*(q*q)`.

    Chain: `3 ∣ p` (`sqrt3_core_dvd_p`) ⇒ `3 ∣ q` (`sqrt3_core_dvd_q`) ⇒
    `¬ coprime p q` (`not_coprime_of_common_prime` with prime 3), the step that
    introduces the contradiction. -/
theorem sqrt3_core_contradiction (p q : ℕ)
    (hco : Nat.Coprime p q) (h : p * p = 3 * (q * q)) (_hq : q ≠ 0) : False := by
  have hp : 3 ∣ p := sqrt3_core_dvd_p p q h
  have hq3 : 3 ∣ q := sqrt3_core_dvd_q p q h hp
  exact not_coprime_of_common_prime prime_three hp hq3 hco

/-! ## The dependency chain as named steps

A minimal local inductive over the step names, mirroring `Sqrt2Branch.Step`,
with no dependency on any other module's branch / proof-tree type. The
contradiction is introduced at the final step `notCoprime`. -/

/-- The named steps of the classical sqrt(3) descent. Local to this module. -/
inductive Step where
  | rationalRoot      -- assumption: p*p = 3*(q*q) with coprime p q, q ≠ 0
  | threeDvdP         -- 3 ∣ p
  | threeDvdQ         -- 3 ∣ q
  | notCoprime        -- ¬ coprime p q  (introduces the contradiction)
deriving DecidableEq, Repr

/-- The dependency chain, in order. The contradiction is introduced by the final
    step `Step.notCoprime`: `threeDvdP` and `threeDvdQ` together contradict the
    `rationalRoot` coprimality assumption. -/
def sqrt3_dependency_chain : List Step :=
  [Step.rationalRoot, Step.threeDvdP, Step.threeDvdQ, Step.notCoprime]

/-- The chain has the four expected steps in order. -/
theorem sqrt3_dependency_chain_eq :
    sqrt3_dependency_chain =
      [Step.rationalRoot, Step.threeDvdP, Step.threeDvdQ, Step.notCoprime] := rfl

/-- The contradiction-introducing step is the last one. -/
theorem sqrt3_chain_contradiction_step :
    sqrt3_dependency_chain.getLast? = some Step.notCoprime := by decide

/-- The chain has exactly four steps. -/
theorem sqrt3_dependency_chain_length : sqrt3_dependency_chain.length = 4 := rfl

end Cred.Examples.MathSeed
