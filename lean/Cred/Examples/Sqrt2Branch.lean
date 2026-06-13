/-
  Cred Examples: the sqrt(2) dependency chain (issue #644 / #641 spirit)

  Self-contained encoding of the classical proof that no coprime pair `(p, q)`
  with `q ≠ 0` satisfies `p*p = 2*(q*q)` — the arithmetic core of the
  irrationality of sqrt(2). The chain is

      p*p = 2*(q*q)  ⇒  2 ∣ p  ⇒  2 ∣ q  ⇒  ¬ coprime p q  (contradiction).

  We reuse the parity/divisibility steps from `Cred.Math` and record the chain
  of step names with a small LOCAL inductive, deliberately NOT importing any
  ProofTheory branch type. Fully proved, no axioms beyond Mathlib.
-/

import Cred.Math.Divisibility
import Mathlib.Tactic

namespace Cred.Examples.Sqrt2Branch

open Cred.Math

/-! ## The core contradiction -/

/-- The arithmetic core of "sqrt(2) is irrational": a coprime pair `(p, q)`
    with `q ≠ 0` cannot satisfy `p*p = 2*(q*q)`.

    Chain: `even p` (`sqrt2_core_even_p`) ⇒ `even q` (`sqrt2_core_even_q`) ⇒
    `¬ coprime p q` (`not_coprime_if_both_even`), the step that introduces the
    contradiction. The bound `1 < p` comes from `q ≠ 0`: if `p ≤ 1` then
    `p*p ≤ 1 < 2 ≤ 2*(q*q)`. -/
theorem sqrt2_core_contradiction (p q : ℕ)
    (hco : Nat.Coprime p q) (h : p * p = 2 * (q * q)) (hq : q ≠ 0) : False := by
  have hp : 2 ∣ p := sqrt2_core_even_p p q h
  have hq2 : 2 ∣ q := sqrt2_core_even_q p q h hp
  -- q ≠ 0 forces q*q ≥ 1, so the right side is ≥ 2, so p*p ≥ 2, so 1 < p
  have hqq_pos : 1 ≤ q * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hq hq)
  have hpp : 2 ≤ p * p := by omega
  have hpos : 1 < p := by
    by_contra hle
    push_neg at hle
    interval_cases p <;> omega
  exact not_coprime_if_both_even p q hp hq2 hpos hco

/-! ## The dependency chain as named steps

A minimal local inductive over the step names, with no dependency on any other
module's branch / proof-tree type. The contradiction is introduced at the final
step `notCoprime`. -/

/-- The named steps of the classical sqrt(2) descent. Local to this module. -/
inductive Step where
  | rationalRoot      -- assumption: p*p = 2*(q*q) with coprime p q, q ≠ 0
  | evenP             -- 2 ∣ p
  | evenQ             -- 2 ∣ q
  | notCoprime        -- ¬ coprime p q  (introduces the contradiction)
deriving DecidableEq, Repr

/-- The dependency chain, in order. The contradiction is introduced by the
    final step `Step.notCoprime`: `evenP` and `evenQ` together contradict the
    `rationalRoot` coprimality assumption. -/
def sqrt2_dependency_chain : List Step :=
  [Step.rationalRoot, Step.evenP, Step.evenQ, Step.notCoprime]

/-- The chain has the four expected steps in order. -/
theorem sqrt2_dependency_chain_eq :
    sqrt2_dependency_chain =
      [Step.rationalRoot, Step.evenP, Step.evenQ, Step.notCoprime] := rfl

/-- The contradiction-introducing step is the last one. -/
theorem sqrt2_chain_contradiction_step :
    sqrt2_dependency_chain.getLast? = some Step.notCoprime := by decide

end Cred.Examples.Sqrt2Branch
