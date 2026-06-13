/-
  Cred.Probability.Cox: a conservative finite representation theorem.

  This is NOT the full Cox derivation. We do not run the Cox functional-equation
  argument that derives the product and sum rules from associativity and
  consistency desiderata. Instead we formalize only the conservative back half:
  a finitely additive, normalized, nonnegative plausibility function on a finite
  world set is represented by a `FinMeasure`. The functional-equation derivation
  of additivity itself is deliberately out of scope.

  Concretely, a `Plausibility W` is a map `p : Finset W → ℚ` with

  - `p ∅ = 0`,
  - `p Finset.univ = 1`,
  - `0 ≤ p A`,
  - finite additivity on disjoint events: `Disjoint A B → p (A ∪ B) = p A + p B`.

  We build the representing measure from the singleton masses `mass w = p {w}`.
  Disjoint additivity gives the singleton decomposition `p A = ∑ w ∈ A, p {w}`
  by induction on `A`; normalization at `Finset.univ` then yields the total-mass
  one condition, and the decomposition gives `P μ A = p A` on every event.

  No measure theory: everything is an explicit `Finset.sum` of rationals.
-/

import Cred.Probability.Valuations

namespace Cred.Probability

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A finite plausibility function on a world set `W`: nonnegative, normalized,
    finitely additive on disjoint events, vanishing on the empty event. -/
structure Plausibility (W : Type*) [Fintype W] [DecidableEq W] where
  p : Finset W → ℚ
  empty : p ∅ = 0
  univ : p Finset.univ = 1
  nonneg : ∀ A, 0 ≤ p A
  additive : ∀ A B : Finset W, Disjoint A B → p (A ∪ B) = p A + p B

/-- Singleton decomposition: additivity on disjoint events forces a plausibility
    to be the sum of its singleton values. Proved by induction on the event. -/
theorem Plausibility.singleton_sum (pl : Plausibility W) (A : Finset W) :
    pl.p A = ∑ w ∈ A, pl.p {w} := by
  induction A using Finset.induction with
  | empty => simpa using pl.empty
  | @insert a s ha ih =>
      have hins : insert a s = {a} ∪ s := Finset.insert_eq a s
      have hdisj : Disjoint ({a} : Finset W) s := by
        rw [Finset.disjoint_singleton_left]
        exact ha
      rw [Finset.sum_insert ha, ← ih, hins, pl.additive {a} s hdisj]

/-- The representing measure built from the singleton masses of a plausibility
    function. Nonnegativity is inherited from `pl.nonneg`; the total-mass-one
    condition is the singleton decomposition at `Finset.univ` together with
    normalization. -/
def Plausibility.toMeasure (pl : Plausibility W) : FinMeasure W where
  mass := fun w => pl.p {w}
  nonneg := fun w => pl.nonneg {w}
  total := by
    have h := pl.singleton_sum Finset.univ
    rw [pl.univ] at h
    simpa using h.symm

/-- The conservative finite Cox representation theorem: every finitely additive,
    normalized, nonnegative plausibility function on a finite world set is
    represented by a `FinMeasure`, agreeing with it on every event. This is the
    additivity-to-measure half only; the Cox functional-equation derivation of
    additivity is not claimed here. -/
theorem cox_finite_representation (pl : Plausibility W) :
    ∃ μ : FinMeasure W, ∀ A : Finset W, P μ A = pl.p A := by
  refine ⟨pl.toMeasure, fun A => ?_⟩
  simp only [P, Plausibility.toMeasure]
  exact (pl.singleton_sum A).symm

end Cred.Probability
