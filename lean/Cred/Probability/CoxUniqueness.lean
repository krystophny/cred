/-
  Cred.Probability.CoxUniqueness: uniqueness of the finite Cox representation.

  Cox.lean produces a `FinMeasure` representing a `Plausibility` and agreeing
  with it on every event. Here we record the matching uniqueness facts: the
  singleton masses are exactly the atomic data, so two finite measures with the
  same atomic masses agree on every event, and the representing measure is
  pinned down by the plausibility values on singletons.

  Everything stays an explicit `Finset.sum` of rationals; no measure theory.
  The uniqueness arguments turn agreement on events into agreement on atoms via
  `Finset.sum_singleton`, then propagate back to arbitrary events by congruence
  of the sum.
-/

import Cred.Probability.Cox

namespace Cred.Probability

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Atomic weights of a plausibility are nonnegative: this is just `nonneg`
    specialized to a singleton event. -/
theorem finite_plausibility_atomic_weights_nonneg (pl : Plausibility W) (w : W) :
    0 ≤ pl.p {w} :=
  pl.nonneg {w}

/-- The atomic weights of a plausibility sum to one. The singleton
    decomposition at `Finset.univ` rewrites the total as `pl.p univ`, which
    normalization fixes at one. -/
theorem finite_plausibility_atomic_weights_sum_one (pl : Plausibility W) :
    ∑ w, pl.p {w} = 1 := by
  have h := pl.singleton_sum Finset.univ
  rw [pl.univ] at h
  simpa using h.symm

omit [DecidableEq W] in
/-- A finite measure on events is determined by its atomic masses: equal masses
    on every world force equal probability on every event, by congruence of the
    event sum. -/
theorem finite_probability_unique_from_atoms (μ ν : FinMeasure W)
    (h : ∀ w, μ.mass w = ν.mass w) : ∀ A : Finset W, P μ A = P ν A := by
  intro A
  simp only [P]
  exact Finset.sum_congr rfl (fun w _ => h w)

/-- Uniqueness of the finite Cox representation: any two finite measures that
    both represent the same plausibility agree on every event. Evaluating the
    representations at singletons forces the atomic masses to coincide, and
    `finite_probability_unique_from_atoms` propagates that to all events. -/
theorem cox_representation_unique (pl : Plausibility W) (μ ν : FinMeasure W)
    (hμ : ∀ A, P μ A = pl.p A) (hν : ∀ A, P ν A = pl.p A) :
    ∀ A : Finset W, P μ A = P ν A := by
  have hatoms : ∀ w, μ.mass w = ν.mass w := by
    intro w
    have hμw : P μ {w} = pl.p {w} := hμ {w}
    have hνw : P ν {w} = pl.p {w} := hν {w}
    have hμmass : P μ {w} = μ.mass w := by
      simp only [P, Finset.sum_singleton]
    have hνmass : P ν {w} = ν.mass w := by
      simp only [P, Finset.sum_singleton]
    rw [← hμmass, ← hνmass, hμw, hνw]
  exact finite_probability_unique_from_atoms μ ν hatoms

end Cred.Probability
