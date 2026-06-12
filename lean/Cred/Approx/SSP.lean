/-
  Cred Approx Example: Positivity / SSP under a step-size restriction (issue #623)

  The model is scalar linear decay `u' = -c u` with `c ≥ 0`. One explicit
  (forward) Euler step is `uStep c dt u = u - c·dt·u = (1 - c·dt)·u`. The
  structure to preserve is positivity, `0 ≤ u` (the physical invariant of a
  decaying quantity that cannot go negative).

  Positivity preservation is conditional on the step size. The factor
  `(1 - c·dt)` stays nonnegative exactly when `c·dt ≤ 1`. This is the
  CFL-like admissibility condition: a strong-stability-preserving (SSP) bound
  on `dt`.

    status table (crisp positivity score, `crispScore Positive`):

      regime                         | uStep status     | score
      -------------------------------|------------------|------
      0 ≤ c·dt ≤ 1, u ≥ 0            | exact            | 1
      threshold relaxation t ≤ score | admissible at t  | ≥ t
      c·dt > 1, u > 0                | inadmissible     | 0

  Inside `c·dt ≤ 1` the step is structure-preserving (positivity is exact).
  Outside it the step is not merely inaccurate but inadmissible: it produces a
  negative value, so the positivity score collapses to 0. We give the concrete
  witness `c = dt = u = 2` (so `c·dt = 4 > 1`), whose step value is `-6 < 0`.
-/

import Cred.Approx.Structure
import Mathlib.Tactic

namespace Cred

namespace Approx

open Credence

/-! ## Scalar linear-decay model and the positivity structure -/

/-- One explicit (forward) Euler step of `u' = -c u`:
    `u ↦ u - c·dt·u = (1 - c·dt)·u`. -/
def uStep (c dt u : ℝ) : ℝ := u - c * dt * u

/-- The factored form of the Euler step. -/
theorem uStep_factor (c dt u : ℝ) : uStep c dt u = (1 - c * dt) * u := by
  unfold uStep; ring

/-- The positivity structure: a state is positive when `0 ≤ u`. -/
def Positive (u : ℝ) : Prop := 0 ≤ u

-- `Positive` is a real-order predicate, so decidability is classical.
noncomputable instance : DecidablePred Positive := fun _ => Classical.dec _

/-- Positivity as a 0/1 credence structure. -/
noncomputable def positiveScore : ℝ → Credence := crispScore Positive

@[simp] theorem positiveScore_one_iff (u : ℝ) :
    positiveScore u = 1 ↔ 0 ≤ u :=
  crispScore_one_iff Positive u

/-! ## Admissible region: positivity preserved under `c·dt ≤ 1` -/

/-- Inside the SSP region `c·dt ≤ 1`, the Euler step preserves positivity.
    With `0 ≤ u`, `0 ≤ c`, `0 ≤ dt`, and `c·dt ≤ 1` the step value is `≥ 0`. -/
theorem uStep_nonneg (c dt u : ℝ)
    (hu : 0 ≤ u) (_hc : 0 ≤ c) (_hdt : 0 ≤ dt) (hcfl : c * dt ≤ 1) :
    0 ≤ uStep c dt u := by
  rw [uStep_factor]
  have hfac : 0 ≤ 1 - c * dt := by linarith
  exact mul_nonneg hfac hu

/-- Admissibility framed through the crisp positivity score: inside the SSP
    region, an exactly-positive state maps to an exactly-positive image. -/
theorem uStep_preserves_score (c dt : ℝ)
    (hc : 0 ≤ c) (hdt : 0 ≤ dt) (hcfl : c * dt ≤ 1) (u : ℝ)
    (hu : positiveScore u = 1) : positiveScore (uStep c dt u) = 1 := by
  rw [positiveScore_one_iff] at hu ⊢
  exact uStep_nonneg c dt u hu hc hdt hcfl

/-! ## Inadmissible outside the region: positivity violated -/

/-- Outside the SSP region the step can go negative. Concrete witness
    `c = dt = u = 2`: then `c·dt = 4 > 1`, `u = 2 > 0`, yet
    `uStep 2 2 2 = 2 - 4·2 = -6 < 0`. -/
theorem uStep_neg_outside_region :
    (2 : ℝ) * 2 > 1 ∧ (0 : ℝ) < 2 ∧ uStep 2 2 2 < 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold uStep; norm_num

/-- The same failure read off the crisp score: the input is exactly positive
    but the image scores `0`, i.e. inadmissible (not merely inaccurate). -/
theorem uStep_breaks_positivity_score :
    positiveScore 2 = 1 ∧ positiveScore (uStep 2 2 2) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [positiveScore_one_iff]; norm_num
  · rw [positiveScore, crispScore_zero_iff]
    show ¬ (0 ≤ uStep 2 2 2)
    unfold uStep; norm_num

/-! ## Scheme-level statement -/

/-- The step at `c = dt = 2` is not a positivity-preservation scheme: it fails
    the exact-preservation class at the witness `u = 2`. -/
theorem uStep_not_preserves_outside_region :
    ¬ Preserves positiveScore (uStep 2 2) := by
  intro hpres
  have hstart : ExactPreserves positiveScore 2 := by
    rw [ExactPreserves_def, positiveScore_one_iff]; norm_num
  have himg := hpres 2 hstart
  rw [ExactPreserves_def, positiveScore_one_iff] at himg
  -- himg : 0 ≤ uStep 2 2 2, contradicting uStep 2 2 2 = -6
  unfold uStep at himg
  norm_num at himg

end Approx

end Cred
