/-
  Cred Approx: Clipped-Linear Scoring Helper (issue #631)

  Every structure degree in the `Approx` family is read off the same recipe: a
  nonnegative residual `r` is divided by a positive scale `eps`, the linear
  decay `1 - r/eps` is clipped to `[0,1]`, and the result is the score. A
  zero residual scores `1` (exact structure), residuals at or beyond `eps`
  score `0`, and the score is antitone in the residual.

  This is pure real analysis with no dependency beyond Mathlib reals and the
  shared `Structure` abstraction. Other example modules import it to manufacture
  their degrees, so the bounds and the characterizations are stated once here.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

open Credence

/-! ## The clipped-linear score -/

/-- Canonical structure score: clip the linear decay `1 - r/eps` to `[0,1]`.
    `r` is a nonnegative residual, `eps > 0` is the scale at which the score
    reaches zero. -/
noncomputable def scoreEps (eps r : ℝ) : ℝ := max 0 (min 1 (1 - r / eps))

/-- The score is never negative (it is a `max` with `0`). -/
theorem scoreEps_nonneg (eps r : ℝ) : 0 ≤ scoreEps eps r :=
  le_max_left _ _

/-- The score never exceeds one (the inner `min` is bounded by `1`). -/
theorem scoreEps_le_one (eps r : ℝ) : scoreEps eps r ≤ 1 := by
  unfold scoreEps
  exact max_le zero_le_one (le_trans (min_le_left _ _) (le_refl 1))

/-- A zero residual scores certainty. -/
theorem scoreEps_one_of_zero {eps : ℝ} (_heps : 0 < eps) : scoreEps eps 0 = 1 := by
  unfold scoreEps
  rw [zero_div, sub_zero, min_eq_left (le_refl 1), max_eq_right zero_le_one]

/-- With a positive scale and a nonnegative residual, the score is certainty
    exactly when the residual vanishes. -/
theorem scoreEps_eq_one_iff {eps r : ℝ} (heps : 0 < eps) (hr : 0 ≤ r) :
    scoreEps eps r = 1 ↔ r = 0 := by
  constructor
  · intro h
    unfold scoreEps at h
    -- the `max 0 …` equals 1, so the inner value reaches 1, forcing r/eps ≤ 0
    have hmin : min 1 (1 - r / eps) = 1 := by
      rcases le_or_lt 1 (1 - r / eps) with hcase | hcase
      · exact min_eq_left hcase
      · exfalso
        have hlt : min 1 (1 - r / eps) = 1 - r / eps := min_eq_right (le_of_lt hcase)
        rw [hlt] at h
        have : max 0 (1 - r / eps) < 1 := by
          rcases le_or_lt 0 (1 - r / eps) with hc2 | hc2
          · rw [max_eq_right hc2]; exact hcase
          · rw [max_eq_left (le_of_lt hc2)]; linarith
        linarith [h ▸ this]
    have hle : (1 : ℝ) ≤ 1 - r / eps := by
      have := min_le_right (1 : ℝ) (1 - r / eps)
      rw [hmin] at this; exact this
    have hdiv : r / eps ≤ 0 := by linarith
    have hrle : r ≤ 0 := by
      have := (div_nonpos_iff).mp hdiv
      rcases this with ⟨_, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    linarith
  · intro h
    rw [h]
    exact scoreEps_one_of_zero heps

/-- Residuals at or past the scale score zero. -/
theorem scoreEps_zero_of_ge {eps r : ℝ} (heps : 0 < eps) (hr : eps ≤ r) :
    scoreEps eps r = 0 := by
  unfold scoreEps
  have hge : (1 : ℝ) ≤ r / eps := (one_le_div heps).mpr hr
  have hle : 1 - r / eps ≤ 0 := by linarith
  have hmin : min 1 (1 - r / eps) = 1 - r / eps :=
    min_eq_right (le_trans hle zero_le_one)
  rw [hmin, max_eq_left hle]

/-- The score is antitone in the residual: larger residuals score lower. -/
theorem scoreEps_antitone {eps r1 r2 : ℝ} (heps : 0 < eps) (h : r1 ≤ r2) :
    scoreEps eps r2 ≤ scoreEps eps r1 := by
  unfold scoreEps
  have hdiv : r1 / eps ≤ r2 / eps := by gcongr
  have hlin : 1 - r2 / eps ≤ 1 - r1 / eps := by linarith
  have hmin : min 1 (1 - r2 / eps) ≤ min 1 (1 - r1 / eps) := by
    apply le_min
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) hlin
  exact max_le_max (le_refl 0) hmin

/-! ## Bridge to credences -/

/-- The clipped-linear score packaged as a credence, using its `[0,1]` bounds. -/
noncomputable def scoreEpsCredence (eps r : ℝ) : Credence :=
  Credence.mk' (scoreEps eps r) (scoreEps_nonneg eps r) (scoreEps_le_one eps r)

@[simp] theorem scoreEpsCredence_val (eps r : ℝ) :
    (scoreEpsCredence eps r).val = scoreEps eps r := rfl

/-- A zero residual gives the certainty credence. -/
theorem scoreEpsCredence_one_of_zero {eps : ℝ} (heps : 0 < eps) :
    scoreEpsCredence eps 0 = 1 := by
  apply Credence.ext
  rw [scoreEpsCredence_val, one_val, scoreEps_one_of_zero heps]

/-- Residuals at or past the scale give the impossibility credence. -/
theorem scoreEpsCredence_zero_of_ge {eps r : ℝ} (heps : 0 < eps) (hr : eps ≤ r) :
    scoreEpsCredence eps r = 0 := by
  apply Credence.ext
  rw [scoreEpsCredence_val, zero_val, scoreEps_zero_of_ge heps hr]

end Approx

end Cred
