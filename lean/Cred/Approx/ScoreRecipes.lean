/-
  Cred Approx: Residual-to-Score Recipe over Rationals (issue #677)

  Governing rule #680: every numeric degree must come from a named source. This
  module pins one such source -- the deterministic residual-to-score recipe -- in
  exact rational arithmetic, so a degree is *by construction* a clipped linear
  reading of a residual `r` against a tolerance `eps`. There is no arbitrary
  fuzzy label: a degree of `1` means the residual vanished, a degree of `0` means
  the residual reached the tolerance, and intermediate degrees are the exact
  clipped fraction `1 - r/eps`.

  The real-valued companion lives in `Cred.Approx.Score` and feeds the
  `Credence` carrier. Here the recipe is rational so the bookkeeping is decidable
  and exact; the same shape and the same four characterizations hold.

  Lemmas: `scoreEps_zero` (residual `0` scores `1`), `scoreEps_ge_eps` (residual
  at or past `eps` scores `0`), `scoreEps_mono` (antitone in the residual),
  `scoreEps_mem_unit` (the score lands in `[0,1]` for `r ≥ 0`). The
  robustness-radius recipe `robustnessScore` reuses the same recipe with the
  radius playing the residual role.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

namespace Rat

/-! ## The rational clipped-linear recipe -/

/-- Deterministic residual-to-score recipe over rationals: clip the linear
    decay `1 - r/eps` below at `0`. `r` is a nonnegative residual and
    `eps > 0` is the tolerance at which the score reaches zero. The upper clip
    is implicit: for `0 ≤ r` the linear term never exceeds `1`. -/
def scoreEps (eps r : ℚ) : ℚ := max 0 (1 - r / eps)

/-- A zero residual scores certainty. -/
theorem scoreEps_zero {eps : ℚ} (_heps : 0 < eps) : scoreEps eps 0 = 1 := by
  unfold scoreEps
  rw [zero_div, sub_zero, max_eq_right zero_le_one]

/-- The score is never negative (it is a `max` with `0`). -/
theorem scoreEps_nonneg (eps r : ℚ) : 0 ≤ scoreEps eps r :=
  le_max_left _ _

/-- Residuals at or past the tolerance score zero. -/
theorem scoreEps_ge_eps {eps r : ℚ} (heps : 0 < eps) (hr : eps ≤ r) :
    scoreEps eps r = 0 := by
  unfold scoreEps
  have hge : (1 : ℚ) ≤ r / eps := (one_le_div heps).mpr hr
  have hle : 1 - r / eps ≤ 0 := by linarith
  exact max_eq_left hle

/-- The recipe is antitone in the residual: larger residuals score lower. -/
theorem scoreEps_mono {eps r1 r2 : ℚ} (heps : 0 < eps) (h : r1 ≤ r2) :
    scoreEps eps r2 ≤ scoreEps eps r1 := by
  unfold scoreEps
  have hdiv : r1 / eps ≤ r2 / eps := by gcongr
  have hlin : 1 - r2 / eps ≤ 1 - r1 / eps := by linarith
  exact max_le_max (le_refl 0) hlin

/-- For a nonnegative residual the score never exceeds one. -/
theorem scoreEps_le_one {eps r : ℚ} (heps : 0 < eps) (hr : 0 ≤ r) :
    scoreEps eps r ≤ 1 := by
  unfold scoreEps
  have hdiv : 0 ≤ r / eps := div_nonneg hr (le_of_lt heps)
  have hlin : 1 - r / eps ≤ 1 := by linarith
  exact max_le zero_le_one hlin

/-- For a nonnegative residual the score lands in the unit interval. -/
theorem scoreEps_mem_unit {eps r : ℚ} (heps : 0 < eps) (hr : 0 ≤ r) :
    0 ≤ scoreEps eps r ∧ scoreEps eps r ≤ 1 :=
  ⟨scoreEps_nonneg eps r, scoreEps_le_one heps hr⟩

/-- With positive tolerance and nonnegative residual, the score is certainty
    exactly when the residual vanishes. -/
theorem scoreEps_eq_one_iff {eps r : ℚ} (heps : 0 < eps) (hr : 0 ≤ r) :
    scoreEps eps r = 1 ↔ r = 0 := by
  constructor
  · intro h
    unfold scoreEps at h
    have hub : (1 : ℚ) - r / eps ≤ 1 := by
      have hdiv : 0 ≤ r / eps := div_nonneg hr (le_of_lt heps)
      linarith
    have hle : (1 : ℚ) ≤ 1 - r / eps := by
      have hmax : max 0 (1 - r / eps) ≤ 1 := max_le zero_le_one hub
      rcases le_total 0 (1 - r / eps) with hge | hlt
      · rw [max_eq_right hge] at h; exact le_of_eq h.symm
      · rw [max_eq_left hlt] at h; exact absurd h (by norm_num)
    have hdiv : r / eps ≤ 0 := by linarith
    have hrle : r ≤ 0 := by
      rcases (div_nonpos_iff).mp hdiv with ⟨_, hd⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    linarith
  · intro h
    rw [h]; exact scoreEps_zero heps

/-! ## Robustness-radius recipe

  A robustness radius `rad ≥ 0` is the largest residual still tolerated. Scoring
  a residual `r` against that radius is the same recipe with `eps := rad`, so the
  degree reads "how far inside the robustness ball" the residual sits: `1` at the
  centre, `0` at or beyond the radius. -/

/-- Robustness score: the residual-to-score recipe with the robustness radius
    `rad > 0` as the tolerance. -/
def robustnessScore (rad r : ℚ) : ℚ := scoreEps rad r

/-- A residual at the centre of the robustness ball scores certainty. -/
theorem robustnessScore_zero {rad : ℚ} (hrad : 0 < rad) :
    robustnessScore rad 0 = 1 :=
  scoreEps_zero hrad

/-- A residual at or beyond the robustness radius scores zero. -/
theorem robustnessScore_ge_rad {rad r : ℚ} (hrad : 0 < rad) (hr : rad ≤ r) :
    robustnessScore rad r = 0 :=
  scoreEps_ge_eps hrad hr

/-- The robustness score is antitone in the residual. -/
theorem robustnessScore_mono {rad r1 r2 : ℚ} (hrad : 0 < rad) (h : r1 ≤ r2) :
    robustnessScore rad r2 ≤ robustnessScore rad r1 :=
  scoreEps_mono hrad h

/-- For a nonnegative residual the robustness score lands in the unit interval. -/
theorem robustnessScore_mem_unit {rad r : ℚ} (hrad : 0 < rad) (hr : 0 ≤ r) :
    0 ≤ robustnessScore rad r ∧ robustnessScore rad r ≤ 1 :=
  scoreEps_mem_unit hrad hr

end Rat

end Approx

end Cred
