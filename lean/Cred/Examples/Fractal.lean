/-
  Cred Examples: The Cantor Set as a Graded-Structure Benchmark (issue #681)

  The middle-thirds Cantor set is the attractor of the iterated function system
  of the two contractions `x ↦ x/3` and `x ↦ (x+2)/3`, both with ratio `1/3`.
  Under the open-set condition its similarity dimension is the Moran solution
  `s` of `2 · (1/3)^s = 1`, namely `s = log 2 / log 3 ≈ 0.6309`.

  This file pins down TWO numeric degrees, each from a NAMED source (governing
  rule #680), never an arbitrary fuzzy label:

  - PRECISE (Moran similarity dimension): `cantorDim = log 2 / log 3`, with the
    Moran equation `cantor_moran : 2 * (1/3)^cantorDim = 1` proved exactly. The
    source of the number is the open-set-condition fixed-point equation for two
    maps of ratio `1/3`.

  - BOX COUNTING (finite, exact at natural scales): at stage `k` the standard
    construction is a union of `cantorBoxCount k = 2^k` intervals of length
    `3^{-k}`. The finite box-dimension estimate `log(N) / log(1/ε)` at scale
    `ε = 3^{-k}` is `log(2^k) / log(3^k)`, and `box_estimate_eq_dim` proves this
    equals `cantorDim` exactly for every `k ≥ 1` (the `k`'s cancel). So the
    grid-counting benchmark already returns the precise dimension at these
    scales -- no limiting argument is needed.

  - GRADED STATUS: `exactSelfSimilarityStatus = 1`. The Cantor set equals the
    union of its two `1/3`-scaled copies, so its self-similarity is exact
    (certainty `1`), not graded. `boxResidual k = 0` records that the
    finite-resolution estimate carries no residual at the natural scales.

  HONESTY. This is a *status layer* over one concrete self-similar set with an
  explicit similarity dimension and an explicit exact-at-natural-scales box
  count. It is NOT general fractal theory: we do not formalize Hausdorff
  measure, Hausdorff dimension, the open-set condition as a theorem, or Moran's
  theorem. The dimension here is the *similarity* dimension defined by the
  Moran equation, which for the Cantor set coincides with the Hausdorff
  dimension by Moran's theorem (not proved here).

  Reuses `Cred.Credence` for the status value (`1 = certainty`); uses
  Mathlib `Real.log` and `Real.rpow`.
-/

import Cred.Core.Value
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Cred

namespace Examples

namespace Fractal

open Real

/-! ## Precise: the Moran similarity dimension -/

/-- The Cantor similarity dimension as the Moran solution of `2 · (1/3)^s = 1`,
    in closed form `log 2 / log 3`. -/
noncomputable def cantorDim : ℝ := Real.log 2 / Real.log 3

/-- The closed form, by definition. -/
theorem cantorDim_eq : cantorDim = Real.log 2 / Real.log 3 := rfl

/-- `log 3 ≠ 0`, used to cancel the denominator in the Moran exponent. -/
theorem log_three_ne_zero : Real.log 3 ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num))

/-- The key exponent identity: `log(1/3) · cantorDim = -log 2`.
    Here `log(1/3) = -log 3`, and the `log 3` cancels against the denominator. -/
theorem log_third_mul_cantorDim : Real.log (1 / 3) * cantorDim = -Real.log 2 := by
  rw [cantorDim, one_div, Real.log_inv]
  rw [neg_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ log_three_ne_zero]

/-- The single scaled copy contributes credence-like factor `(1/3)^cantorDim = 1/2`. -/
theorem third_rpow_cantorDim : (1 / 3 : ℝ) ^ cantorDim = 1 / 2 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 3),
    log_third_mul_cantorDim, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- **Moran / open-set-condition equation.** The Cantor set is built from two
    maps of ratio `1/3`; its similarity dimension `cantorDim` is the unique
    `s` with `2 · (1/3)^s = 1`. This proves the equation at `s = cantorDim`. -/
theorem cantor_moran : 2 * (1 / 3 : ℝ) ^ cantorDim = 1 := by
  rw [third_rpow_cantorDim]; norm_num

/-- The Moran solution is unique: `2 · (1/3)^s = 1` forces `s = cantorDim`.
    The function `s ↦ 2·(1/3)^s` is strictly monotone, so its level set at `1`
    is a single point. -/
theorem cantor_moran_unique {s : ℝ} (h : 2 * (1 / 3 : ℝ) ^ s = 1) :
    s = cantorDim := by
  have h13 : (1 / 3 : ℝ) ^ s = 1 / 2 := by linarith
  -- take logs: `s · log(1/3) = log(1/2)`
  have hlog : Real.log ((1 / 3 : ℝ) ^ s) = Real.log (1 / 2) := by rw [h13]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 1 / 3)] at hlog
  -- `log(1/3) = -log 3`, `log(1/2) = -log 2`
  have hl3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  have hl2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hl3, hl2, mul_neg, neg_inj] at hlog
  -- `hlog : s * log 3 = log 2`
  have h3 : Real.log 3 ≠ 0 := log_three_ne_zero
  rw [cantorDim, eq_div_iff h3]
  exact hlog

/-- `cantorDim` lies strictly between `0` and `1`: positive because `log 2 > 0`
    and `log 3 > 0`; below `1` because `log 2 < log 3`. -/
theorem cantorDim_pos : 0 < cantorDim := by
  rw [cantorDim]
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem cantorDim_lt_one : cantorDim < 1 := by
  rw [cantorDim, div_lt_one (Real.log_pos (by norm_num))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem cantorDim_pos_lt_one : 0 < cantorDim ∧ cantorDim < 1 :=
  ⟨cantorDim_pos, cantorDim_lt_one⟩

/-! ## Box counting: finite, exact at natural scales -/

/-- The box count of the stage-`k` Cantor construction at scale `3^{-k}`:
    the union of `2^k` intervals of length `3^{-k}`. -/
def cantorBoxCount (k : ℕ) : ℕ := 2 ^ k

@[simp] theorem cantorBoxCount_zero : cantorBoxCount 0 = 1 := rfl
@[simp] theorem cantorBoxCount_succ (k : ℕ) :
    cantorBoxCount (k + 1) = 2 * cantorBoxCount k := by
  simp only [cantorBoxCount, pow_succ]
  ring

/-- **Box-counting benchmark is exact at the natural scales.** The finite
    box-dimension estimate `log N / log(1/ε)` with `N = 2^k` boxes at scale
    `ε = 3^{-k}` is `log(2^k) / log(3^k)`, and this equals `cantorDim` exactly
    for every `k ≥ 1`, since `log(2^k)/log(3^k) = (k·log 2)/(k·log 3) =
    log 2 / log 3`. No limit is required: the grid count already returns the
    precise similarity dimension at these scales. -/
theorem box_estimate_eq_dim {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((2 : ℝ) ^ k) / Real.log ((3 : ℝ) ^ k) = cantorDim := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  rw [Real.log_pow, Real.log_pow, cantorDim]
  rw [mul_div_mul_left _ _ hk0]

/-- Restated with the named box count: at scale `3^{-k}` the estimate from
    `cantorBoxCount k` boxes equals `cantorDim`. -/
theorem box_estimate_count_eq_dim {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((cantorBoxCount k : ℝ)) / Real.log ((3 : ℝ) ^ k) = cantorDim := by
  have : ((cantorBoxCount k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    simp only [cantorBoxCount]; push_cast; ring
  rw [this]; exact box_estimate_eq_dim hk

/-! ## Graded status

The status credences carry their numeric content from a named source: the
exact self-similarity of the Cantor set (the attractor equals the union of its
two `1/3`-scaled copies) and the exactness of the box count at the natural
scales. They are not arbitrary fuzzy labels. -/

/-- Exact-self-similarity status: certainty `1`. The Cantor set equals the union
    of its two `1/3`-scaled copies, so the self-similar structure is exact, not
    graded. We state this at the level we can prove cleanly: the status value is
    the certainty credence `1`. (We do not formalize the set-equality itself;
    that is the named justification for the value, recorded in the docstring.) -/
def exactSelfSimilarityStatus : Credence := 1

@[simp] theorem exactSelfSimilarityStatus_val :
    exactSelfSimilarityStatus.val = 1 := rfl

/-- The status is full certainty. -/
theorem exactSelfSimilarity_certain : exactSelfSimilarityStatus = 1 := rfl

/-- Finite-resolution residual of the box-counting estimate at scale `3^{-k}`:
    the gap between the estimate and the precise dimension. By
    `box_estimate_eq_dim` this residual is `0` for every `k ≥ 1`. -/
noncomputable def boxResidual (k : ℕ) : ℝ :=
  Real.log ((2 : ℝ) ^ k) / Real.log ((3 : ℝ) ^ k) - cantorDim

/-- The box-counting residual vanishes at every natural scale `k ≥ 1`: the
    finite benchmark is exact, so its finite-resolution status is also
    certainty. -/
theorem boxResidual_eq_zero {k : ℕ} (hk : 1 ≤ k) : boxResidual k = 0 := by
  rw [boxResidual, box_estimate_eq_dim hk, sub_self]

end Fractal

end Examples

end Cred
