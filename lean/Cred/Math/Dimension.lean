/-
  Cred Math: Similarity Dimension of an Equal-Ratio IFS (generalizes Fractal.lean)

  `Cred/Examples/Fractal.lean` pins the middle-thirds Cantor set: two contractions
  of ratio `1/3`, similarity dimension `log 2 / log 3`, the Moran equation
  `2 · (1/3)^s = 1`, its uniqueness, and the exact-at-natural-scales box estimate.

  This file generalizes that one concrete attractor to an `n`-map iterated
  function system whose maps all share a single contraction ratio `r ∈ (0,1)`.
  Under the open-set condition the similarity dimension is the Moran solution `s`
  of `n · r^s = 1`, in closed form `similarityDim n r = log n / log(1/r)`. The
  Cantor set is the instance `n = 2`, `r = 1/3`.

  As in `Fractal.lean` this is a *similarity-dimension* layer over the Moran
  fixed-point equation. We do not formalize Hausdorff measure, Hausdorff
  dimension, the open-set condition as a theorem, or Moran's theorem; the
  equality with the Hausdorff dimension under the open-set condition is the named
  justification recorded here, not proved.

  Tactics mirror `Fractal.lean`: `rpow_def_of_pos` + `exp_neg` + `exp_log` for the
  Moran equation, `log_rpow` for uniqueness, `log_pow` cancellation for the box
  estimate.
-/

import Cred.Core.Value
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Cred

namespace Math

open Real

/-! ## Similarity dimension of an equal-ratio IFS -/

/-- The similarity dimension of an `n`-map IFS of common ratio `r`, the Moran
    solution of `n · r^s = 1` in closed form `log n / log(1/r)`. -/
noncomputable def similarityDim (n : ℕ) (r : ℝ) : ℝ := Real.log n / Real.log (1 / r)

/-- The closed form, by definition. -/
theorem similarityDim_eq (n : ℕ) (r : ℝ) :
    similarityDim n r = Real.log n / Real.log (1 / r) := rfl

/-- The denominator `log (1/r)` is positive for `r ∈ (0,1)`: then `1/r > 1`, so
    its log is positive. This is the analogue of `log 3 > 0`. -/
theorem log_inv_r_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < Real.log (1 / r) := by
  apply Real.log_pos
  rw [lt_div_iff₀ hr, one_mul]
  exact hr1

/-- `log (1/r) ≠ 0`, used to cancel the denominator. -/
theorem log_inv_r_ne_zero {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.log (1 / r) ≠ 0 :=
  ne_of_gt (log_inv_r_pos hr hr1)

/-- The key exponent identity: `log r · similarityDim n r = -log n`.
    Here `log r = -log(1/r)`, and the `log(1/r)` cancels against the denominator.
    Analogue of `log_third_mul_cantorDim`. -/
theorem log_r_mul_similarityDim {n : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.log r * similarityDim n r = -Real.log n := by
  have hne : Real.log (1 / r) ≠ 0 := log_inv_r_ne_zero hr hr1
  have hlr : Real.log r = -Real.log (1 / r) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [similarityDim, hlr, neg_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]

/-- A single scaled copy contributes factor `r^(similarityDim n r) = 1/n`.
    Analogue of `third_rpow_cantorDim`. -/
theorem r_rpow_similarityDim {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 0 < r) (hr1 : r < 1) :
    r ^ (similarityDim n r) = 1 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  rw [Real.rpow_def_of_pos hr, log_r_mul_similarityDim hr hr1, Real.exp_neg,
    Real.exp_log hnpos, one_div]

/-- **Moran / open-set-condition equation.** For an `n`-map IFS of ratio `r`,
    the similarity dimension `similarityDim n r` is the `s` with `n · r^s = 1`.
    Analogue of `cantor_moran`. -/
theorem moran_general {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 0 < r) (hr1 : r < 1) :
    (n : ℝ) * r ^ (similarityDim n r) = 1 := by
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [r_rpow_similarityDim hn hr hr1, mul_one_div, div_self hnne]

/-- The Moran solution is unique: `n · r^s = 1` forces `s = similarityDim n r`.
    The map `s ↦ n · r^s` is strictly monotone, so its level set at `1` is a
    point. Analogue of `cantor_moran_unique`, via `log_rpow`. -/
theorem moran_general_unique {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 0 < r) (hr1 : r < 1)
    {s : ℝ} (h : (n : ℝ) * r ^ s = 1) : s = similarityDim n r := by
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  -- `r^s = 1/n`
  have hrs : r ^ s = 1 / (n : ℝ) := by
    rw [eq_div_iff hnne]
    rw [mul_comm] at h
    exact h
  -- take logs: `s · log r = log (1/n)`
  have hlog : Real.log (r ^ s) = Real.log (1 / (n : ℝ)) := by rw [hrs]
  rw [Real.log_rpow hr] at hlog
  -- `log r = -log(1/r)`, `log(1/n) = -log n`
  have hlr : Real.log r = -Real.log (1 / r) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hln : Real.log (1 / (n : ℝ)) = -Real.log n := by
    rw [one_div, Real.log_inv]
  rw [hlr, hln] at hlog
  -- `hlog : s * (-log(1/r)) = -log n`, hence `s * log(1/r) = log n`
  have hne : Real.log (1 / r) ≠ 0 := log_inv_r_ne_zero hr hr1
  rw [mul_neg, neg_inj] at hlog
  rw [similarityDim, eq_div_iff hne]
  exact hlog

/-- `similarityDim n r` is positive: numerator `log n > 0` (since `n ≥ 2`) and
    denominator `log(1/r) > 0`. Analogue of `cantorDim_pos`. -/
theorem similarityDim_pos {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 0 < r) (hr1 : r < 1) :
    0 < similarityDim n r := by
  rw [similarityDim]
  apply div_pos _ (log_inv_r_pos hr hr1)
  apply Real.log_pos
  have : (2 : ℕ) ≤ n := hn
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
  linarith

/-- `similarityDim n r < 1` exactly when `n < 1/r`: the dimension is below one iff
    the maps shrink fast enough relative to their count. Proof by `log` strict
    monotonicity, since `log` and the positive denominator preserve the order.
    Analogue of `cantorDim_lt_one` (where `2 < 3`). -/
theorem similarityDim_lt_one_iff {n : ℕ} {r : ℝ} (hn : 2 ≤ n) (hr : 0 < r)
    (hr1 : r < 1) : similarityDim n r < 1 ↔ (n : ℝ) < 1 / r := by
  have hden : 0 < Real.log (1 / r) := log_inv_r_pos hr hr1
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hinvpos : (0 : ℝ) < 1 / r := by positivity
  rw [similarityDim, div_lt_one hden]
  constructor
  · intro h
    -- `log n < log (1/r)` ⇒ `n < 1/r` by strict monotonicity of `exp`/injectivity
    by_contra hcon
    push_neg at hcon
    have : Real.log (1 / r) ≤ Real.log n := Real.log_le_log hinvpos hcon
    linarith
  · intro h
    exact Real.log_lt_log hnpos h

/-- **Box-counting benchmark is exact at the natural scales.** The estimate
    `log N / log(1/ε)` with `N = n^k` boxes at scale `ε = r^k` is
    `log(n^k) / log((1/r)^k)`, and the `k`'s cancel to `similarityDim n r` for
    every `k ≥ 1`. Analogue of `box_estimate_eq_dim`. -/
theorem box_estimate_eq_dim {n : ℕ} {r : ℝ} (_hn : 2 ≤ n) (_hr : 0 < r) (_hr1 : r < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((n : ℝ) ^ k) / Real.log ((1 / r) ^ k) = similarityDim n r := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  rw [Real.log_pow, Real.log_pow, similarityDim, mul_div_mul_left _ _ hk0]

/-- The Cantor set is the instance `n = 2`, `r = 1/3`: `similarityDim 2 (1/3)`
    is the Cantor dimension `log 2 / log 3`. The denominator simplifies because
    `1 / (1/3) = 3`. -/
theorem cantor_is_instance : similarityDim 2 (1 / 3) = Real.log 2 / Real.log 3 := by
  rw [similarityDim]
  have hd : (1 : ℝ) / (1 / 3) = 3 := by norm_num
  have hn : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hd, hn]

end Math

end Cred
