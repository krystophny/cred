/-
  Cred Approx: Positivity-Preserving Scalar Updates

  Carrier: ℝ. Structure: nonnegativity, scored via crispScore.
  Good scheme: x ↦ x / (1 + a·x) for a ≥ 0, x ≥ 0. Preserves
  nonnegativity because denominator is positive and numerator is nonneg.
  Bad scheme: explicit Euler x ↦ x - h with step h > 0. Fails for
  x ∈ (0, h): the output is negative, so ExactPreserves fails.
-/

import Cred.Core.Value
import Cred.Approx.Structure

namespace Cred

namespace Approx

open Credence

/-! ## The nonnegativity structure on ℝ -/

/-- Nonnegativity of a real number, as a crisp 0/1 credence score. -/
noncomputable def nonnegScore : ℝ → Credence := crispScore (fun x : ℝ => 0 ≤ x)

@[simp] theorem nonnegScore_one_iff (x : ℝ) : nonnegScore x = 1 ↔ 0 ≤ x := by
  simp [nonnegScore]

@[simp] theorem nonnegScore_zero_iff (x : ℝ) : nonnegScore x = 0 ↔ x < 0 := by
  simp only [nonnegScore, crispScore_zero_iff]
  exact not_le

/-- ExactPreserves nonnegScore x is equivalent to 0 ≤ x. -/
@[simp] theorem exactPreserves_nonneg_iff (x : ℝ) :
    ExactPreserves nonnegScore x ↔ 0 ≤ x := by
  simp [ExactPreserves_def, nonnegScore]

/-! ## Good scheme: implicit / positivity-preserving update -/

/-- Implicit-style update: x ↦ x / (1 + a · x) for a ≥ 0.
    The denominator is always ≥ 1 for x ≥ 0, so the output is nonneg. -/
noncomputable def implicitUpdate (a : ℝ) (x : ℝ) : ℝ := x / (1 + a * x)

/-- For a ≥ 0 and x ≥ 0, the implicit update preserves nonnegativity. -/
theorem implicitUpdate_nonneg (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ implicitUpdate a x := by
  unfold implicitUpdate
  apply div_nonneg hx
  have : 0 ≤ a * x := mul_nonneg ha hx
  linarith

/-- The implicit update Preserves nonnegativity. -/
theorem implicitUpdate_preserves (a : ℝ) (ha : 0 ≤ a) :
    Preserves nonnegScore (implicitUpdate a) := by
  intro x hx
  rw [exactPreserves_nonneg_iff] at hx ⊢
  exact implicitUpdate_nonneg a ha x hx

/-! ## Bad scheme: explicit Euler x ↦ x - h -/

/-- Explicit Euler subtraction: x ↦ x - h. -/
def explicitEuler (h : ℝ) (x : ℝ) : ℝ := x - h

/-- For any h > 0, the explicit Euler scheme does NOT preserve nonnegativity:
    x = h/2 is nonneg but x - h = -h/2 < 0. -/
theorem explicitEuler_not_preserves (h : ℝ) (hpos : 0 < h) :
    ¬ Preserves nonnegScore (explicitEuler h) := by
  -- witness: x₀ = h/2 ∈ [0, ∞) but x₀ - h = -h/2 < 0
  intro hpres
  have hx : ExactPreserves nonnegScore (h / 2) := by
    rw [exactPreserves_nonneg_iff]
    linarith
  have hafter := hpres (h / 2) hx
  rw [exactPreserves_nonneg_iff] at hafter
  unfold explicitEuler at hafter
  linarith

/-! ## Concrete counterexample: x = 1/2, h = 1 -/

/-- Starting at x = 1/2 with step h = 1, the explicit Euler step gives -1/2 < 0,
    so ExactPreserves fails after one step. -/
theorem explicitEuler_counterexample :
    ExactPreserves nonnegScore (1 / 2 : ℝ) ∧
    ¬ ExactPreserves nonnegScore (explicitEuler 1 (1 / 2 : ℝ)) := by
  constructor
  · rw [exactPreserves_nonneg_iff]
    norm_num
  · rw [exactPreserves_nonneg_iff]
    unfold explicitEuler
    norm_num

end Approx

end Cred
