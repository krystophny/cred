/-
  Cred Approx: Maximum-Principle Preservation

  A value satisfies a maximum principle when it stays in a closed interval [m, M].
  We model this as a crisp structure score on ℝ and prove that a
  convex-combination (averaging) update preserves the bound, then exhibit a
  counterexample for an overshooting scheme.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

namespace MaxPrinciple

open Credence

/-! ## Interval bound structure -/

/-- The structure "value lies in [m, M]": crisp score from a decidable predicate. -/
noncomputable def inBounds (m M : ℝ) : ℝ → Credence :=
  crispScore (fun x => m ≤ x ∧ x ≤ M)

@[simp] theorem inBounds_one_iff (m M x : ℝ) :
    inBounds m M x = 1 ↔ m ≤ x ∧ x ≤ M := crispScore_one_iff _ x

@[simp] theorem inBounds_zero_iff (m M x : ℝ) :
    inBounds m M x = 0 ↔ ¬(m ≤ x ∧ x ≤ M) := crispScore_zero_iff _ x

/-! ## Convex-combination update -/

/-- Credence weight w ∈ [0,1] for blending. -/
structure Weight where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

/-- Weighted average: (1-w)·x + w·y. -/
def avg (w : Weight) (x y : ℝ) : ℝ := (1 - w.val) * x + w.val * y

theorem avg_val (w : Weight) (x y : ℝ) :
    avg w x y = (1 - w.val) * x + w.val * y := rfl

/-- Blending two values in [m, M] stays in [m, M] (lower bound). -/
theorem avg_ge_of_ge (m : ℝ) (w : Weight) (x y : ℝ) (hx : m ≤ x) (hy : m ≤ y) :
    m ≤ avg w x y := by
  simp only [avg_val]
  have hw0 := w.nonneg
  have hw1 := w.le_one
  nlinarith

/-- Blending two values in [m, M] stays in [m, M] (upper bound). -/
theorem avg_le_of_le (M : ℝ) (w : Weight) (x y : ℝ) (hx : x ≤ M) (hy : y ≤ M) :
    avg w x y ≤ M := by
  simp only [avg_val]
  have hw0 := w.nonneg
  have hw1 := w.le_one
  nlinarith

/-- Blending two values in [m, M] stays in [m, M]. -/
theorem avg_inBounds (m M : ℝ) (w : Weight) (x y : ℝ)
    (hx : m ≤ x ∧ x ≤ M) (hy : m ≤ y ∧ y ≤ M) :
    m ≤ avg w x y ∧ avg w x y ≤ M :=
  ⟨avg_ge_of_ge m w x y hx.1 hy.1, avg_le_of_le M w x y hx.2 hy.2⟩

/-! ## Preservation theorem -/

-- A fixed blending target y ∈ [m, M] gives a scheme x ↦ avg w x y.
-- We check that it Preserves the bound structure.

/-- Averaging toward a fixed target in [m, M] preserves exact membership. -/
theorem avg_preserves (m M : ℝ) (w : Weight) (y : ℝ) (hy : m ≤ y ∧ y ≤ M) :
    Preserves (inBounds m M) (fun x => avg w x y) := by
  intro x hx
  rw [ExactPreserves_def] at *
  rw [inBounds_one_iff] at *
  exact avg_inBounds m M w x y hx hy

/-! ## Counterexample: overshooting scheme -/

-- The scheme x ↦ 2·x - m overshoots M when x = M and M > m.
-- Concretely with m = 0, M = 1, x = 1: the image is 2·1 - 0 = 2 > 1.

/-- An overshooting scheme does NOT preserve the bound. -/
theorem overshoot_not_preserves :
    ¬ Preserves (inBounds 0 1) (fun x : ℝ => 2 * x - 0) := by
  intro h
  -- x = 1 is in [0, 1]
  have hmem : ExactPreserves (inBounds 0 1) (1 : ℝ) := by
    rw [ExactPreserves_def, inBounds_one_iff]
    norm_num
  -- the scheme maps 1 to 2·1 - 0 = 2
  have himg := h 1 hmem
  rw [ExactPreserves_def, inBounds_one_iff] at himg
  -- 2 ≤ 1 is false
  norm_num at himg

end MaxPrinciple

end Approx

end Cred
