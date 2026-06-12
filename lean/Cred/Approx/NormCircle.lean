/-
  Cred Approx Example: Norm / Unit-Circle Preservation (issue #616)

  The structure here is "the 2D vector lies on the unit circle", scored crisply
  by `x^2 + y^2 = 1`. Rotation by any angle `t` preserves this exactly (the
  Pythagorean identity `sin^2 + cos^2 = 1`), so rotation is a `Preserves` scheme
  for the unit-circle structure.

  The explicit (forward) Euler step for the harmonic oscillator is the contrast:
  it scales every norm by `1 + h^2`, so it cannot preserve the circle. We give
  the concrete counterexample `(1,0) ↦ (1,-1)` at step `h = 1`, whose image has
  squared norm `2 ≠ 1`.
-/

import Cred.Approx.Structure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Cred

namespace Approx

open Credence Real

/-! ## The unit-circle structure on ℝ × ℝ -/

/-- A point lies on the unit circle when its squared norm is one. -/
def OnCircle (p : ℝ × ℝ) : Prop := p.1 ^ 2 + p.2 ^ 2 = 1

-- `OnCircle` is real equality, so its decidability is classical (noncomputable).
noncomputable instance : DecidablePred OnCircle := fun _ => Classical.dec _

/-- Unit-circle membership as a 0/1 credence structure. -/
noncomputable def circleScore : ℝ × ℝ → Credence := crispScore OnCircle

@[simp] theorem circleScore_one_iff (p : ℝ × ℝ) :
    circleScore p = 1 ↔ p.1 ^ 2 + p.2 ^ 2 = 1 :=
  crispScore_one_iff OnCircle p

/-! ## Rotation preserves the unit circle -/

/-- Rotation of the plane by angle `t` (matrix `(cos t, -sin t; sin t, cos t)`). -/
noncomputable def rotate (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos t * p.1 - Real.sin t * p.2, Real.sin t * p.1 + Real.cos t * p.2)

/-- Rotation keeps the squared norm: a vector form of `sin^2 + cos^2 = 1`. -/
theorem rotate_norm_sq (t : ℝ) (p : ℝ × ℝ) :
    (rotate t p).1 ^ 2 + (rotate t p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [rotate]
  linear_combination (p.1 ^ 2 + p.2 ^ 2) * h

/-- Rotation by any angle preserves the unit-circle structure exactly. -/
theorem rotate_preserves (t : ℝ) : Preserves circleScore (rotate t) := by
  intro p hp
  rw [ExactPreserves_def] at hp ⊢
  rw [circleScore_one_iff] at hp ⊢
  rw [rotate_norm_sq]
  exact hp

/-! ## Explicit Euler for the harmonic oscillator grows the norm -/

/-- One explicit (forward) Euler step of the harmonic oscillator `x' = v, v' = -x`
    with time step `h`: `(x, v) ↦ (x + h·v, v - h·x)`. -/
def eulerStep (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + h * p.2, p.2 - h * p.1)

/-- The explicit Euler step scales every squared norm by `1 + h^2`. -/
theorem eulerStep_norm_sq (h : ℝ) (p : ℝ × ℝ) :
    (eulerStep h p).1 ^ 2 + (eulerStep h p).2 ^ 2 = (1 + h ^ 2) * (p.1 ^ 2 + p.2 ^ 2) := by
  simp only [eulerStep]
  ring

/-- Concrete counterexample: starting on the circle, the Euler step at `h = 1`
    sends `(1,0)` to `(1,-1)`, whose squared norm is `2 ≠ 1`. -/
theorem eulerStep_breaks_circle :
    OnCircle (1, 0) ∧ ¬ OnCircle (eulerStep 1 (1, 0)) := by
  refine ⟨?_, ?_⟩
  · show (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1; norm_num
  · show ¬ ((eulerStep 1 (1, 0)).1 ^ 2 + (eulerStep 1 (1, 0)).2 ^ 2 = 1)
    simp only [eulerStep]
    norm_num

/-- The Euler step is not a unit-circle preservation scheme: it fails the
    exact-preservation class at the witness `(1,0)`. -/
theorem eulerStep_not_preserves : ¬ Preserves circleScore (eulerStep 1) := by
  intro hpres
  have hstart : ExactPreserves circleScore (1, 0) := by
    rw [ExactPreserves_def, circleScore_one_iff]; norm_num
  have himg := hpres (1, 0) hstart
  rw [ExactPreserves_def, circleScore_one_iff] at himg
  -- himg : squared norm of the image is 1, contradicting the explicit value 2
  simp only [eulerStep] at himg
  norm_num at himg

end Approx

end Cred
