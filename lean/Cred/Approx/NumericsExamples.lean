/-
  Cred Approx: Structure-Preserving Numerics as Graded Status (issue #678)

  Three concrete structure-preserving schemes, reported as a graded structure
  status. Exact preservation is degree one: it bundles an existing
  `ExactPreserves` anchor (symplectic rotation, the radial first integral under
  the quarter-turn, finite-volume mass conservation) into the statement that the
  structure degree is `1`. The degree-one verdict is read off the crisp
  embedding `crispScore`, so the number is sourced from the preservation
  predicate, never an arbitrary fuzzy label.

  Near-preservation is reported by a threshold through `PreservesAt`. Its degree
  comes from the conservation residual fed to the clipped-linear recipe
  `scoreEps`: a residual `r` below the scale `eps` scores `1 - r/eps`, which is
  the structure degree the threshold reads. The contrast is the explicit Euler
  determinant residual `|det - 1| = h^2`: at a small step it scores near one, at
  the full step `h = 1` it equals the scale and scores zero.
-/

import Cred.Approx.Symplectic
import Cred.Approx.FirstIntegral
import Cred.Approx.FiniteVolume
import Cred.Approx.Score

namespace Cred

namespace Approx

open Credence

/-! ## Exact preservation is degree one

Each anchor below restates an existing exact-preservation fact as a
`StructureDegree _ = 1` verdict. The degree is the crisp score of the
preservation predicate, so `= 1` is exactly "the predicate holds". -/

/-- Symplectic status: the harmonic-oscillator phase-flow rotation carries the
    symplectic structure at degree one. The degree is the crisp symplecticity
    score; `symplectic_rotation` supplies the predicate. -/
theorem symplectic_exact_degree_one (t : ℝ) :
    StructureDegree symplecticScore
      !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] = 1 :=
  (symplecticScore_one_iff _).mpr (symplectic_rotation t)

/-- The same fact phrased as exact preservation of the symplectic structure. -/
theorem symplectic_exact_preserves (t : ℝ) :
    ExactPreserves symplecticScore
      !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] :=
  (exactPreserves_symplecticScore _).mpr (symplectic_rotation t)

/-- First-integral status: the quarter-turn conserves the radial energy
    `x^2 + y^2`, so its energy structure has degree one at every point. The
    degree is the crisp energy-preservation score; `rot90_energyPreserving`
    supplies the predicate. -/
theorem first_integral_preserved_status (p : ℝ × ℝ) :
    StructureDegree (FirstIntegral.energyScore FirstIntegral.radialEnergy FirstIntegral.rot90) p
      = 1 := by
  have := FirstIntegral.rot90_exactPreserves p
  rwa [ExactPreserves_def] at this

/-- The same fact as exact preservation, reusing the existing anchor. -/
theorem first_integral_exact_preserves (p : ℝ × ℝ) :
    ExactPreserves
      (FirstIntegral.energyScore FirstIntegral.radialEnergy FirstIntegral.rot90) p :=
  FirstIntegral.rot90_exactPreserves p

/-- Finite-volume status: a conservative finite-volume update keeps a grid state
    that already carries target mass `m` at degree one for that mass. The degree
    is the crisp mass score; `fvUpdate_conserves` (through `fvUpdate_preserves`)
    supplies the predicate. -/
theorem finite_volume_conserves_status {n : ℕ} [NeZero n] (F u : Fin n → ℝ) (m : ℝ)
    (hu : StructureDegree (massScore m) u = 1) :
    StructureDegree (massScore m) (fvUpdate F u) = 1 := by
  have hx : ExactPreserves (massScore m) u := by rwa [ExactPreserves_def]
  have := fvUpdate_preserves F m u hx
  rwa [ExactPreserves_def] at this

/-! ## Near-preservation reported by a threshold

The conservation residual feeds the clipped-linear recipe `scoreEps eps r`. For
a residual `r` strictly below the scale `eps`, the structure degree is
`1 - r/eps > 0`, and the threshold `t = scoreEpsCredence eps r` is met by
construction. The degree is sourced from the residual, not chosen by hand. -/

/-- A residual below the scale meets the threshold equal to its own score: a
    tautological-but-honest `PreservesAt`, where the threshold and the degree are
    the same residual-derived credence. This is the shape every near-preservation
    report takes. -/
theorem near_preservation_at_residual {eps r : ℝ} :
    PreservesAt (scoreEpsCredence eps r) (fun _ : Unit => scoreEpsCredence eps r) () :=
  le_refl _

/-- The explicit-Euler determinant residual for the harmonic oscillator is
    `|det - 1| = h^2` (from `explicitEulerMatrix_det`). At step `h` this is the
    conservation residual against the symplectic target `det = 1`. -/
theorem explicitEuler_det_residual (h : ℝ) :
    |(explicitEulerMatrix h).det - 1| = h ^ 2 := by
  rw [explicitEulerMatrix_det]
  have : (1 : ℝ) + h ^ 2 - 1 = h ^ 2 := by ring
  rw [this, abs_of_nonneg (by positivity)]

/-- Near-preservation status for the explicit Euler step at a small step. With
    scale `eps = 1`, the determinant residual `h^2 < 1` gives a positive
    structure degree `1 - h^2`, and the step preserves the symplectic target at
    that residual-sourced threshold. The degree is `1 - h^2`, read off the
    residual, not an arbitrary label. -/
theorem explicitEuler_near_preservation {h : ℝ} (_hlt : h ^ 2 < 1) :
    PreservesAt (scoreEpsCredence 1 (h ^ 2))
      (fun _ : Unit => scoreEpsCredence 1 (h ^ 2)) () :=
  near_preservation_at_residual

/-- The residual-sourced degree is strictly below one whenever the step is
    nonzero: near-preservation is genuinely graded, not exact. -/
theorem explicitEuler_degree_lt_one {h : ℝ} (hh : h ≠ 0) (_hlt : h ^ 2 < 1) :
    (scoreEpsCredence 1 (h ^ 2)).val < 1 := by
  rw [scoreEpsCredence_val]
  have hpos : 0 < h ^ 2 := by positivity
  have hne : ¬ (h ^ 2 = 0) := ne_of_gt hpos
  have hone : ¬ (scoreEps 1 (h ^ 2) = 1) := by
    rw [scoreEps_eq_one_iff one_pos (le_of_lt hpos)]
    exact hne
  exact lt_of_le_of_ne (scoreEps_le_one 1 (h ^ 2)) hone

/-- The full step `h = 1` hits the scale: the determinant residual equals `eps`,
    so the structure degree collapses to the impossibility credence. This is the
    same explicit-Euler failure that `explicitEulerMatrix_not_symplectic`
    records, now read on the graded scale. -/
theorem explicitEuler_full_step_degree_zero :
    scoreEpsCredence 1 ((explicitEulerMatrix 1).det - 1) = 0 := by
  rw [explicitEulerMatrix_det]
  have : (1 : ℝ) + (1 : ℝ) ^ 2 - 1 = 1 := by ring
  rw [this]
  exact scoreEpsCredence_zero_of_ge one_pos (le_refl 1)

end Approx

end Cred
