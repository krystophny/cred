/-
  Cred Approx Example: Finite-Volume Mass Conservation (issue #622)

  The carrier is the state of a periodic grid of `n` cells, `u : Fin n → ℝ`.
  A conservative finite-volume scheme updates each cell by the net flux through
  its two faces: `u i ↦ u i - (F (i+1) - F i)`, with cyclic indexing on `Fin n`.
  The structure preserved is the total mass `∑ i, u i`. Conservation is exact
  because the flux differences telescope around the cycle: the map `i ↦ i+1` is a
  bijection of `Fin n` (`Equiv.addRight 1`), so `∑ i, (F (i+1) - F i) = 0`.

  The contrast is a value-local but non-conservative update: pointwise damping
  `u i ↦ u i - λ·u i` reads only the local cell yet shrinks the total mass. The
  concrete witness is the single-cell grid carrying mass `1`, damped by `λ = 1/2`
  to mass `1/2 ≠ 1`.

  Bridge: total mass at target `m` is a crisp 0/1 structure `massScore m`. The
  finite-volume update is a `Preserves` scheme for it at every `m`; the damping
  update is not.
-/

import Cred.Approx.Structure
import Mathlib.Algebra.BigOperators.Fin

namespace Cred

namespace Approx

open Credence Finset

/-! ## Total mass on a periodic grid -/

/-- Total mass of a grid state: the sum over all cells. -/
def totalMass {n : ℕ} (u : Fin n → ℝ) : ℝ := ∑ i, u i

/-- One conservative finite-volume update on a periodic grid: each cell loses the
    net flux through its two faces. `F i` is the flux at face `i-1/2`; indexing is
    cyclic on `Fin n` (so `i+1` wraps around). Needs `n ≠ 0` for the cyclic group
    structure on `Fin n`. -/
def fvUpdate {n : ℕ} [NeZero n] (F u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => u i - (F (i + 1) - F i)

/-! ## Telescoping cancellation and mass conservation -/

/-- The flux differences telescope to zero around the cycle: `i ↦ i+1` is a
    bijection of `Fin n` (`Equiv.addRight 1`), so the shifted sum equals the
    original and the difference vanishes. -/
theorem flux_telescope {n : ℕ} [NeZero n] (F : Fin n → ℝ) :
    ∑ i : Fin n, (F (i + 1) - F i) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hshift : ∑ i : Fin n, F (i + 1) = ∑ i : Fin n, F i :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) F
  rw [hshift, sub_self]

/-- The key conservation law: a finite-volume update leaves the total mass
    unchanged, because the net face fluxes cancel around the periodic cycle. -/
theorem fvUpdate_conserves {n : ℕ} [NeZero n] (F u : Fin n → ℝ) :
    totalMass (fvUpdate F u) = totalMass u := by
  unfold totalMass fvUpdate
  rw [Finset.sum_sub_distrib, flux_telescope, sub_zero]

/-! ## The mass structure as a crisp 0/1 score -/

/-- A grid state carries target mass `m` when its total mass is exactly `m`. -/
def HasMass {n : ℕ} (m : ℝ) (u : Fin n → ℝ) : Prop := totalMass u = m

-- `HasMass` is real equality, so its decidability is classical (noncomputable).
noncomputable instance {n : ℕ} (m : ℝ) : DecidablePred (HasMass (n := n) m) :=
  fun _ => Classical.dec _

/-- Carrying target mass `m` as a 0/1 credence structure on grid states. -/
noncomputable def massScore {n : ℕ} (m : ℝ) : (Fin n → ℝ) → Credence :=
  crispScore (HasMass m)

@[simp] theorem massScore_one_iff {n : ℕ} (m : ℝ) (u : Fin n → ℝ) :
    massScore m u = 1 ↔ totalMass u = m :=
  crispScore_one_iff (HasMass m) u

/-! ## Finite-volume update preserves the mass structure -/

/-- The finite-volume update is an exact mass-preservation scheme at every target
    mass `m`: starting on the mass-`m` class it stays there. -/
theorem fvUpdate_preserves {n : ℕ} [NeZero n] (F : Fin n → ℝ) (m : ℝ) :
    Preserves (massScore m) (fvUpdate F) := by
  intro u hu
  rw [ExactPreserves_def] at hu ⊢
  rw [massScore_one_iff] at hu ⊢
  rw [fvUpdate_conserves]
  exact hu

/-! ## A value-local but non-conservative update breaks mass -/

/-- Pointwise damping: each cell loses a fraction `λ` of its own value. This is
    value-local (it reads only cell `i`) but not conservative. -/
def dampUpdate {n : ℕ} (lam : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => u i - lam * u i

/-- Concrete counterexample: the single-cell grid carrying mass `1`, damped by
    `λ = 1/2`, lands on mass `1/2 ≠ 1`. -/
theorem dampUpdate_breaks_mass :
    HasMass 1 (fun _ : Fin 1 => (1 : ℝ)) ∧
      ¬ HasMass 1 (dampUpdate (1 / 2) (fun _ : Fin 1 => (1 : ℝ))) := by
  refine ⟨?_, ?_⟩
  · show totalMass (fun _ : Fin 1 => (1 : ℝ)) = 1
    unfold totalMass
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · show ¬ totalMass (dampUpdate (1 / 2) (fun _ : Fin 1 => (1 : ℝ))) = 1
    unfold totalMass dampUpdate
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num

/-- The damping update is not a mass-preservation scheme: it fails the exact
    class at the single-cell unit-mass witness. -/
theorem dampUpdate_not_preserves :
    ¬ Preserves (massScore (n := 1) 1) (dampUpdate (1 / 2)) := by
  intro hpres
  have hstart : ExactPreserves (massScore (n := 1) 1) (fun _ => (1 : ℝ)) := by
    rw [ExactPreserves_def, massScore_one_iff]
    unfold totalMass
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have himg := hpres _ hstart
  rw [ExactPreserves_def, massScore_one_iff] at himg
  unfold totalMass dampUpdate at himg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at himg
  norm_num at himg

end Approx

end Cred
