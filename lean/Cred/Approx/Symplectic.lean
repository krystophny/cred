/-
  Cred Approx Example: Symplectic Linear Maps (issue #619)

  The structure here is "the linear map preserves the canonical symplectic form
  `J = (0,1;-1,0)`", scored crisply by `Aᵀ J A = J`. For 2x2 real matrices this
  is exactly `det A = 1`, the bridge `symplectic_iff_det`. We read it off from the
  identity `Aᵀ J A = (det A) • J`, which holds for every 2x2 matrix.

  Concrete symplectic maps: the identity, the harmonic-oscillator phase-flow
  rotation `(cos t, -sin t; sin t, cos t)` (Pythagoras gives `det = 1`), and the
  shear `(1, s; 0, 1)`. A non-unit scaling `(a, 0; 0, a)` with `a^2 ≠ 1` is the
  contrast: its determinant `a^2 ≠ 1`, so it breaks the form (witness `a = 2`).

  Integrator comparison for the harmonic oscillator `x' = v, v' = -x`: the
  symplectic (semi-implicit) Euler step `(1, h; -h, 1-h^2)` has determinant `1`
  and is a `Preserves` scheme for the symplectic structure; the explicit Euler
  step `(1, h; -h, 1)` has determinant `1 + h^2`, so at `h = 1` its determinant
  is `2 ≠ 1` and it fails the exact-preservation class.
-/

import Cred.Approx.Structure
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Cred

namespace Approx

open Credence Matrix Real

/-! ## The canonical symplectic form and structure on 2x2 real matrices -/

/-- The canonical symplectic form `J = (0,1;-1,0)`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- A linear map is symplectic when it preserves the form `J`. -/
def Symplectic (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := Aᵀ * J * A = J

/-- For any 2x2 matrix, `Aᵀ J A` is the determinant scaling of `J`. -/
theorem transpose_mul_J_mul (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Aᵀ * J * A = A.det • J := by
  rw [Matrix.det_fin_two A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply] <;> ring

/-- The symplectic form is nonzero (entry `(0,1)` is `1`). -/
theorem J_ne_zero : J ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [J] at this

/-- For 2x2 real matrices, symplecticity is exactly unit determinant. -/
theorem symplectic_iff_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Symplectic A ↔ A.det = 1 := by
  unfold Symplectic
  rw [transpose_mul_J_mul]
  constructor
  · intro h
    have hzero : (A.det - 1) • J = 0 := by
      rw [sub_smul, one_smul, h, sub_self]
    rcases smul_eq_zero.mp hzero with hd | hJ
    · linarith [sub_eq_zero.mp hd]
    · exact absurd hJ J_ne_zero
  · intro h; rw [h, one_smul]

/-! ## Concrete symplectic and non-symplectic maps -/

/-- The identity map is symplectic. -/
theorem symplectic_one : Symplectic (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [symplectic_iff_det]; simp

/-- The harmonic-oscillator rotation `(cos t, -sin t; sin t, cos t)` is symplectic
    for every angle `t` (`sin^2 + cos^2 = 1`). -/
theorem symplectic_rotation (t : ℝ) :
    Symplectic !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] := by
  rw [symplectic_iff_det, Matrix.det_fin_two_of]
  have h := Real.sin_sq_add_cos_sq t
  ring_nf; nlinarith [h]

/-- The shear `(1, s; 0, 1)` is symplectic for every shear amount `s`. -/
theorem symplectic_shear (s : ℝ) : Symplectic !![1, s; 0, 1] := by
  rw [symplectic_iff_det, Matrix.det_fin_two_of]; ring

/-- A non-unit scaling `(a, 0; 0, a)` with `a^2 ≠ 1` is not symplectic. -/
theorem not_symplectic_scaling {a : ℝ} (ha : a ^ 2 ≠ 1) :
    ¬ Symplectic !![a, 0; 0, a] := by
  rw [symplectic_iff_det, Matrix.det_fin_two_of]
  intro h; apply ha; nlinarith [h]

/-- Concrete witness: the scaling by `2` is not symplectic (determinant `4`). -/
theorem not_symplectic_scaling_two : ¬ Symplectic !![(2 : ℝ), 0; 0, 2] := by
  rw [symplectic_iff_det, Matrix.det_fin_two_of]; norm_num

/-! ## Bridge to the structure-degree abstraction -/

-- `Symplectic` is real-matrix equality, so decidability is classical (noncomputable).
noncomputable instance : DecidablePred Symplectic := fun _ => Classical.dec _

/-- Symplecticity as a 0/1 credence structure on 2x2 real matrices. -/
noncomputable def symplecticScore : Matrix (Fin 2) (Fin 2) ℝ → Credence :=
  crispScore Symplectic

@[simp] theorem symplecticScore_one_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    symplecticScore A = 1 ↔ Symplectic A :=
  crispScore_one_iff Symplectic A

/-- Exact preservation of the symplectic structure is exactly symplecticity. -/
theorem exactPreserves_symplecticScore (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ExactPreserves symplecticScore A ↔ Symplectic A :=
  exactPreserves_crispScore Symplectic A

/-! ## Integrator comparison for the harmonic oscillator -/

/-- One symplectic (semi-implicit) Euler step matrix for `x' = v, v' = -x` at step
    `h`: `(1, h; -h, 1 - h^2)`. Its determinant is `1`. -/
def symplecticEuler (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, h; -h, 1 - h ^ 2]

/-- The symplectic Euler step has unit determinant, hence is symplectic. -/
theorem symplecticEuler_symplectic (h : ℝ) : Symplectic (symplecticEuler h) := by
  rw [symplecticEuler, symplectic_iff_det, Matrix.det_fin_two_of]; ring

/-- One explicit (forward) Euler step matrix for `x' = v, v' = -x` at step `h`:
    `(1, h; -h, 1)`. Its determinant is `1 + h^2`. -/
def explicitEulerMatrix (h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, h; -h, 1]

/-- The explicit Euler step determinant is `1 + h^2`. -/
theorem explicitEulerMatrix_det (h : ℝ) : (explicitEulerMatrix h).det = 1 + h ^ 2 := by
  rw [explicitEulerMatrix, Matrix.det_fin_two_of]; ring

/-- For any nonzero step the explicit Euler matrix is not symplectic. -/
theorem explicitEulerMatrix_not_symplectic {h : ℝ} (hh : h ≠ 0) :
    ¬ Symplectic (explicitEulerMatrix h) := by
  rw [symplectic_iff_det, explicitEulerMatrix_det]
  intro hdet
  have : h ^ 2 = 0 := by linarith
  exact hh (by nlinarith [this])

/-- Concrete contrast at step `h = 1`: the symplectic Euler step preserves the
    structure while the explicit Euler step (determinant `2`) does not. -/
theorem euler_step_comparison :
    Symplectic (symplecticEuler 1) ∧ ¬ Symplectic (explicitEulerMatrix 1) :=
  ⟨symplecticEuler_symplectic 1, explicitEulerMatrix_not_symplectic one_ne_zero⟩

end Approx

end Cred
