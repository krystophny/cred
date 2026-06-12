/-
  Cred Approx Example: Energy-Balance Systems (issue #627)

  A finite-dimensional port-Hamiltonian-style toy on a scalar state `x : ℝ`
  with quadratic energy `E x = x^2 / 2`. One discrete step combines linear
  damping (rate `a ≥ 0`, time step `dt`) with an input/source term:

    step a dt input x = x - a*dt*x + dt*input.

  Three regimes of the energy balance:

  * conservation: with `a = 0` and `input = 0` the step is the identity in
    energy, so `E (step 0 dt 0 x) = E x` exactly;
  * dissipation: with `input = 0` and `0 ≤ a*dt ≤ 1` the damping can only spend
    energy, so `E (step a dt 0 x) ≤ E x` (a one-sided balance inequality);
  * exact balance law: in general `E (step a dt input x)` equals `E x` minus a
    dissipation term plus an input/cross term, an algebraic identity.

  The crisp structure here is "the step conserves energy at `x`". Its 0/1 score
  reads off through `StructureDegree`: the conservative scheme keeps the score at
  certainty (exact), the dissipative scheme meets only the zero threshold at a
  witness where strict energy is lost, and the input scheme is branch dependent
  (conserving at the fixed point `x = 0`, breaking it elsewhere).
-/

import Cred.Approx.Structure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cred

namespace Approx

open Credence

/-! ## State, energy, and the discrete step -/

/-- Quadratic energy of the scalar state. -/
noncomputable def E (x : ℝ) : ℝ := x ^ 2 / 2

/-- One discrete step: linear damping at rate `a` over time step `dt`, plus an
    input/source term. -/
def step (a dt input x : ℝ) : ℝ := x - a * dt * x + dt * input

@[simp] theorem E_def (x : ℝ) : E x = x ^ 2 / 2 := rfl

@[simp] theorem step_def (a dt input x : ℝ) :
    step a dt input x = x - a * dt * x + dt * input := rfl

/-! ## Conservation: undamped, unforced step keeps energy constant -/

/-- With no damping and no input the step is the identity, hence energy neutral. -/
theorem step_conserves (dt x : ℝ) : E (step 0 dt 0 x) = E x := by
  simp only [step_def, E_def]
  ring

/-! ## Dissipation: damped, unforced step cannot increase energy -/

/-- With no input and a contractive damping factor `0 ≤ a*dt ≤ 1`, the step is
    energy non-increasing: a one-sided balance inequality (dissipation only). -/
theorem step_dissipates {a dt x : ℝ} (h0 : 0 ≤ a * dt) (h1 : a * dt ≤ 1) :
    E (step a dt 0 x) ≤ E x := by
  simp only [step_def, E_def]
  nlinarith [sq_nonneg x, mul_nonneg h0 (sq_nonneg x), sq_nonneg (a * dt)]

/-! ## Exact balance law -/

/-- The exact energy balance: the new energy equals the old energy minus a
    dissipation term `(a*dt)*(1 - (a*dt)/2)*x^2` plus an input/cross term
    `dt*input*((1 - a*dt)*x + dt*input/2)`. This is a pure algebraic identity. -/
theorem energy_balance_law (a dt input x : ℝ) :
    E (step a dt input x)
      = E x
        - (a * dt) * (1 - a * dt / 2) * x ^ 2
        + dt * input * ((1 - a * dt) * x + dt * input / 2) := by
  simp only [step_def, E_def]
  ring

/-! ## Crisp energy-conservation structure -/

/-- The step conserves energy at state `x`: the post-step energy equals the
    pre-step energy. Carries the chosen `a`, `dt`, `input` parameters. -/
def Conserves (a dt input x : ℝ) : Prop := E (step a dt input x) = E x

-- `Conserves` is a real equality, so its decidability is classical.
noncomputable instance (a dt input : ℝ) : DecidablePred (Conserves a dt input) :=
  fun _ => Classical.dec _

/-- Energy conservation as a 0/1 credence structure on the state. -/
noncomputable def conserveScore (a dt input : ℝ) : ℝ → Credence :=
  crispScore (Conserves a dt input)

@[simp] theorem conserveScore_one_iff (a dt input x : ℝ) :
    conserveScore a dt input x = 1 ↔ E (step a dt input x) = E x :=
  crispScore_one_iff (Conserves a dt input) x

/-! ## Bridge: exact vs threshold vs branch-dependent balance -/

/-- Exact regime: the conservative scheme `(a = 0, input = 0)` preserves the
    energy-conservation structure exactly at every state. -/
theorem conserve_exact (dt : ℝ) :
    Preserves (conserveScore 0 dt 0) (step 0 dt 0) := by
  intro x _
  rw [ExactPreserves_def, conserveScore_one_iff]
  exact step_conserves dt _

/-- The conservative scheme sits at certainty: its structure degree is `1`
    everywhere, the top of the threshold scale. -/
theorem conserve_degree_one (dt x : ℝ) :
    StructureDegree (conserveScore 0 dt 0) x = 1 := by
  rw [StructureDegree_def, conserveScore_one_iff]
  exact step_conserves dt x

/-- Threshold regime: a strictly dissipative scheme meets only the zero
    threshold at a witness that genuinely loses energy. With `a*dt = 1` and a
    nonzero state the step sends `x` to `0`, so energy drops from `x^2/2` to `0`
    and the conservation score there is `0` (only `PreservesAt 0`, not exact). -/
theorem dissipative_threshold :
    StructureDegree (conserveScore 1 1 0) 1 = 0
      ∧ PreservesAt 0 (conserveScore 1 1 0) 1
      ∧ ¬ ExactPreserves (conserveScore 1 1 0) 1 := by
  have hscore : conserveScore 1 1 0 1 = 0 := by
    unfold conserveScore
    rw [crispScore_zero_iff]
    show ¬ (E (step 1 1 0 1) = E 1)
    simp only [step_def, E_def]
    norm_num
  refine ⟨hscore, ?_, ?_⟩
  · exact preservesAt_zero (conserveScore 1 1 0) 1
  · rw [ExactPreserves_def, hscore]
    exact zero_ne_one_credence

/-- Branch-dependent regime: a forced scheme `(input ≠ 0)` is the pure
    translation `x ↦ x + 1` (here `a = 0, dt = 1, input = 1`). It conserves
    energy exactly on the reflection-symmetric state `x = -1/2`, whose image
    `1/2` has equal energy, but breaks conservation at that very image `1/2`,
    whose image `3/2` has larger energy. So conservation is state dependent. -/
theorem forced_branch_dependent :
    Conserves 0 1 1 (-1/2) ∧ ¬ Conserves 0 1 1 (1/2) := by
  refine ⟨?_, ?_⟩
  · show E (step 0 1 1 (-1/2)) = E (-1/2)
    simp only [step_def, E_def]; norm_num
  · show ¬ (E (step 0 1 1 (1/2)) = E (1/2))
    simp only [step_def, E_def]; norm_num

/-- The forced scheme is not an exact energy-conservation preservation scheme:
    the state `x = -1/2` conserves energy, so it lies in the exact class, yet its
    image `step 0 1 1 (-1/2) = 1/2` does not conserve. `Preserves` would force
    the image back into the class, a contradiction. -/
theorem forced_not_preserves :
    ¬ Preserves (conserveScore 0 1 1) (step 0 1 1) := by
  intro hpres
  -- the witness state conserves energy, so it is in the exact-preservation class
  have hstart : ExactPreserves (conserveScore 0 1 1) (-1/2) := by
    rw [ExactPreserves_def, conserveScore_one_iff]
    show E (step 0 1 1 (-1/2)) = E (-1/2)
    simp only [step_def, E_def]; norm_num
  -- preservation would put its image in the class too
  have himg := hpres (-1/2) hstart
  rw [ExactPreserves_def, conserveScore_one_iff] at himg
  -- but the image `step 0 1 1 (-1/2) = 1/2` fails conservation
  simp only [step_def, E_def] at himg
  norm_num at himg

end Approx

end Cred
