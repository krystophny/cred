/-
  Cred Approx Example: Compatible Discretization, d∘d = 0 (issue #624)

  A compatible (mimetic) discretization is one that reproduces a structural
  identity of the continuum operators, not merely one that is locally accurate.
  The defining identity of a cochain complex is `d ∘ d = 0`.

  We build the smallest nontrivial complex on a periodic 1D grid `Fin (n+1)`:

    V0 = (Fin (n+1) → ℝ)   node values
    V1 = (Fin (n+1) → ℝ)   edge values
    V2 = ℝ                 the loop functional

  with the discrete gradient `d0 u i = u (i+1) - u i` (forward difference with
  periodic wrap) and the loop sum `d1 w = ∑ i, w i`. On a closed periodic loop
  every gradient telescopes, so `d1 (d0 u) = 0` for all `u`: the discrete grad is
  closed (`closedGrad`). Packaged as functions, `d1 ∘ d0` is the zero map.

  The structure score `compatibleScore` is 1 exactly when a candidate edge field
  is closed, i.e. lies in the kernel of `d1`. The gradient always lands there;
  the bridge theorem `grad_is_compatible` records this.

  The contrast is a non-mimetic scheme `d0bad u i = u (i+1) - 2 · u i`, a biased
  difference that does not telescope. On the concrete node field `![0, 1]` over
  `Fin 2` its loop sum is `-1 ≠ 0`, so the bad gradient is not closed and the
  scheme fails the compatibility class.
-/

import Cred.Approx.Structure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Real.Basic

namespace Cred

namespace Approx

open Credence Finset

/-! ## The periodic 1D cochain complex -/

/-- Discrete gradient on the periodic grid `Fin (n+1)`: forward difference with
    wrap-around. This is `d0 : V0 → V1`. -/
def d0 {n : ℕ} (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := fun i => u (i + 1) - u i

/-- Loop functional: the total sum around the periodic grid. This is the next
    coboundary `d1 : V1 → V2`, collapsing an edge field to its circulation. -/
def d1 {n : ℕ} (w : Fin (n + 1) → ℝ) : ℝ := ∑ i, w i

/-- An edge field is closed when its circulation around the loop vanishes. -/
def Closed {n : ℕ} (w : Fin (n + 1) → ℝ) : Prop := d1 w = 0

-- `Closed` is a real equation; its decidability is classical.
noncomputable instance {n : ℕ} : DecidablePred (Closed (n := n)) := fun _ => Classical.dec _

/-! ## The defining identity: d1 ∘ d0 = 0 -/

/-- The shift `i ↦ i + 1` is a permutation of the periodic grid, so summing a
    function over the shifted index equals summing it over the index. -/
theorem sum_shift {n : ℕ} (u : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), u (i + 1)) = ∑ i : Fin (n + 1), u i :=
  Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) u

/-- The discrete gradient is closed: its loop sum is zero. This is the discrete
    `div ∘ grad = 0` / `∑ grad = 0` identity, the heart of `d ∘ d = 0`. -/
theorem closedGrad {n : ℕ} (u : Fin (n + 1) → ℝ) : d1 (d0 u) = 0 := by
  simp only [d1, d0]
  rw [Finset.sum_sub_distrib, sum_shift, sub_self]

/-- The composition `d1 ∘ d0` is the zero map: the cochain identity `d ∘ d = 0`
    stated at the level of operators. -/
theorem d1_comp_d0_eq_zero {n : ℕ} :
    (d1 ∘ d0 : (Fin (n + 1) → ℝ) → ℝ) = fun _ => 0 := by
  funext u
  exact closedGrad u

/-- Every gradient field is closed. -/
theorem closed_d0 {n : ℕ} (u : Fin (n + 1) → ℝ) : Closed (d0 u) := closedGrad u

/-! ## Compatibility as a crisp structure -/

/-- Compatibility score of an edge field: certainty exactly when it is closed,
    i.e. lies in the kernel of the next coboundary `d1`. -/
noncomputable def compatibleScore {n : ℕ} : (Fin (n + 1) → ℝ) → Credence :=
  crispScore (Closed (n := n))

@[simp] theorem compatibleScore_one_iff {n : ℕ} (w : Fin (n + 1) → ℝ) :
    compatibleScore w = 1 ↔ d1 w = 0 :=
  crispScore_one_iff (Closed (n := n)) w

/-- Bridge: the discrete gradient lands in the compatible (kernel) class. A
    discretization that produces gradients is compatible because it reproduces
    `d ∘ d = 0`, not merely because it is accurate. -/
theorem grad_is_compatible {n : ℕ} (u : Fin (n + 1) → ℝ) :
    ExactPreserves compatibleScore (d0 u) := by
  rw [ExactPreserves_def, compatibleScore_one_iff]
  exact closedGrad u

/-! ## A non-mimetic scheme breaks the identity -/

/-- A biased discrete gradient: `u (i+1) - 2·u i`. It is locally a difference but
    does not telescope around the loop, so it violates `d ∘ d = 0`. -/
def d0bad (u : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => u (i + 1) - 2 * u i

/-- The biased gradient of the node field `![0, 1]` has loop sum `-1`. -/
theorem d1_d0bad_value : d1 (d0bad ![0, 1]) = -1 := by
  show (∑ i, (d0bad ![0, 1]) i) = -1
  rw [Fin.sum_univ_two]
  show (![(0 : ℝ), 1] ((0 : Fin 2) + 1) - 2 * ![(0 : ℝ), 1] 0)
      + (![(0 : ℝ), 1] ((1 : Fin 2) + 1) - 2 * ![(0 : ℝ), 1] 1) = -1
  rw [show ((0 : Fin 2) + 1) = 1 from rfl, show ((1 : Fin 2) + 1) = 0 from rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Concrete witness: the biased gradient of `![0, 1]` is not closed, so the
    biased scheme is incompatible. -/
theorem d0bad_not_closed : ¬ Closed (d0bad ![0, 1]) := by
  show ¬ d1 (d0bad ![0, 1]) = 0
  rw [d1_d0bad_value]
  norm_num

/-- The biased scheme fails the compatibility class: its image of `![0, 1]` does
    not exactly preserve `compatibleScore`. -/
theorem d0bad_not_compatible : ¬ ExactPreserves compatibleScore (d0bad ![0, 1]) := by
  rw [ExactPreserves_def, compatibleScore_one_iff]
  rw [d1_d0bad_value]
  norm_num

end Approx

end Cred
