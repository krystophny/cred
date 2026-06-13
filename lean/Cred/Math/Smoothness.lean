/-
  Cred Math: Differentiability as Credence Status

  A STATUS layer over mathlib's `DifferentiableAt`, not a new calculus. The
  graded datum `diffStatus f x` reports whether `f` is differentiable at `x` as
  a credence: 1 for "certainly differentiable", 0 for "certainly not". This is
  the crisp (two-valued) fragment of differentiability lifted into the credence
  lattice; no genuinely interior values appear, which `diffStatus_crisp`
  records. The classical content stays mathlib's: differentiability decisions,
  the closure lemmas, and the load-bearing kink witness
  `not_differentiableAt_abs_zero`.

  WHY A CRISP STATUS. Differentiability is a yes/no predicate, so the honest
  reading is the two-element image {0, 1} ⊆ Credence. Embedding it as a credence
  lets differentiability sit beside the other graded statuses in this layer and
  be combined with them, while the recovery lemmas pin it back to the underlying
  `DifferentiableAt` so nothing is added and nothing lost.
-/

import Cred.Core.Value
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs

namespace Cred

namespace Math

open Credence
open Classical

/-- Differentiability of `f` at `x` reported as a credence: certainty (1) when
`f` is differentiable there, impossibility (0) otherwise. The `if` is decided
through classical choice on the `DifferentiableAt` proposition. -/
noncomputable def diffStatus (f : ℝ → ℝ) (x : ℝ) : Credence :=
  if DifferentiableAt ℝ f x then 1 else 0

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are `0` and `1`,
which are distinct reals. Used to read the status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

theorem diffStatus_eq_one_iff (f : ℝ → ℝ) (x : ℝ) :
    diffStatus f x = 1 ↔ DifferentiableAt ℝ f x := by
  unfold diffStatus
  by_cases h : DifferentiableAt ℝ f x
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

theorem diffStatus_eq_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    diffStatus f x = 0 ↔ ¬ DifferentiableAt ℝ f x := by
  unfold diffStatus
  by_cases h : DifferentiableAt ℝ f x
  · simp only [h, if_true, not_true, iff_false]
    intro ho; exact absurd ho.symm cred_zero_ne_one
  · simp only [h, if_false, not_false_iff, iff_true]

theorem diffStatus_id (x : ℝ) : diffStatus (fun y => y) x = 1 := by
  rw [diffStatus_eq_one_iff]
  exact differentiableAt_id'

theorem diffStatus_const (c x : ℝ) : diffStatus (fun _ => c) x = 1 := by
  rw [diffStatus_eq_one_iff]
  exact differentiableAt_const c

/-- The load-bearing witness: at its kink `|·|` is not differentiable, so its
status drops to impossibility. This is the point where the crisp status is
genuinely informative rather than always `1`. -/
theorem diffStatus_abs_zero : diffStatus (fun x => |x|) 0 = 0 := by
  rw [diffStatus_eq_zero_iff]
  exact not_differentiableAt_abs_zero

theorem diffStatus_crisp (f : ℝ → ℝ) (x : ℝ) :
    diffStatus f x = 0 ∨ diffStatus f x = 1 := by
  unfold diffStatus
  by_cases h : DifferentiableAt ℝ f x
  · exact Or.inr (by simp [h])
  · exact Or.inl (by simp [h])

end Math

end Cred
