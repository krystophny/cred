/-
  Cred ProofTheory: Theory-Extension Branches over the Foundation Language

  A `TheoryBranch` records a finite theory `T` of foundation formulas together
  with one added formula `R` (a hypothetical extension).  The branch is
  `LocallyInconsistent` when some formula and its negation both appear among the
  formulas it carries.  Mirroring `labelled_no_ex_falso` (`Cred.Sequent`) and
  `local_contradiction_no_explosion` (`Cred.ProofTheory.Branches`), the central
  guarantee is no explosion: a locally inconsistent branch does NOT
  threshold-entail an unrelated formula.

  The witness is a concrete foundation structure that designates the
  inconsistency at the threshold `1/2` (both the formula and its negation
  evaluate to `1/2`) while leaving the unrelated atom undesignated (it evaluates
  to `0`).  The `ThresholdConsequence` target from `Cred.Foundation.Consequence`
  is used directly; there is no object-language conditional.
-/

import Cred.Foundation.Consequence

namespace Cred.ProofTheory

open Cred.Foundation
open Cred.Foundation.Structure

universe u v

/-- A theory-extension branch over the foundation language: a finite theory `T`
    plus a single added formula `R`. -/
structure TheoryBranch (Func : Type u) (Pred : Type v) where
  theory : List (Formula Func Pred)
  added : Formula Func Pred

namespace TheoryBranch

variable {Func : Type u} {Pred : Type v}

/-- All formulas carried by the branch: the theory together with the added
    formula. -/
def formulas (β : TheoryBranch Func Pred) : List (Formula Func Pred) :=
  β.added :: β.theory

/-- A branch is locally inconsistent when some carried formula and its negation
    are both present. -/
def LocallyInconsistent (β : TheoryBranch Func Pred) : Prop :=
  ∃ A : Formula Func Pred, A ∈ β.formulas ∧ Formula.neg A ∈ β.formulas

end TheoryBranch

/-! ## Concrete inconsistent branch and witness over `Fin 2` predicates -/

/-- The carrier of the witness structure: a single point. -/
def Point : Type := Unit

/-- A concrete inconsistent branch over predicate symbols `Fin 2` (no function
    symbols).  The theory holds `atom 0`; the added formula is its negation. -/
def inconsistentBranch : TheoryBranch Empty (Fin 2) where
  theory := [Formula.atom 0 []]
  added := Formula.neg (Formula.atom 0 [])

/-- The branch is locally inconsistent: `atom 0` and `neg (atom 0)` are both
    present. -/
theorem inconsistentBranch_locallyInconsistent :
    inconsistentBranch.LocallyInconsistent := by
  refine ⟨Formula.atom 0 [], ?_, ?_⟩ <;>
    simp [inconsistentBranch, TheoryBranch.formulas]

/-- The witness structure: every predicate `0` evaluates to `1/2`, predicate `1`
    to `0`.  Equality and quantifiers are pinned to fixed values; they are not
    exercised by the branch. -/
noncomputable def witness : Structure Empty (Fin 2) where
  Domain := Point
  witness := ()
  func := fun e _ => e.elim
  pred := fun p _ => if p = 0 then Credence.half else 0
  eq := fun _ _ => 1
  all := fun _ => 1
  ex := fun _ => 0

@[simp] theorem witness_pred_zero (env : witness.Assignment) :
    witness.evalFormula env (Formula.atom 0 []) = Credence.half := by
  show (if (0 : Fin 2) = 0 then Credence.half else 0) = Credence.half
  rw [if_pos rfl]

@[simp] theorem witness_pred_one (env : witness.Assignment) :
    witness.evalFormula env (Formula.atom 1 []) = 0 := by
  show (if (1 : Fin 2) = 0 then Credence.half else 0) = 0
  rw [if_neg (by decide : ¬ (1 : Fin 2) = 0)]

/-- The witness designates the whole inconsistent branch at threshold `1/2`:
    both `atom 0` and `neg (atom 0)` evaluate to `1/2`. -/
theorem witness_designates_branch (env : witness.Assignment) :
    ∀ p ∈ inconsistentBranch.formulas,
      Credence.half ≤ witness.evalFormula env p := by
  intro p hp
  simp only [inconsistentBranch, TheoryBranch.formulas, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · -- neg (atom 0) evaluates to ~(1/2) = 1/2
    show Credence.half ≤ witness.evalFormula env (Formula.neg (Formula.atom 0 []))
    rw [Credence.le_def]
    show (1 : ℝ) / 2 ≤ (~(witness.evalFormula env (Formula.atom 0 []))).val
    rw [witness_pred_zero]
    rw [Credence.neg_val, Credence.half_val]
    norm_num
  · -- atom 0 evaluates to 1/2
    rw [witness_pred_zero]

/-- The witness does NOT designate the unrelated atom `1`: it evaluates to `0`,
    which is below the threshold `1/2`. -/
theorem witness_not_designates_unrelated (env : witness.Assignment) :
    ¬ Credence.half ≤ witness.evalFormula env (Formula.atom 1 []) := by
  rw [witness_pred_one, Credence.le_def]
  rw [Credence.half_val, Credence.zero_val]
  norm_num

/-- No explosion: the locally inconsistent branch does NOT threshold-entail the
    unrelated atom `1`.  The witness structure designates every formula of the
    branch at the threshold `1/2` while leaving `atom 1` undesignated, so the
    `ThresholdConsequence` cannot hold. -/
theorem theory_branch_no_explosion :
    ¬ Structure.ThresholdConsequence.{0, 0, 0} Credence.half
        inconsistentBranch.formulas (Formula.atom 1 []) := by
  intro h
  have hwit := witness_designates_branch (fun _ => ())
  have hconcl := h witness (fun _ => ()) hwit
  exact witness_not_designates_unrelated (fun _ => ()) hconcl

end Cred.ProofTheory
