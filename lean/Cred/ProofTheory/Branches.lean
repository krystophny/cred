/-
  Cred ProofTheory: Hypothetical Branches (issues #634(4), #641)

  A branch is a hypothetical context of labelled assumptions together with the
  nodes derivable from it under the generative calculus.  A branch is locally
  contradictory when it holds both `A` and `neg A`.  The central guarantee
  mirrors `labelled_no_ex_falso` of `Cred.Sequent`: the generative rules carry
  NO explosion rule, so a locally contradictory branch does NOT derive an
  unrelated atom.  The witness is a valuation that designates the contradiction
  while leaving the unrelated atom undesignated.
-/

import Cred.ProofTheory.Generative

namespace Cred.ProofTheory

open Cred

/-- A hypothetical branch: a list of labelled assumptions. -/
structure Branch (α : Type*) where
  assumptions : List (LForm α)

namespace Branch

variable {α : Type*}

/-- A node is derived in a branch when it is derivable at the given label from
    the branch assumptions. -/
def Derived (β : Branch α) (k : Label) (φ : Formula α) : Prop :=
  Derives β.assumptions k φ

end Branch

/-- A labelled context is locally contradictory at a label `k` when it contains
    both `A` and `neg A`, each demanded at `k`. -/
def LocallyContradictory (Γ : List (LForm α)) (k : Label) : Prop :=
  ∃ A : Formula α, (⟨k, A⟩ : LForm α) ∈ Γ ∧ (⟨k, .neg A⟩ : LForm α) ∈ Γ

/-! ## No explosion from a locally contradictory branch -/

/-- A concrete contradictory branch over `Fin 2`: the atom `0` and its negation
    are both demanded positive. -/
def contradictoryBranch : Branch (Fin 2) where
  assumptions :=
    [ ⟨.positive, .atom 0⟩, ⟨.positive, .neg (.atom 0)⟩ ]

/-- The branch is indeed locally contradictory at the positive label. -/
theorem contradictoryBranch_locallyContradictory :
    LocallyContradictory contradictoryBranch.assumptions .positive := by
  refine ⟨.atom 0, ?_, ?_⟩ <;>
    simp [contradictoryBranch]

/-- The half/zero countermodel: atom `0` gets `1/2`, atom `1` gets `0`. -/
noncomputable def halfZero : Fin 2 → Credence :=
  fun i => if i = 0 then Credence.half else 0

@[simp] theorem halfZero_zero : halfZero 0 = Credence.half :=
  if_pos rfl

@[simp] theorem halfZero_one : halfZero 1 = 0 :=
  if_neg (by decide : ¬ (1 : Fin 2) = 0)

/-- The countermodel designates the whole contradictory branch: both `A` and
    `neg A` evaluate to `1/2`, which is positive. -/
theorem halfZero_designates_contradictory :
    Designated halfZero contradictoryBranch.assumptions := by
  intro b hb
  simp only [contradictoryBranch, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · show (0 : ℝ) < (eval halfZero (.atom 0)).val
    simp only [eval, halfZero_zero, Credence.half_val]
    norm_num
  · show (0 : ℝ) < (eval halfZero (.neg (.atom 0))).val
    simp only [eval, halfZero_zero, Credence.neg_val, Credence.half_val]
    norm_num

/-- The countermodel does NOT designate the unrelated atom `1`: it evaluates to
    `0`, which is not positive. -/
theorem halfZero_not_designates_unrelated :
    ¬ Label.designates .positive (eval halfZero (.atom 1)) := by
  show ¬ (0 : ℝ) < (eval halfZero (.atom 1)).val
  simp only [eval, halfZero_one, Credence.zero_val]
  norm_num

/-- No explosion: the locally contradictory branch does not derive the
    unrelated atom `1` at the positive label.  The generative calculus has no
    explosion rule, so soundness against the half/zero countermodel forbids the
    derivation. -/
theorem local_contradiction_no_explosion :
    ¬ contradictoryBranch.Derived .positive (.atom 1) := by
  intro h
  have hs := generative_sound h halfZero halfZero_designates_contradictory
  exact halfZero_not_designates_unrelated hs

end Cred.ProofTheory
