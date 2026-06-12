/-
  Cred Math: Robustness Audit (issue #599)

  Using the branch classifier to audit how robust a theorem is under varying
  assumptions. A claim is a `Formula α`; a family of admissible branches is a
  `List (Branch α)`. The classifier `Branch.classify` already reports a five-way
  status; here we read three of those verdicts as a robustness audit:

  - ROBUST: certain in every admissible branch (`Status.certain`). The claim is
    a theorem no matter which admissible assumption set is realized.
  - BRANCH-DEPENDENT: certain in some branch, impossible in another
    (`Status.branchDependent`). The claim is an axiom relative to the family —
    its truth depends on which branch is chosen.
  - INADMISSIBLE: no admissible branch (`Status.contradictory`, the empty
    family). Adding an inconsistent assumption removes every branch, and no
    claim is supported.

  Classical mathematics embeds as the crisp fragment: excluded middle is robust
  across any family of crisp branches (the value-algebra audit), reusing
  `crisp_excluded_middle_formula` from the crisp bridge. The branch-dependent
  and inadmissible cases reuse the `Choice` worked example and `classify_nil`.
-/

import Cred.Branch.Independence
import Cred.Bridge.Crisp

namespace Cred

namespace Branch

open Credence

variable {α : Type*}

/-! ## Robustness predicates

Each predicate is a thin reading of one `classify` verdict. We keep `classify`
as the single source of truth so the soundness theorems already proven in
`Branch/Independence.lean` carry over directly. -/

/-- A claim is ROBUST across a branch family when it is certain in every branch. -/
noncomputable def Robust [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) : Prop :=
  classify φ branches = Status.certain

/-- A claim is BRANCH-DEPENDENT when the family splits it across the {0,1}
    boundaries: certain in one branch, impossible in another. -/
noncomputable def BranchDependent [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) : Prop :=
  classify φ branches = Status.branchDependent

/-- A claim is INADMISSIBLE when no branch is admissible (the empty family). -/
noncomputable def Inadmissible [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) : Prop :=
  classify φ branches = Status.contradictory

/-! ## Robust = certain in every branch

The two directions tie `Robust` to the underlying per-branch certainty. The
forward direction is exactly `classify_certain_sound`; the converse needs a
nonempty family (the empty family is `contradictory`, not `certain`). -/

/-- A robust claim is certain in every branch (audit soundness). Reuses
    `classify_certain_sound`. -/
theorem robust_certain_every_branch [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α))
    (h : Robust φ branches) :
    ∀ b ∈ branches, (evalCred b φ).val = 1 :=
  classify_certain_sound φ branches h

/-- A claim certain in every branch of a nonempty family is robust. The
    converse of `robust_certain_every_branch`; together they characterize
    robustness as branchwise certainty over a nonempty family. -/
theorem robust_of_all_one [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) (hne : branches ≠ [])
    (h : ∀ b ∈ branches, (evalCred b φ).val = 1) :
    Robust φ branches := by
  cases branches with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    -- no branch is interior (every value is exactly 1)
    have hany :
        (hd :: tl).any
          (fun b => decide (0 < (evalCred b φ).val ∧ (evalCred b φ).val < 1)) = false := by
      rw [List.any_eq_false]
      intro b hb
      simp only [decide_eq_true_eq, h b hb, lt_self_iff_false, and_false, not_false_eq_true]
    -- every value equals 1
    have hall :
        (hd :: tl).all (fun b => decide ((evalCred b φ).val = 1)) = true := by
      rw [List.all_eq_true]
      intro b hb
      simp only [decide_eq_true_eq]
      exact h b hb
    unfold Robust
    simp only [classify]
    rw [if_neg (by rw [hany]; exact Bool.false_ne_true), if_pos hall]

/-! ## Worked audit: the crisp value-algebra fragment is robust

Classical mathematics embeds as the crisp fragment. We audit excluded middle
`φ ⊔ ~φ` over an arbitrary family of crisp branches: it is robust, certain in
every branch, by the value-algebra fact `crisp_excluded_middle_formula`. This
is the concrete connection to the value algebra: the robustness verdict is read
off `Credence.certainty_eq_one_iff` through the crisp bridge. -/

/-- A branch is crisp when it assigns only the boundary values 0 and 1. -/
def CrispBranch (b : Branch α) : Prop := ∀ a, b a = 0 ∨ b a = 1

/-- Excluded middle is certain in every crisp branch (value-algebra audit step).
    Direct reuse of `crisp_excluded_middle_formula`. -/
theorem excluded_middle_certain_crisp
    (b : Branch α) (hb : CrispBranch b) (φ : Formula α) :
    (evalCred b (Formula.disj φ (Formula.neg φ))).val = 1 := by
  rw [crisp_excluded_middle_formula b hb φ]; rfl

/-- Robustness audit: excluded middle is robust across any nonempty family of
    crisp branches. The classical tautology survives every admissible
    assumption set in the crisp fragment. -/
theorem excluded_middle_robust [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) (hne : branches ≠ [])
    (hcrisp : ∀ b ∈ branches, CrispBranch b) :
    Robust (Formula.disj φ (Formula.neg φ)) branches :=
  robust_of_all_one _ branches hne
    (fun b hb => excluded_middle_certain_crisp b (hcrisp b hb) φ)

/-! ## Worked audit: an axiom-style atom is branch-dependent

The `Choice` atom from `Branch/Independence.lean` is the canonical axiom: certain
in the `accept` branch, impossible in the `reject` branch. Across that pair the
audit returns BRANCH-DEPENDENT. -/

/-- The choice atom is a genuine `BranchDependent` claim across accept/reject:
    its truth is an assumption, not a theorem. Reuses `choice_branchDependent`. -/
theorem choice_audit_branch_dependent :
    BranchDependent Choice [accept, reject] :=
  choice_branchDependent

/-- A branch-dependent claim is not robust: the accept/reject audit shows the
    choice atom fails the robustness test. -/
theorem choice_not_robust :
    ¬ Robust Choice [accept, reject] := by
  unfold Robust
  rw [choice_branchDependent]
  exact fun h => Status.noConfusion h

/-! ## Worked audit: an inconsistent assumption is inadmissible

Adding an inconsistent assumption (one with no admissible branch) collapses the
family to the empty list, and the audit returns INADMISSIBLE for every claim —
no theorem is supported by contradictory assumptions. This is the contradictory
case of the value-algebra audit: requiring an atom both certain and impossible
admits no branch. -/

/-- The inconsistent (empty) family makes every claim inadmissible. The empty
    branch list is the first `classify` case, so this is definitional. -/
theorem inconsistent_inadmissible (φ : Formula α) [DecidableEq α] :
    Inadmissible φ ([] : List (Branch α)) := rfl

/-- An inadmissible claim is not robust: contradictory assumptions support no
    theorem. -/
theorem inadmissible_not_robust (φ : Formula α) [DecidableEq α] :
    ¬ Robust φ ([] : List (Branch α)) := fun h => Status.noConfusion h

/-- An inadmissible audit verdict means the branch family is empty: the
    assumptions admit no valuation. Restatement of
    `classify_contradictory_iff_nil`. -/
theorem inadmissible_iff_nil [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) :
    Inadmissible φ branches ↔ branches = [] :=
  classify_contradictory_iff_nil φ branches

/-! ## Trichotomy of the audit

The three audit verdicts are mutually exclusive: a claim is at most one of
robust, branch-dependent, inadmissible. This is immediate from `Status` being
a (decidable) enumeration, but recording it makes the audit's exhaustiveness
explicit. -/

/-- Robust, branch-dependent, and inadmissible are pairwise exclusive verdicts. -/
theorem audit_verdicts_exclusive [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) :
    (Robust φ branches → ¬ BranchDependent φ branches) ∧
    (Robust φ branches → ¬ Inadmissible φ branches) ∧
    (BranchDependent φ branches → ¬ Inadmissible φ branches) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro hx hy
      simp only [Robust, BranchDependent, Inadmissible] at hx hy
      rw [hx] at hy
      exact Status.noConfusion hy

end Branch

end Cred
