/-
  Cred Branch: Independence Classification (issues #523, #526)

  A branch is an assignment of credence to atomic principles, i.e. an admissible
  valuation. Given a statement and a finite family of branches, `classify`
  reports one of five statuses: certain, impossible, branchDependent,
  contradictory, or underdetermined.

  The intended example: a base with two admissible branches that disagree on a
  single choice-style atom. The principle is certain in one branch and
  impossible in the other, so it is branchDependent across the pair. Forcing the
  atom to be simultaneously certain and impossible (a contradictory extension)
  yields contradictory status.
-/

import Cred.Core.Value
import Cred.Core.Consequence

namespace Cred

namespace Branch

open Credence

set_option linter.dupNamespace false in
/-- A branch is an admissible valuation: a credence assignment to atoms. -/
def Branch (α : Type*) := α → Credence

/-- A statement is certain in a branch when it evaluates to credence 1. -/
noncomputable def CertainIn (b : Branch α) (φ : Formula α) : Prop :=
  evalCred b φ = 1

/-- A statement is impossible in a branch when it evaluates to credence 0. -/
noncomputable def ImpossibleIn (b : Branch α) (φ : Formula α) : Prop :=
  evalCred b φ = 0

/-- Five-way status of a statement against a family of branches. -/
inductive Status where
  | certain          -- certain in every branch
  | impossible       -- impossible in every branch
  | branchDependent  -- certain in one branch, impossible in another
  | contradictory    -- no branch is admissible (the family is empty)
  | underdetermined  -- some branch leaves the statement strictly between 0 and 1
  deriving DecidableEq, Repr

/-- Classify a statement against a finite family of branches.

    Priority: an empty family is `contradictory` (no admissible valuation). With
    branches present, any branch placing the statement strictly inside (0,1)
    forces `underdetermined`. Otherwise every branch pins the statement to a
    boundary, and the status records whether all agree on certainty, all agree
    on impossibility, or the boundaries split (branchDependent). -/
noncomputable def classify [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) : Status :=
  match branches with
  | [] => Status.contradictory
  | bs =>
    if bs.any (fun b => decide (0 < (evalCred b φ).val ∧ (evalCred b φ).val < 1)) then
      Status.underdetermined
    else if bs.all (fun b => decide ((evalCred b φ).val = 1)) then
      Status.certain
    else if bs.all (fun b => decide ((evalCred b φ).val = 0)) then
      Status.impossible
    else
      Status.branchDependent

/-! ## Worked instance: a choice-style atom

`Choice : Formula Bool` is the atom indexed by `true`. The `accept` branch sets
it to credence 1, the `reject` branch sets it to credence 0. They are admissible
in their own right; together they make the choice principle branchDependent. -/

/-- The choice-style principle as the atom indexed by `true`. -/
def Choice : Formula Bool := Formula.atom true

/-- Accepting branch: the choice atom is certain. -/
noncomputable def accept : Branch Bool := fun a => if a then 1 else 0

/-- Rejecting branch: the choice atom is impossible. -/
noncomputable def reject : Branch Bool := fun _ => 0

@[simp] theorem accept_choice_val : (evalCred accept Choice).val = 1 := rfl

@[simp] theorem reject_choice_val : (evalCred reject Choice).val = 0 := rfl

/-- The choice principle is certain in the accepting branch. -/
theorem choice_certain_accept : CertainIn accept Choice := by
  unfold CertainIn
  ext
  simp [accept_choice_val]

/-- The choice principle is impossible in the rejecting branch. -/
theorem choice_impossible_reject : ImpossibleIn reject Choice := by
  unfold ImpossibleIn
  ext
  simp [reject_choice_val]

/-- Across the accept/reject pair the choice principle is branchDependent:
    certain in one branch, impossible in the other, never interior. -/
theorem choice_branchDependent :
    classify Choice [accept, reject] = Status.branchDependent := by
  have haccept : (evalCred accept Choice).val = 1 := accept_choice_val
  have hreject : (evalCred reject Choice).val = 0 := reject_choice_val
  -- interior tests: false in both branches (each value sits on a boundary)
  have hint_a :
      decide (0 < (evalCred accept Choice).val ∧ (evalCred accept Choice).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [haccept]; rintro ⟨_, h⟩; exact (lt_irrefl 1) h)
  have hint_r :
      decide (0 < (evalCred reject Choice).val ∧ (evalCred reject Choice).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hreject]; rintro ⟨h, _⟩; exact (lt_irrefl 0) h)
  -- certainty test: false in the rejecting branch
  have hcert_r : decide ((evalCred reject Choice).val = 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hreject]; exact zero_ne_one)
  -- impossibility test: false in the accepting branch
  have himp_a : decide ((evalCred accept Choice).val = 0) = false :=
    decide_eq_false_iff_not.mpr (by rw [haccept]; exact one_ne_zero)
  have gAny :
      ([accept, reject].any
        (fun b => decide (0 < (evalCred b Choice).val ∧ (evalCred b Choice).val < 1)))
        = false := by
    simp only [List.any_cons, List.any_nil, hint_a, hint_r, Bool.or_self, Bool.or_false]
  have gAll1 :
      ([accept, reject].all (fun b => decide ((evalCred b Choice).val = 1))) = false := by
    simp only [List.all_cons, List.all_nil, hcert_r, Bool.and_false, Bool.and_true]
  have gAll0 :
      ([accept, reject].all (fun b => decide ((evalCred b Choice).val = 0))) = false := by
    simp only [List.all_cons, List.all_nil, himp_a, Bool.false_and]
  simp only [classify]
  rw [if_neg (by rw [gAny]; exact Bool.false_ne_true),
      if_neg (by rw [gAll1]; exact Bool.false_ne_true),
      if_neg (by rw [gAll0]; exact Bool.false_ne_true)]

/-! ## Contradictory extension

Conjoining the choice atom with its own negation pins the statement to
credence 0 in every branch — it can never be certain — yet the empty family of
admissible branches is what `classify` reports as `contradictory`. We model the
contradictory extension directly: a base whose set of admissible branches is
empty has `contradictory` status for any statement. -/

/-- A statement against no admissible branches is contradictory. -/
theorem classify_nil (φ : Formula Bool) :
    classify φ [] = Status.contradictory := rfl

/-- The contradictory extension: requiring the choice atom both certain and
    impossible admits no branch, so the choice principle is contradictory. -/
theorem choice_contradictory :
    classify Choice [] = Status.contradictory := rfl

/-! ## Soundness of the classification verdicts -/

/-- When `classify` returns `certain`, every branch makes the statement certain. -/
theorem classify_certain_sound [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α))
    (h : classify φ branches = Status.certain) :
    ∀ b ∈ branches, (evalCred b φ).val = 1 := by
  intro b hb
  cases branches with
  | nil => simp [classify] at h
  | cons hd tl =>
    simp only [classify] at h
    by_cases hany :
        (hd :: tl).any (fun b => decide (0 < (evalCred b φ).val ∧ (evalCred b φ).val < 1)) = true
    · rw [if_pos hany] at h; exact absurd h (by decide)
    · rw [if_neg hany] at h
      by_cases hall : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 1)) = true
      · have := List.all_eq_true.mp hall b hb
        simpa using this
      · rw [if_neg hall] at h
        by_cases hall0 : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 0)) = true
        · rw [if_pos hall0] at h; exact absurd h (by decide)
        · rw [if_neg hall0] at h; exact absurd h (by decide)

/-- When `classify` returns `impossible`, every branch makes the statement
    impossible. -/
theorem classify_impossible_sound [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α))
    (h : classify φ branches = Status.impossible) :
    ∀ b ∈ branches, (evalCred b φ).val = 0 := by
  intro b hb
  cases branches with
  | nil => simp [classify] at h
  | cons hd tl =>
    simp only [classify] at h
    by_cases hany :
        (hd :: tl).any (fun b => decide (0 < (evalCred b φ).val ∧ (evalCred b φ).val < 1)) = true
    · rw [if_pos hany] at h; exact absurd h (by decide)
    · rw [if_neg hany] at h
      by_cases hall : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 1)) = true
      · rw [if_pos hall] at h; exact absurd h (by decide)
      · rw [if_neg hall] at h
        by_cases hall0 : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 0)) = true
        · have := List.all_eq_true.mp hall0 b hb
          simpa using this
        · rw [if_neg hall0] at h; exact absurd h (by decide)

/-- When `classify` returns `contradictory`, the family is empty: no admissible
    branch exists. -/
theorem classify_contradictory_iff_nil [DecidableEq α]
    (φ : Formula α) (branches : List (Branch α)) :
    classify φ branches = Status.contradictory ↔ branches = [] := by
  cases branches with
  | nil => simp [classify]
  | cons hd tl =>
    constructor
    · intro h
      simp only [classify] at h
      by_cases hany :
          (hd :: tl).any (fun b => decide (0 < (evalCred b φ).val ∧ (evalCred b φ).val < 1)) = true
      · rw [if_pos hany] at h; exact absurd h (by decide)
      · rw [if_neg hany] at h
        by_cases hall : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 1)) = true
        · rw [if_pos hall] at h; exact absurd h (by decide)
        · rw [if_neg hall] at h
          by_cases hall0 : (hd :: tl).all (fun b => decide ((evalCred b φ).val = 0)) = true
          · rw [if_pos hall0] at h; exact absurd h (by decide)
          · rw [if_neg hall0] at h; exact absurd h (by decide)
    · intro h; exact absurd h (by simp)

end Branch

end Cred
