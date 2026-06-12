/-
  Cred Math: Naturals (v1)

  Classical arithmetic facts hold at CERTAINTY (credence 1) in the crisp
  fragment.  The mechanism is `crispScore`: a decidable predicate over ℕ
  lifts to a 0/1 Credence, and the score is 1 exactly when the predicate
  holds.  Classical arithmetic then enters as the proof that the predicate
  *does* hold, giving score 1 by `crispScore_one_iff`.

  Cred adds STATUS on top:
  - Crisp arithmetic facts are certain (score 1 always).
  - A Nat claim that varies across branches — here, `n < m` for an unknown
    pair (n, m) — is classified as `branchDependent` by `Branch.classify`.

  We reuse mathlib `Nat` for all arithmetic and `Branch.Independence` for
  the status layer; no non-trivial content is reinvented.
-/

import Cred.Approx.Structure
import Cred.Branch.Independence

namespace Cred

namespace Math.Nat

open Credence Approx Branch

/-! ## (a) Crisp fragment: arithmetic at certainty

`natEqScore a b` is the credence of the proposition `a = b` where `a b : ℕ`.
It is 1 when the equation holds, 0 otherwise. -/

/-- Crisp score for Nat equality: 1 iff `a = b`. -/
def natEqScore (a b : ℕ) : Credence := crispScore (fun p : ℕ × ℕ => p.1 = p.2) (a, b)

@[simp] theorem natEqScore_one_iff (a b : ℕ) : natEqScore a b = 1 ↔ a = b :=
  crispScore_one_iff _ _

/-- `natLeScore a b` is the credence of `a ≤ b`. -/
def natLeScore (a b : ℕ) : Credence := crispScore (fun p : ℕ × ℕ => p.1 ≤ p.2) (a, b)

@[simp] theorem natLeScore_one_iff (a b : ℕ) : natLeScore a b = 1 ↔ a ≤ b :=
  crispScore_one_iff _ _

/-! ### Classical facts as certainty-1 results -/

/-- `0 + n = n` holds at certainty: the equality score is 1. -/
theorem add_zero_left_certain (n : ℕ) : natEqScore (0 + n) n = 1 :=
  (natEqScore_one_iff _ _).mpr (Nat.zero_add n)

/-- `n + 0 = n` holds at certainty. -/
theorem add_zero_right_certain (n : ℕ) : natEqScore (n + 0) n = 1 :=
  (natEqScore_one_iff _ _).mpr (Nat.add_zero n)

/-- Succ is injective: the equality score of `n` and `m` is 1 when their
    successors are equal. -/
theorem succ_inj_certain (n m : ℕ) (h : n.succ = m.succ) : natEqScore n m = 1 :=
  (natEqScore_one_iff _ _).mpr (Nat.succ.inj h)

/-- Concrete inequality: `3 < 7` holds at certainty. -/
theorem three_lt_seven_certain : natLeScore 3 7 = 1 :=
  (natLeScore_one_iff _ _).mpr (by norm_num)

/-- `ExactPreserves` of the equality structure at a true Nat equation. -/
theorem exactPreserves_natEq (n : ℕ) :
    ExactPreserves (fun p : ℕ × ℕ => natEqScore p.1 p.2) (n, n) := by
  simp [ExactPreserves, StructureDegree, natEqScore]

/-! ## (b) STATUS layer: branch-dependent Nat claim

`IsSmaller : Formula Bool` is the atom indexed by `true`; two branches
disagree on whether it holds (i.e., whether some `n < m`).  The `accept`
branch assigns credence 1 (the claim holds); the `reject` branch assigns
credence 0 (it does not).  `Branch.classify` then returns `branchDependent`.

This is the minimal demonstration that a Nat-flavoured claim — one whose
truth depends on which natural numbers one is talking about — carries Cred
status `branchDependent` rather than being globally certain. -/

/-- The atomic claim "n is strictly less than m" for some contextual pair. -/
def IsSmaller : Formula Bool := Formula.atom true

/-- Branch where the claim holds (e.g., n = 1, m = 2). -/
noncomputable def acceptSmaller : Branch.Branch Bool := fun a => if a then 1 else 0

/-- Branch where the claim fails (e.g., n = 5, m = 2). -/
noncomputable def rejectSmaller : Branch.Branch Bool := fun _ => 0

@[simp] theorem acceptSmaller_val : (evalCred acceptSmaller IsSmaller).val = 1 := rfl

@[simp] theorem rejectSmaller_val : (evalCred rejectSmaller IsSmaller).val = 0 := rfl

/-- A Nat-ordering claim is branch-dependent: certain in one branch,
    impossible in another. -/
theorem isSmaller_branchDependent :
    Branch.classify IsSmaller [acceptSmaller, rejectSmaller] = Branch.Status.branchDependent := by
  have haccept : (evalCred acceptSmaller IsSmaller).val = 1 := acceptSmaller_val
  have hreject : (evalCred rejectSmaller IsSmaller).val = 0 := rejectSmaller_val
  -- neither branch places the claim strictly inside (0,1)
  have hint_a :
      decide (0 < (evalCred acceptSmaller IsSmaller).val ∧
              (evalCred acceptSmaller IsSmaller).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [haccept]; rintro ⟨_, h⟩; exact lt_irrefl 1 h)
  have hint_r :
      decide (0 < (evalCred rejectSmaller IsSmaller).val ∧
              (evalCred rejectSmaller IsSmaller).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hreject]; rintro ⟨h, _⟩; exact lt_irrefl 0 h)
  -- not certain in every branch (fails in rejectSmaller)
  have hcert_r : decide ((evalCred rejectSmaller IsSmaller).val = 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hreject]; exact zero_ne_one)
  -- not impossible in every branch (fails in acceptSmaller)
  have himp_a : decide ((evalCred acceptSmaller IsSmaller).val = 0) = false :=
    decide_eq_false_iff_not.mpr (by rw [haccept]; exact one_ne_zero)
  simp only [Branch.classify]
  rw [if_neg (by
        simp only [List.any_cons, List.any_nil, hint_a, hint_r,
          Bool.or_self, Bool.or_false]
        exact Bool.false_ne_true),
      if_neg (by
        simp only [List.all_cons, List.all_nil, hcert_r,
          Bool.and_false, Bool.and_true]
        exact Bool.false_ne_true),
      if_neg (by
        simp only [List.all_cons, List.all_nil, himp_a,
          Bool.false_and]
        exact Bool.false_ne_true)]

end Math.Nat

end Cred
