/-
  Cred Math: Reals inside Cred (issue #594)

  First theorem package for ordinary real analysis inside the Cred framework.
  The semantics are the hosted mathlib `ℝ` (the hybrid choice): classical real
  facts are reused verbatim, never reinvented, and the Cred layer sits on top as
  a status. A crisp real claim is lifted to a 0/1 credence by `realScore`
  (`Approx.crispScore` of a decidable real predicate), so a true claim is
  certain (score 1) and a false one impossible (score 0).

  This is the "classical math embeds as the crisp fragment" principle for the
  reals: order reflexivity, the additive and multiplicative identities, and a
  simple inequality are all degree-1 / certain on crisp data. The closing
  section adds the genuinely Cred-only structure: the same real predicate becomes
  branch-dependent across two branches that disagree on the witness, and a
  threshold-qualified consequence over a real-derived atom.

  Boundary note: the credence value algebra itself is real-free on the rationals
  (`Cred.RatUnit` in `Algebra/Rational.lean`) and completed to the hosted unit
  interval (`Algebra/Completion.lean`). This module is on the far side of that
  boundary: it studies the hosted reals as data scored by the algebra, not the
  construction of the algebra of values.
-/

import Cred.Approx.Structure
import Cred.Branch.Independence
import Cred.Threshold

namespace Cred

namespace Math

open Credence Approx

/-! ## Real claims as crisp scores

A decidable real predicate is lifted to a 0/1 credence by `crispScore`. The score
is certainty exactly when the predicate holds, so a true classical real fact is
certain and a false one impossible. Real predicates are equalities and order
facts, so their decidability is classical (noncomputable). -/

/-- A real predicate lifted to a 0/1 credence: certain when it holds. -/
noncomputable def realScore (P : ℝ → Prop) [DecidablePred P] : ℝ → Credence :=
  crispScore P

theorem realScore_one_iff (P : ℝ → Prop) [DecidablePred P] (x : ℝ) :
    realScore P x = 1 ↔ P x :=
  crispScore_one_iff P x

theorem realScore_zero_iff (P : ℝ → Prop) [DecidablePred P] (x : ℝ) :
    realScore P x = 0 ↔ ¬ P x :=
  crispScore_zero_iff P x

/-- A true real claim is certain: if `P x` holds, its score is credence 1. -/
theorem realScore_certain_of (P : ℝ → Prop) [DecidablePred P] {x : ℝ} (h : P x) :
    realScore P x = 1 :=
  (realScore_one_iff P x).mpr h

/-! ## Crisp real facts at certainty

Each fact is a classical mathlib theorem on the hosted reals; reusing it, the
corresponding `realScore` is certainty. The predicates are stated pointwise so the
classical decidability instance is local. -/

-- Order reflexivity, the additive identity, the multiplicative identity, and a
-- simple inequality, each scored crisply; their predicates decide classically.
noncomputable instance instDecLe : DecidablePred (fun x : ℝ => x ≤ x) :=
  fun _ => Classical.dec _
noncomputable instance instDecAddZero :
    DecidablePred (fun x : ℝ => x + 0 = x) := fun _ => Classical.dec _
noncomputable instance instDecMulOne :
    DecidablePred (fun x : ℝ => x * 1 = x) := fun _ => Classical.dec _
noncomputable instance instDecSqNonneg :
    DecidablePred (fun x : ℝ => 0 ≤ x ^ 2) := fun _ => Classical.dec _

/-- Order reflexivity is certain: `a ≤ a` scores 1 for every real `a`. -/
theorem le_refl_certain (a : ℝ) :
    realScore (fun x : ℝ => x ≤ x) a = 1 :=
  realScore_certain_of _ (le_refl a)

/-- The additive identity is certain: `a + 0 = a` scores 1 for every real `a`. -/
theorem add_zero_certain (a : ℝ) :
    realScore (fun x : ℝ => x + 0 = x) a = 1 :=
  realScore_certain_of _ (add_zero a)

/-- The multiplicative identity is certain: `a * 1 = a` scores 1 for every real `a`. -/
theorem mul_one_certain (a : ℝ) :
    realScore (fun x : ℝ => x * 1 = x) a = 1 :=
  realScore_certain_of _ (mul_one a)

/-- A simple inequality is certain: `0 ≤ a^2` scores 1 for every real `a`. -/
theorem sq_nonneg_certain (a : ℝ) :
    realScore (fun x : ℝ => 0 ≤ x ^ 2) a = 1 :=
  realScore_certain_of _ (sq_nonneg a)

/-! ## Status example: a real claim that is not certain

Certainty is the crisp fragment. The Cred layer adds status. The real predicate
`0 ≤ x` is true at `x = 1` and false at `x = -1`, so the atom it scores is
certain in one branch and impossible in the other: branch-dependent, not
certain. A threshold-qualified consequence over the same real-derived atom
closes the package. -/

noncomputable instance instDecNonneg :
    DecidablePred (fun x : ℝ => (0 : ℝ) ≤ x) := fun _ => Classical.dec _

/-- The atom whose credence is the score of `0 ≤ x`. -/
def nonnegAtom : Formula Unit := Formula.atom ()

/-- Branch evaluating the nonneg atom at `x = 1`, where `0 ≤ x` holds. -/
noncomputable def posBranch : Branch.Branch Unit :=
  fun _ => realScore (fun x : ℝ => (0 : ℝ) ≤ x) 1

/-- Branch evaluating the nonneg atom at `x = -1`, where `0 ≤ x` fails. -/
noncomputable def negBranch : Branch.Branch Unit :=
  fun _ => realScore (fun x : ℝ => (0 : ℝ) ≤ x) (-1)

theorem posBranch_val : (evalCred posBranch nonnegAtom).val = 1 := by
  have h : realScore (fun x : ℝ => (0 : ℝ) ≤ x) 1 = 1 :=
    realScore_certain_of _ (by norm_num)
  show (realScore (fun x : ℝ => (0 : ℝ) ≤ x) 1).val = 1
  rw [h]; rfl

theorem negBranch_val : (evalCred negBranch nonnegAtom).val = 0 := by
  have h : realScore (fun x : ℝ => (0 : ℝ) ≤ x) (-1) = 0 :=
    (realScore_zero_iff _ _).mpr (by norm_num)
  show (realScore (fun x : ℝ => (0 : ℝ) ≤ x) (-1)).val = 0
  rw [h]; rfl

/-- Status example: the real claim `0 ≤ x`, scored as an atom, is
    branch-dependent across the `x = 1` and `x = -1` branches: certain in one,
    impossible in the other, never interior. This is the Cred status that
    classical certainty cannot express. -/
theorem nonneg_branchDependent :
    Branch.classify nonnegAtom [posBranch, negBranch] = Branch.Status.branchDependent := by
  have hp : (evalCred posBranch nonnegAtom).val = 1 := posBranch_val
  have hn : (evalCred negBranch nonnegAtom).val = 0 := negBranch_val
  have hint_p :
      decide (0 < (evalCred posBranch nonnegAtom).val ∧
        (evalCred posBranch nonnegAtom).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hp]; rintro ⟨_, h⟩; exact (lt_irrefl 1) h)
  have hint_n :
      decide (0 < (evalCred negBranch nonnegAtom).val ∧
        (evalCred negBranch nonnegAtom).val < 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hn]; rintro ⟨h, _⟩; exact (lt_irrefl 0) h)
  have hcert_n : decide ((evalCred negBranch nonnegAtom).val = 1) = false :=
    decide_eq_false_iff_not.mpr (by rw [hn]; exact zero_ne_one)
  have himp_p : decide ((evalCred posBranch nonnegAtom).val = 0) = false :=
    decide_eq_false_iff_not.mpr (by rw [hp]; exact one_ne_zero)
  have gAny :
      ([posBranch, negBranch].any
        (fun b => decide (0 < (evalCred b nonnegAtom).val ∧
          (evalCred b nonnegAtom).val < 1))) = false := by
    simp only [List.any_cons, List.any_nil, hint_p, hint_n, Bool.or_self, Bool.or_false]
  have gAll1 :
      ([posBranch, negBranch].all
        (fun b => decide ((evalCred b nonnegAtom).val = 1))) = false := by
    simp only [List.all_cons, List.all_nil, hcert_n, Bool.and_false, Bool.and_true]
  have gAll0 :
      ([posBranch, negBranch].all
        (fun b => decide ((evalCred b nonnegAtom).val = 0))) = false := by
    simp only [List.all_cons, List.all_nil, himp_p, Bool.false_and]
  simp only [Branch.classify]
  rw [if_neg (by rw [gAny]; exact Bool.false_ne_true),
      if_neg (by rw [gAll1]; exact Bool.false_ne_true),
      if_neg (by rw [gAll0]; exact Bool.false_ne_true)]

/-- Threshold-qualified status over the same real-derived atom: at threshold
    `1/2`, the nonneg atom is its own consequence. A real claim that is only
    threshold-qualified (not certain) still licenses reflexive inference at its
    floor, which is the graded layer above the crisp fragment. -/
theorem nonneg_threshold_reflexivity :
    thresholdConsequence ⟨1 / 2, by norm_num, by norm_num⟩ Unit [nonnegAtom] nonnegAtom :=
  threshold_reflexivity _ nonnegAtom

end Math

end Cred
