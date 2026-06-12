/-
  Cred Foundation Arithmetic

  A genuine standard model of arithmetic as a `Structure`.  The domain is `Nat`
  with `0`, successor, addition, and multiplication interpreted by `func`, crisp
  equality, and quantifiers given by the real infimum/supremum of credences over
  the whole domain (`credInf`/`credSup`), not a witness-only collapse.

  The seven Robinson Q axioms are closed `Formula`s.  Each is shown to evaluate
  to certainty `1` in this model for every assignment, which for the universal
  axioms uses that the inf quantifier ranges over all of `Nat`.  From this,
  `arithQ_con` proves `bot` is not derivable from the Q axioms at certainty.
-/

import Cred.Foundation.Kernel
import Cred.Predicate

namespace Cred
namespace Foundation

open Credence

/-! ## Signature of arithmetic

`zero` (arity 0), `succ` (arity 1), `add`/`mul` (arity 2).  No atomic
predicates: equality is a `Formula` constructor, so `Pred := Empty`. -/

inductive ArithQFunc where
  | zero
  | succ
  | add
  | mul
deriving DecidableEq, Repr

abbrev ArithQPred := Empty
abbrev ArithQTerm := Term ArithQFunc
abbrev ArithQFormula := Formula ArithQFunc ArithQPred

namespace arithQ

/-! ## Object-language term builders -/

def zeroT : ArithQTerm := .app .zero []
def succT (t : ArithQTerm) : ArithQTerm := .app .succ [t]
def addT (s t : ArithQTerm) : ArithQTerm := .app .add [s, t]
def mulT (s t : ArithQTerm) : ArithQTerm := .app .mul [s, t]

/-- De Bruijn variable. -/
def v (n : Nat) : ArithQTerm := .var n

/-- Material implication encoded through De Morgan disjunction and negation,
    since the language has no implication constructor. -/
def impF (φ ψ : ArithQFormula) : ArithQFormula := .disj (.neg φ) ψ

/-! ## The standard model

`Nat` with genuine `0`/`S`/`+`/`*`, crisp equality, and inf/sup quantifiers
ranging over the whole domain. -/

noncomputable def natModel : Structure ArithQFunc ArithQPred where
  Domain := Nat
  witness := 0
  func
    | .zero, _ => 0
    | .succ, [n] => n + 1
    | .succ, _ => 0
    | .add, [a, b] => a + b
    | .add, _ => 0
    | .mul, [a, b] => a * b
    | .mul, _ => 0
  pred p _ := p.elim
  eq a b := if a = b then 1 else 0
  all f := GradedPredicate.credInf f
  ex f := GradedPredicate.credSup f

instance : Nonempty natModel.Domain := ⟨(0 : Nat)⟩

@[simp] theorem natModel_eq (a b : Nat) :
    natModel.eq a b = if a = b then 1 else 0 := rfl

@[simp] theorem natModel_eq_self (a : Nat) : natModel.eq a a = 1 := by
  simp [natModel_eq]

theorem natModel_eq_of_eq {a b : Nat} (h : a = b) : natModel.eq a b = 1 := by
  subst h; exact natModel_eq_self a

/-! ### Term evaluation on the builders -/

@[simp] theorem eval_zeroT (env : natModel.Assignment) :
    natModel.evalTerm env zeroT = (0 : Nat) := rfl

@[simp] theorem eval_v (env : natModel.Assignment) (n : Nat) :
    natModel.evalTerm env (v n) = env n := rfl

/-! ## Crisp equality and genuine inf/sup quantifier laws -/

theorem natModel_crispEquality : natModel.CrispEquality where
  eq_refl x := by simp [natModel_eq]
  eq_one_imp {x y} h := by
    by_cases hxy : x = y
    · exact hxy
    · rw [natModel_eq, if_neg hxy] at h
      have : (0 : ℝ) = 1 := by
        have := congrArg Credence.val h
        rwa [Credence.zero_val, Credence.one_val] at this
      norm_num at this
  eq_zero_of_ne {x y} h := by simp [natModel_eq, h]

/-- `all f = credInf f` is `1` exactly when every instance is `1`; here the
    quantifier ranges over all of `Nat`, so this is the genuine universal claim. -/
theorem natModel_all_eq_one {f : Nat → Credence} (h : ∀ n, f n = 1) :
    natModel.all f = 1 := by
  show GradedPredicate.credInf f = 1
  apply le_antisymm
  · exact (GradedPredicate.credInf f).le_one
  · have : (GradedPredicate.credInf f).val = 1 := by
      show iInf (fun n => (f n).val) = 1
      simp only [h, Credence.one_val]
      exact ciInf_const
    exact le_of_eq (Credence.ext this.symm)

theorem natModel_quantifierLaws : natModel.QuantifierLaws where
  all_le_instance f x := by
    show (GradedPredicate.credInf f).val ≤ (f x).val
    exact GradedPredicate.forall_le f x
  instance_le_ex f x := by
    show (f x).val ≤ (GradedPredicate.credSup f).val
    exact GradedPredicate.le_exists f x
  all_one := by
    show GradedPredicate.credInf (fun _ : Nat => (1 : Credence)) = 1
    exact natModel_all_eq_one (fun _ => rfl)
  ex_zero := by
    show GradedPredicate.credSup (fun _ : Nat => (0 : Credence)) = 0
    apply le_antisymm
    · have : (GradedPredicate.credSup (fun _ : Nat => (0 : Credence))).val = 0 := by
        show iSup (fun _ : Nat => (0 : Credence).val) = 0
        simp only [Credence.zero_val, ciSup_const]
      exact le_of_eq (Credence.ext this)
    · exact (GradedPredicate.credSup _).nonneg

/-! ## The Robinson Q axioms as closed formulas

De Bruijn convention: under `forallE` the bound variable is `var 0`; an outer
bound variable seen from inside one more binder is `var 1`. -/

/-- Q1: `∀x, ¬(S x = 0)`. -/
def axSuccNeZero : ArithQFormula :=
  .forallE (.neg (.equal (succT (v 0)) zeroT))

/-- Q2: `∀x ∀y, S x = S y → x = y`. -/
def axSuccInj : ArithQFormula :=
  .forallE (.forallE
    (impF (.equal (succT (v 1)) (succT (v 0))) (.equal (v 1) (v 0))))

/-- Q3: `∀x, x = 0 ∨ ∃y, x = S y` (every number is zero or a successor). -/
def axPred : ArithQFormula :=
  .forallE (.disj (.equal (v 0) zeroT)
    (.existsE (.equal (v 1) (succT (v 0)))))

/-- Q4: `∀x, x + 0 = x`. -/
def axAddZero : ArithQFormula :=
  .forallE (.equal (addT (v 0) zeroT) (v 0))

/-- Q5: `∀x ∀y, x + S y = S (x + y)`. -/
def axAddSucc : ArithQFormula :=
  .forallE (.forallE
    (.equal (addT (v 1) (succT (v 0))) (succT (addT (v 1) (v 0)))))

/-- Q6: `∀x, x · 0 = 0`. -/
def axMulZero : ArithQFormula :=
  .forallE (.equal (mulT (v 0) zeroT) zeroT)

/-- Q7: `∀x ∀y, x · S y = x · y + x`. -/
def axMulSucc : ArithQFormula :=
  .forallE (.forallE
    (.equal (mulT (v 1) (succT (v 0))) (addT (mulT (v 1) (v 0)) (v 1))))

/-- The full Robinson Q axiom list. -/
def axioms : List ArithQFormula :=
  [axSuccNeZero, axSuccInj, axPred, axAddZero, axAddSucc, axMulZero, axMulSucc]

/-! ## Each axiom holds at certainty in the standard model

The universal cases reduce to a pointwise crisp equation true for every natural
number; `natModel_all_eq_one` then lifts the inf to `1`. -/

theorem eval_axSuccNeZero (env : natModel.Assignment) :
    natModel.evalFormula env axSuccNeZero = 1 := by
  refine natModel_all_eq_one (fun n => ?_)
  show ~(natModel.eq (n + 1) (0 : Nat)) = 1
  simp [natModel_eq]

theorem eval_axSuccInj (env : natModel.Assignment) :
    natModel.evalFormula env axSuccInj = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  refine natModel_all_eq_one (fun y => ?_)
  show ~(natModel.eq (x + 1) (y + 1)) ⊔ natModel.eq x y = 1
  by_cases hxy : x = y
  · subst hxy; simp [natModel_eq]
  · have hs : x + 1 ≠ y + 1 := fun h => hxy (Nat.succ_injective h)
    simp [natModel_eq, hxy, hs]

theorem eval_axPred (env : natModel.Assignment) :
    natModel.evalFormula env axPred = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  show natModel.eq x (0 : Nat) ⊔ natModel.ex (fun y : Nat => natModel.eq x (y + 1)) = 1
  cases x with
  | zero => simp [natModel_eq]
  | succ k =>
      have hk : natModel.eq (k + 1) (k + 1) ≤
          natModel.ex (fun y : Nat => natModel.eq (k + 1) (y + 1)) :=
        natModel_quantifierLaws.instance_le_ex (fun y : Nat => natModel.eq (k + 1) (y + 1)) k
      have hsup : natModel.ex (fun y : Nat => natModel.eq (k + 1) (y + 1)) = 1 := by
        apply le_antisymm
        · exact (natModel.ex _).le_one
        · rw [natModel_eq_self] at hk; exact hk
      rw [hsup, Credence.disj_one]

theorem eval_axAddZero (env : natModel.Assignment) :
    natModel.evalFormula env axAddZero = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  show natModel.eq (x + (0 : Nat)) x = 1
  exact natModel_eq_of_eq (Nat.add_zero x)

theorem eval_axAddSucc (env : natModel.Assignment) :
    natModel.evalFormula env axAddSucc = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  refine natModel_all_eq_one (fun y => ?_)
  show natModel.eq (x + (y + 1)) (x + y + 1) = 1
  exact natModel_eq_of_eq (Nat.add_succ x y)

theorem eval_axMulZero (env : natModel.Assignment) :
    natModel.evalFormula env axMulZero = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  show natModel.eq (x * (0 : Nat)) (0 : Nat) = 1
  exact natModel_eq_of_eq (Nat.mul_zero x)

theorem eval_axMulSucc (env : natModel.Assignment) :
    natModel.evalFormula env axMulSucc = 1 := by
  refine natModel_all_eq_one (fun x => ?_)
  refine natModel_all_eq_one (fun y => ?_)
  show natModel.eq (x * (y + 1)) (x * y + x) = 1
  exact natModel_eq_of_eq (Nat.mul_succ x y)

/-- Every Q axiom evaluates to certainty in the standard model, under every
    assignment.  This is the genuine "N ⊨ Q" content. -/
theorem axioms_eval_one (env : natModel.Assignment) :
    ∀ φ ∈ axioms, natModel.evalFormula env φ = 1 := by
  intro φ hφ
  simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with h | h | h | h | h | h | h <;> subst h
  · exact eval_axSuccNeZero env
  · exact eval_axSuccInj env
  · exact eval_axPred env
  · exact eval_axAddZero env
  · exact eval_axAddSucc env
  · exact eval_axMulZero env
  · exact eval_axMulSucc env

/-! ## Provability over Q and consistency -/

/-- `φ` is provable from the Robinson Q axioms at certainty. -/
def provableFromQ (φ : ArithQFormula) : Prop :=
  Nonempty (Structure.FoundationProof (1 : Credence) axioms φ)

/-- Consistency of Q over the standard model: `bot` is not provable from the
    Q axioms at certainty.  A proof would be sound at `natModel`, where the
    axioms are all designated `1`, forcing `1 ≤ evalFormula bot = 0`. -/
theorem arithQ_con : ¬ provableFromQ Formula.bot := by
  rintro ⟨p⟩
  have hsound := Structure.FoundationProof.sound p natModel
    (fun _ : Nat => natModel.witness)
    natModel_crispEquality natModel_quantifierLaws
    (fun φ hφ => le_of_eq (axioms_eval_one _ φ hφ).symm)
  have hbot : natModel.evalFormula (fun _ => natModel.witness) Formula.bot = 0 := rfl
  rw [hbot] at hsound
  have : (1 : Credence).val ≤ (0 : Credence).val := hsound
  norm_num at this

/-! ## Non-vacuity

Q proves genuine arithmetic facts.  `0 = 0` is derivable, and the structure
makes a concrete true equation (`2 + 1 = 3`) evaluate to certainty. -/

/-- `0 = 0` is provable from Q (reflexivity is a genuine rule). -/
theorem provableFromQ_zero_refl : provableFromQ (.equal zeroT zeroT) :=
  ⟨Structure.FoundationProof.equalityRefl zeroT⟩

/-- `x + 0 = x` is derivable from Q at `x := 0` via universal instantiation of
    `axAddZero`, a genuine arithmetic consequence rather than an axiom verbatim. -/
theorem provableFromQ_addZero_zero :
    provableFromQ (Formula.instantiate zeroT (.equal (addT (v 0) zeroT) (v 0))) :=
  ⟨Structure.FoundationProof.forallElim
    (Structure.FoundationProof.base (Structure.Proof.hyp (by
      show axAddZero ∈ axioms
      simp only [axioms, List.mem_cons]
      tauto)))⟩

/-- Concrete true arithmetic equation evaluated in the standard model:
    `S(S 0) + S 0 = S(S(S 0))`, i.e. `2 + 1 = 3`, holds at certainty. -/
theorem natModel_two_add_one (env : natModel.Assignment) :
    natModel.evalFormula env
        (.equal (addT (succT (succT zeroT)) (succT zeroT))
          (succT (succT (succT zeroT)))) = 1 := by
  show natModel.eq (2 + 1 : Nat) (3 : Nat) = 1
  exact natModel_eq_of_eq (by norm_num)

end arithQ
end Foundation
end Cred
