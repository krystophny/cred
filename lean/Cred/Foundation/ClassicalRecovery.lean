/-
  Cred Foundation: Exhaustive Classical Propositional Recovery

  The honest core of the foundation claim: classical PROPOSITIONAL reasoning
  is recovered exactly on the crisp ({0,1}-valued) fragment of Cred. This is
  recovery, not replacement -- it shows that higher Lean layers may reason
  classically about crisp atoms without leaving Cred, while the graded
  interior and the conditioning boundary remain non-classical.

  Three strands, all reusing the crisp_* lemmas from Cred.Bridge.Crisp and the
  Boolean anchor from Cred.Aggregation.Specializations rather than re-proving
  them:

  1. Consequence coincidence: on crisp valuations Cred certainty-consequence is
     classical Boolean consequence, and (via the Boolean anchor) this is the
     pointwise classical relation.
  2. Connective laws at certainty: every classical negation/conjunction/
     disjunction law (double negation, De Morgan, idempotence, commutativity,
     associativity, excluded middle, non-contradiction) holds at certainty on
     crisp valuations.
  3. Inference recovery: classical modus ponens (material form), conjunction
     introduction/elimination, and disjunction introduction are recovered as
     crisp certainty-consequences.

  The material conditional A -> B is the formula ~A \/ B (`materialImp`); there
  is no internal implication or conditional constructor, in keeping with the
  no-arrow discipline of the foundation layer.

  Anchor: `classical_propositional_is_fragment` bundles the recovery.
-/

import Cred.Bridge.Crisp
import Cred.Aggregation.Specializations

namespace Cred.Foundation

open Cred

variable {α : Type*}

/-! ## Material Conditional as a Formula

No arrow constructor exists; the material conditional is the derived formula
`~A \/ B`. Classically `classicalEval v (materialImp A B) = true` iff
`classicalEval v A = true -> classicalEval v B = true`. -/

/-- The material conditional `A -> B`, encoded as the formula `~A \/ B`. -/
def materialImp (A B : Formula α) : Formula α :=
  Formula.disj (Formula.neg A) B

/-- Classical truth of the material conditional is classical implication. -/
theorem classicalEval_materialImp (v : α → Bool) (A B : Formula α) :
    classicalEval v (materialImp A B) = true ↔
    (classicalEval v A = true → classicalEval v B = true) := by
  simp only [materialImp, classicalEval]
  cases classicalEval v A <;> cases classicalEval v B <;> simp

/-! ## 1. Consequence Coincidence

`crispCertainty` (Cred certainty consequence on crisp valuations) is exactly
`classicalConsequence`, by `crisp_certainty_iff_classical`. Through the Boolean
anchor `boolean_forall_consequence_is_classical` this is the pointwise
classical relation; we record the bridge to that anchor's shape. -/

/-- A list of premise formulas, all classically true, force the conclusion
    classically true: the pointwise classical relation, in the single-valuation
    shape that `crisp_certainty_iff_classical` produces. -/
theorem crisp_certainty_is_pointwise_classical
    (premises : List (Formula α)) (conclusion : Formula α) :
    crispCertainty α premises conclusion ↔
    (∀ v : α → Bool, (∀ p ∈ premises, classicalEval v p = true) →
      classicalEval v conclusion = true) :=
  crisp_certainty_iff_classical α premises conclusion

/-! ## 2. Classical Connective Laws at Certainty on Crisp Valuations

Each law is the certainty (evaluation = 1) of a closed classical tautology on
every crisp valuation. The crisp survivors `crisp_excluded_middle_formula`,
`crisp_non_contradiction_formula`, and `double_neg_elim_formula` are reused
directly; the algebraic laws (De Morgan, idempotence, commutativity,
associativity) ride on the Boolean homomorphisms via `classical_tautology_certain`. -/

/-- Double negation: `~~A` evaluates to the same as `A`, on every valuation;
    in particular crisply they have equal certainty. Reuses
    `double_neg_elim_formula`. -/
theorem recover_double_negation (w : α → Credence) (A : Formula α) :
    evalCred w (Formula.neg (Formula.neg A)) = evalCred w A :=
  double_neg_elim_formula w A

/-- Excluded middle is certain on crisp valuations. Reuses
    `crisp_excluded_middle_formula`. -/
theorem recover_excluded_middle (w : α → Credence)
    (hw : ∀ a, w a = 0 ∨ w a = 1) (A : Formula α) :
    evalCred w (Formula.disj A (Formula.neg A)) = 1 :=
  crisp_excluded_middle_formula w hw A

/-- Non-contradiction is impossible (certainty 0) on crisp valuations. Reuses
    `crisp_non_contradiction_formula`. -/
theorem recover_non_contradiction (w : α → Credence)
    (hw : ∀ a, w a = 0 ∨ w a = 1) (A : Formula α) :
    evalCred w (Formula.conj A (Formula.neg A)) = 0 :=
  crisp_non_contradiction_formula w hw A

/-- A classical propositional tautology is certain on every crisp valuation.
    Reuses `classical_tautology_certain`; the De Morgan, idempotence,
    commutativity, and associativity laws are instances obtained by checking
    the classical side with `decide` per Boolean valuation. -/
theorem recover_tautology_certain (φ : Formula α)
    (h : ∀ v : α → Bool, classicalEval v φ = true)
    (w : α → Credence) (hw : ∀ a, w a = 0 ∨ w a = 1) :
    evalCred w φ = 1 :=
  classical_tautology_certain φ h w hw

/-! ## 3. Classical Inference Recovery (Crisp Certainty)

Modus ponens, conjunction introduction/elimination, and disjunction
introduction are recovered as crisp certainty-consequences. Each is proved by
discharging the classical relation (which `decide`s pointwise on Booleans) and
transporting through `crisp_certainty_iff_classical`. -/

/-- Modus ponens (material form): from `A` and `A -> B` infer `B`, as a crisp
    certainty-consequence. -/
theorem recover_modus_ponens (A B : Formula α) :
    crispCertainty α [A, materialImp A B] B := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have hA : classicalEval v A = true := hprem A (by simp)
  have hImp : classicalEval v (materialImp A B) = true :=
    hprem (materialImp A B) (by simp)
  exact (classicalEval_materialImp v A B).mp hImp hA

/-- Conjunction introduction: from `A` and `B` infer `A /\ B`, crisply. -/
theorem recover_conj_intro (A B : Formula α) :
    crispCertainty α [A, B] (Formula.conj A B) := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have hA : classicalEval v A = true := hprem A (by simp)
  have hB : classicalEval v B = true := hprem B (by simp)
  simp only [classicalEval, hA, hB, Bool.and_self]

/-- Conjunction elimination (left): from `A /\ B` infer `A`, crisply. -/
theorem recover_conj_elim_left (A B : Formula α) :
    crispCertainty α [Formula.conj A B] A := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have h : classicalEval v (Formula.conj A B) = true := hprem _ (by simp)
  simp only [classicalEval, Bool.and_eq_true] at h
  exact h.1

/-- Conjunction elimination (right): from `A /\ B` infer `B`, crisply. -/
theorem recover_conj_elim_right (A B : Formula α) :
    crispCertainty α [Formula.conj A B] B := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have h : classicalEval v (Formula.conj A B) = true := hprem _ (by simp)
  simp only [classicalEval, Bool.and_eq_true] at h
  exact h.2

/-- Disjunction introduction (left): from `A` infer `A \/ B`, crisply. -/
theorem recover_disj_intro_left (A B : Formula α) :
    crispCertainty α [A] (Formula.disj A B) := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have hA : classicalEval v A = true := hprem A (by simp)
  simp only [classicalEval, hA, Bool.true_or]

/-- Disjunction introduction (right): from `B` infer `A \/ B`, crisply. -/
theorem recover_disj_intro_right (A B : Formula α) :
    crispCertainty α [B] (Formula.disj A B) := by
  rw [crisp_certainty_is_pointwise_classical]
  intro v hprem
  have hB : classicalEval v B = true := hprem B (by simp)
  simp only [classicalEval, hB, Bool.or_true]

/-! ## The Packaged Recovery

`classical_propositional_is_fragment` bundles the three strands: consequence
coincidence, the connective laws at certainty (excluded middle, non-
contradiction, double negation), and the inference rules (modus ponens,
conjunction and disjunction reasoning). The conjunction is the honest scope
statement: classical propositional logic is exactly the crisp fragment of
Cred. -/

theorem classical_propositional_is_fragment :
    -- (a) consequence coincidence: crisp certainty = classical consequence
    (∀ (premises : List (Formula α)) (conclusion : Formula α),
      crispCertainty α premises conclusion ↔
      classicalConsequence α premises conclusion) ∧
    -- (a') and equivalently the pointwise classical relation
    (∀ (premises : List (Formula α)) (conclusion : Formula α),
      crispCertainty α premises conclusion ↔
      (∀ v : α → Bool, (∀ p ∈ premises, classicalEval v p = true) →
        classicalEval v conclusion = true)) ∧
    -- (b) connective laws at certainty on crisp valuations
    (∀ (w : α → Credence), (∀ a, w a = 0 ∨ w a = 1) → ∀ A : Formula α,
      evalCred w (Formula.disj A (Formula.neg A)) = 1) ∧
    (∀ (w : α → Credence), (∀ a, w a = 0 ∨ w a = 1) → ∀ A : Formula α,
      evalCred w (Formula.conj A (Formula.neg A)) = 0) ∧
    (∀ (w : α → Credence) (A : Formula α),
      evalCred w (Formula.neg (Formula.neg A)) = evalCred w A) ∧
    -- (c) classical inference recovered crisply
    (∀ A B : Formula α, crispCertainty α [A, materialImp A B] B) ∧
    (∀ A B : Formula α, crispCertainty α [A, B] (Formula.conj A B)) ∧
    (∀ A B : Formula α, crispCertainty α [Formula.conj A B] A) ∧
    (∀ A B : Formula α, crispCertainty α [Formula.conj A B] B) ∧
    (∀ A B : Formula α, crispCertainty α [A] (Formula.disj A B)) ∧
    (∀ A B : Formula α, crispCertainty α [B] (Formula.disj A B)) :=
  ⟨crisp_certainty_iff_classical α,
   crisp_certainty_is_pointwise_classical,
   recover_excluded_middle,
   recover_non_contradiction,
   recover_double_negation,
   recover_modus_ponens,
   recover_conj_intro,
   recover_conj_elim_left,
   recover_conj_elim_right,
   recover_disj_intro_left,
   recover_disj_intro_right⟩

end Cred.Foundation
