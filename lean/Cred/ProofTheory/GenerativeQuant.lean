/-
  Cred ProofTheory: Generative Quantifier and Equality Rules (issues #634, #642)

  `Cred.ProofTheory.Generative` gives a fully local labelled calculus for the
  connective fragment (negation, conjunction, disjunction) over a toy
  propositional `Formula`.  That fragment has no equality and no quantifiers,
  because its formulas have no term structure.

  This module extends the generative programme to the first-order foundation
  language `Cred.Foundation.Formula`, which does carry terms, equality and
  quantifiers.  The calculus `GenDerives` is generative in the same sense as
  `Generative.Derives`: every constructor is a local introduction, elimination,
  or structural step, and soundness is proved by induction against the credence
  semantics.  The equality and quantifier steps reuse the law interfaces
  `Structure.CrispEquality` and `Structure.QuantifierLaws` and the *semantic*
  lemmas `equality_substitution_threshold`, `forall_elim_semantic`,
  `exists_intro_semantic` proved over them.  No semantic-consequence relation is
  imported as an oracle rule.

  There is no implication or conditional formula constructor; the foundation
  language has none, and none is added here.
-/

import Cred.Foundation.Equality
import Cred.Foundation.Quantifier

namespace Cred.ProofTheory

open Cred Cred.Foundation Cred.Foundation.Structure

universe u v w

variable {Func : Type u} {Pred : Type v}

/-- A model is generatively *admissible* when it satisfies both law interfaces:
    crisp equality and the quantifier order laws.  These are exactly the
    hypotheses the equality and quantifier rules below need; carrying them in
    one bundle keeps the generative consequence target self-contained. -/
structure LawModel (M : Structure.{u, v, w} Func Pred) : Prop where
  equality : M.CrispEquality
  quantifier : M.QuantifierLaws

/-- Generative threshold consequence relative to the law interfaces: every
    admissible model that designates all premises at threshold `t` designates
    the conclusion at `t`.  This is the soundness target for `GenDerives`. -/
def GenConsequence (t : Credence)
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    LawModel.{u, v, w} M →
    (∀ p ∈ premises, t ≤ M.evalFormula env p) →
    t ≤ M.evalFormula env conclusion

/-! ## The Generative Calculus

`GenDerives t Γ φ` reads: from premises `Γ` demanded at threshold `t`, the
conclusion `φ` is derivable.  Every constructor is a local rule. -/

inductive GenDerives (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Prop where
  /-- A premise is derivable. -/
  | hyp {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      φ ∈ Γ → GenDerives t Γ φ
  /-- Adding premises preserves derivability. -/
  | weaken {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      GenDerives t Γ φ → (∀ p ∈ Γ, p ∈ Δ) → GenDerives t Δ φ
  /-- Cut on a derived intermediate formula. -/
  | cut {Γ : List (Formula Func Pred)} {mid φ : Formula Func Pred} :
      GenDerives t Γ mid → GenDerives t (mid :: Γ) φ → GenDerives t Γ φ
  /-- Equality reflexivity is a local axiom (no premises). -/
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      GenDerives t Γ (Formula.equal τ τ)
  /-- Equality substitution (Leibniz, local form): from `τ = υ` and a property
      holding of `τ`, conclude the property of `υ`.  Sound because crisp
      equality forces the term denotations to coincide. -/
  | equalitySubst {Γ : List (Formula Func Pred)} {τ υ : Term Func}
      {φ : Formula Func Pred} :
      GenDerives t Γ (Formula.equal τ υ) →
      GenDerives t Γ (Formula.instantiate τ φ) →
      GenDerives t Γ (Formula.instantiate υ φ)
  /-- Universal elimination: from `∀φ`, conclude any instance `φ[τ]`.  Sound
      because the quantifier law puts the universal below every instance. -/
  | forallElim {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      (τ : Term Func) :
      GenDerives t Γ (Formula.forallE φ) →
      GenDerives t Γ (Formula.instantiate τ φ)
  /-- Existential introduction: from an instance `φ[τ]`, conclude `∃φ`.  Sound
      because the quantifier law puts every instance below the existential. -/
  | existsIntro {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      (τ : Term Func) :
      GenDerives t Γ (Formula.instantiate τ φ) →
      GenDerives t Γ (Formula.existsE φ)

/-! ## Soundness -/

/-- The generative quantifier/equality calculus is sound against the credence
    semantics for every law-respecting model.  Proved by induction over the
    local rules; the equality and quantifier cases reuse the semantic lemmas
    `equality_substitution_threshold`, `forall_elim_semantic`, and
    `exists_intro_semantic`. -/
theorem genDerives_sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : GenDerives t Γ φ) :
    GenConsequence.{u, v, w} t Γ φ := by
  induction h with
  | hyp hmem =>
      intro M env _ hΓ; exact hΓ _ hmem
  | weaken _ hsub ih =>
      intro M env hLaw hΔ
      exact ih M env hLaw (fun p hp => hΔ p (hsub p hp))
  | cut _ _ ihmid ihgoal =>
      intro M env hLaw hΓ
      have hmid := ihmid M env hLaw hΓ
      apply ihgoal M env hLaw
      intro p hp
      cases List.mem_cons.mp hp with
      | inl h => subst h; exact hmid
      | inr h => exact hΓ p h
  | equalityRefl τ =>
      intro M env hLaw _
      simp [evalFormula, hLaw.equality.eq_refl, Credence.le_one']
  | equalitySubst _ _ ihEq ihφ =>
      intro M env hLaw hΓ
      exact equality_substitution_threshold t _ _ _ M env hLaw.equality (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl h => subst h; exact ihEq M env hLaw hΓ
        | inr h =>
            cases List.mem_cons.mp h with
            | inl h => subst h; exact ihφ M env hLaw hΓ
            | inr h => cases h)
  | forallElim τ _ ih =>
      intro M env hLaw hΓ
      rw [evalFormula_instantiate]
      exact forall_elim_semantic t M env hLaw.quantifier _ (M.evalTerm env τ)
        (ih M env hLaw hΓ)
  | existsIntro τ _ ih =>
      intro M env hLaw hΓ
      apply exists_intro_semantic t M env hLaw.quantifier _ (M.evalTerm env τ)
      rw [← evalFormula_instantiate]
      exact ih M env hLaw hΓ

/-! ## Per-rule soundness corollaries

Each names the soundness consequence of one generative rule, as a one-line
specialization of `genDerives_sound`.  These are the citation hooks for the
paper. -/

/-- Equality substitution is sound: from `τ = υ` and `φ[τ]` it derives `φ[υ]`. -/
theorem equalitySubst_sound {t : Credence} {Γ : List (Formula Func Pred)}
    {τ υ : Term Func} {φ : Formula Func Pred}
    (hEq : GenDerives t Γ (Formula.equal τ υ))
    (hφ : GenDerives t Γ (Formula.instantiate τ φ)) :
    GenConsequence.{u, v, w} t Γ (Formula.instantiate υ φ) :=
  genDerives_sound (GenDerives.equalitySubst hEq hφ)

/-- Universal elimination is sound: from `∀φ` it derives any instance `φ[τ]`. -/
theorem forallElim_sound {t : Credence} {Γ : List (Formula Func Pred)}
    {φ : Formula Func Pred} (τ : Term Func)
    (h : GenDerives t Γ (Formula.forallE φ)) :
    GenConsequence.{u, v, w} t Γ (Formula.instantiate τ φ) :=
  genDerives_sound (GenDerives.forallElim τ h)

/-- Existential introduction is sound: from an instance `φ[τ]` it derives `∃φ`. -/
theorem existsIntro_sound {t : Credence} {Γ : List (Formula Func Pred)}
    {φ : Formula Func Pred} (τ : Term Func)
    (h : GenDerives t Γ (Formula.instantiate τ φ)) :
    GenConsequence.{u, v, w} t Γ (Formula.existsE φ) :=
  genDerives_sound (GenDerives.existsIntro τ h)

-- TODO(generative): the connective fragment (conjElim / disjIntro) is not
-- duplicated here.  The propositional generative rules live in
-- `Cred.ProofTheory.Generative` over the toy `Formula`; lifting them to the
-- foundation `Formula` plus a per-premise `Label` layer (so the cross-label
-- lifting rules of `Generative.Derives` apply to first-order formulas) is the
-- remaining unification step.  It needs a shared labelled context over
-- `Foundation.Formula`, which the current single-threshold `GenDerives` does
-- not yet carry.

end Cred.ProofTheory
