/-
  Cred Kernel: Proof Certificates for Labelled Derivations

  This module is the first kernel boundary.  A `Proof` is data in `Type`
  rather than a derivability proposition.  Each certificate erases to the labelled
  calculus and inherits its soundness theorem.
-/

import Cred.Sequent

namespace Cred
namespace Kernel

open Credence

universe u

variable {α : Type u}

inductive Proof : LabelContext α → LabelledFormula α → Type (max 1 u) where
  | hyp {Γ : LabelContext α} {b : LabelledFormula α} :
      b ∈ Γ.bounds → Proof Γ b
  | weaken {Γ Δ : LabelContext α} {b : LabelledFormula α} :
      Proof Γ b →
      (∀ x ∈ Γ.bounds, x ∈ Δ.bounds) →
      (∀ J ∈ Γ.conds, J ∈ Δ.conds) →
      Proof Δ b
  | cut {Γ : LabelContext α} {mid b : LabelledFormula α} :
      Proof Γ mid →
      Proof (Γ.addBound mid) b →
      Proof Γ b
  | thresholdMono {Γ : LabelContext α} {s t : Credence} {φ : Formula α} :
      Proof Γ { kind := .threshold s, formula := φ } →
      t ≤ s →
      Proof Γ { kind := .threshold t, formula := φ }
  | thresholdToPositive {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      Proof Γ { kind := .threshold t, formula := φ } →
      0 < t.val →
      Proof Γ { kind := .positive, formula := φ }
  | certainToThreshold {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      Proof Γ { kind := .certain, formula := φ } →
      Proof Γ { kind := .threshold t, formula := φ }
  | positivityRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaPositivity α premises conclusion →
      (∀ p ∈ premises, Proof Γ { kind := .positive, formula := p }) →
      Proof Γ { kind := .positive, formula := conclusion }
  | certaintyRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaCertainty α premises conclusion →
      (∀ p ∈ premises, Proof Γ { kind := .certain, formula := p }) →
      Proof Γ { kind := .certain, formula := conclusion }
  | thresholdRule {Γ : LabelContext α} {t : Credence}
      {premises : List (Formula α)} {conclusion : Formula α} :
      thresholdConsequence t α premises conclusion →
      (∀ p ∈ premises, Proof Γ { kind := .threshold t, formula := p }) →
      Proof Γ { kind := .threshold t, formula := conclusion }
  | chainRuleCut {Γ : LabelContext α} {J : CondJudgment α}
      {t lower : Credence} :
      J ∈ Γ.conds →
      lower ≤ J.cond →
      Proof Γ { kind := .threshold t, formula := J.evidence } →
      Proof Γ { kind := .threshold (lower ⊗ t), formula := J.joint }
  | conjElimLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Proof Γ { kind := .threshold t, formula := .conj φ ψ } →
      Proof Γ { kind := .threshold t, formula := φ }
  | conjElimRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Proof Γ { kind := .threshold t, formula := .conj φ ψ } →
      Proof Γ { kind := .threshold t, formula := ψ }
  | disjIntroLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Proof Γ { kind := .threshold t, formula := φ } →
      Proof Γ { kind := .threshold t, formula := .disj φ ψ }
  | disjIntroRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Proof Γ { kind := .threshold t, formula := ψ } →
      Proof Γ { kind := .threshold t, formula := .disj φ ψ }
  | negNegIntro {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      Proof Γ { kind := k, formula := φ } →
      Proof Γ { kind := k, formula := .neg (.neg φ) }
  | negNegElim {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      Proof Γ { kind := k, formula := .neg (.neg φ) } →
      Proof Γ { kind := k, formula := φ }

namespace Proof

def toDerivation {Γ : LabelContext α} {goal : LabelledFormula α} :
    Proof Γ goal → Derivation Γ goal
  | hyp hb => Derivation.hyp hb
  | weaken h hbounds hconds =>
      Derivation.weaken h.toDerivation hbounds hconds
  | cut hmid hgoal =>
      Derivation.cut hmid.toDerivation hgoal.toDerivation
  | thresholdMono h hle =>
      Derivation.thresholdMono h.toDerivation hle
  | thresholdToPositive h ht =>
      Derivation.thresholdToPositive h.toDerivation ht
  | certainToThreshold h =>
      Derivation.certainToThreshold h.toDerivation
  | positivityRule hsem hprems =>
      Derivation.positivityRule hsem
        (fun p hp => (hprems p hp).toDerivation)
  | certaintyRule hsem hprems =>
      Derivation.certaintyRule hsem
        (fun p hp => (hprems p hp).toDerivation)
  | thresholdRule hsem hprems =>
      Derivation.thresholdRule hsem
        (fun p hp => (hprems p hp).toDerivation)
  | chainRuleCut hJ hcond hEvidence =>
      Derivation.chainRuleCut hJ hcond hEvidence.toDerivation
  | conjElimLeft h =>
      Derivation.conjElimLeft h.toDerivation
  | conjElimRight h =>
      Derivation.conjElimRight h.toDerivation
  | disjIntroLeft h =>
      Derivation.disjIntroLeft h.toDerivation
  | disjIntroRight h =>
      Derivation.disjIntroRight h.toDerivation
  | negNegIntro h =>
      Derivation.negNegIntro h.toDerivation
  | negNegElim h =>
      Derivation.negNegElim h.toDerivation

theorem sound {Γ : LabelContext α} {goal : LabelledFormula α}
    (p : Proof Γ goal) :
    ∀ v : α → Credence, Γ.Satisfied v → goal.Satisfied v :=
  derivation_sound p.toDerivation

theorem to_thresholdConsequence {t : Credence}
    {premises : List (Formula α)} {conclusion : Formula α}
    (p : Proof (formulaContext (.threshold t) premises)
      { kind := .threshold t, formula := conclusion }) :
    thresholdConsequence t α premises conclusion :=
  derivation_sound_thresholdConsequence p.toDerivation

theorem to_formulaCertainty
    {premises : List (Formula α)} {conclusion : Formula α}
    (p : Proof (formulaContext .certain premises)
      { kind := .certain, formula := conclusion }) :
    formulaCertainty α premises conclusion :=
  derivation_sound_formulaCertainty p.toDerivation

theorem to_formulaPositivity
    {premises : List (Formula α)} {conclusion : Formula α}
    (p : Proof (formulaContext .positive premises)
      { kind := .positive, formula := conclusion }) :
    formulaPositivity α premises conclusion :=
  derivation_sound_formulaPositivity p.toDerivation

end Proof

theorem no_ex_falso_certificate :
    Proof noExFalsoContext { kind := .positive, formula := .atom 1 } → False :=
  fun p => labelled_no_ex_falso p.toDerivation

end Kernel
end Cred
