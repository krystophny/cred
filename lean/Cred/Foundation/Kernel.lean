/-
  Cred Foundation Kernel

  Type-level certificates for the first-order foundation calculus.  Certificates
  erase to `Structure.Derivation` and inherit semantic soundness.
-/

import Cred.Foundation.Calculus

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

inductive Proof (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Type (max 1 u v) where
  | hyp {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      φ ∈ Γ → Proof t Γ φ
  | weaken {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Proof t Γ φ →
      (∀ p ∈ Γ, p ∈ Δ) →
      Proof t Δ φ
  | cut {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Proof t Γ φ →
      Proof t (φ :: Γ) ψ →
      Proof t Γ ψ
  | conjElimLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Proof t Γ (.conj φ ψ) →
      Proof t Γ φ
  | conjElimRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Proof t Γ (.conj φ ψ) →
      Proof t Γ ψ
  | disjIntroLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Proof t Γ φ →
      Proof t Γ (.disj φ ψ)
  | disjIntroRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Proof t Γ ψ →
      Proof t Γ (.disj φ ψ)

namespace Proof

def toDerivation {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
    Proof t Γ φ → Derivation t Γ φ
  | hyp hp => Derivation.hyp hp
  | weaken p hsub => Derivation.weaken p.toDerivation hsub
  | cut p q => Derivation.cut p.toDerivation q.toDerivation
  | conjElimLeft p => Derivation.conjElimLeft p.toDerivation
  | conjElimRight p => Derivation.conjElimRight p.toDerivation
  | disjIntroLeft p => Derivation.disjIntroLeft p.toDerivation
  | disjIntroRight p => Derivation.disjIntroRight p.toDerivation

theorem sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (p : Proof t Γ φ) :
    ThresholdConsequence.{u, v, w} t Γ φ :=
  derivation_sound p.toDerivation

end Proof

inductive CrispProof (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Type (max 1 u v) where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Proof t Γ φ → CrispProof t Γ φ
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      CrispProof t Γ (.equal τ τ)
  | equalitySymm {Γ : List (Formula Func Pred)} {τ υ : Term Func} :
      CrispProof t Γ (.equal τ υ) →
      CrispProof t Γ (.equal υ τ)
  | equalityTrans {Γ : List (Formula Func Pred)} {τ υ χ : Term Func} :
      CrispProof t Γ (.equal τ υ) →
      CrispProof t Γ (.equal υ χ) →
      CrispProof t Γ (.equal τ χ)
  | equalitySubst {Γ : List (Formula Func Pred)} {τ υ : Term Func}
      {φ : Formula Func Pred} :
      CrispProof t Γ (.equal τ υ) →
      CrispProof t Γ (Formula.instantiate τ φ) →
      CrispProof t Γ (Formula.instantiate υ φ)

namespace CrispProof

def toDerivation {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
    CrispProof t Γ φ → CrispDerivation t Γ φ
  | base p => CrispDerivation.base p.toDerivation
  | equalityRefl τ => CrispDerivation.equalityRefl τ
  | equalitySymm p => CrispDerivation.equalitySymm p.toDerivation
  | equalityTrans p q => CrispDerivation.equalityTrans p.toDerivation q.toDerivation
  | equalitySubst p q => CrispDerivation.equalitySubst p.toDerivation q.toDerivation

theorem sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (p : CrispProof t Γ φ) :
    CrispThresholdConsequence.{u, v, w} t Γ φ :=
  crisp_derivation_sound p.toDerivation

end CrispProof

inductive QuantifierProof (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Type (max 1 u v) where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Proof t Γ φ → QuantifierProof t Γ φ
  | forallElim {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      QuantifierProof t Γ (.forallE φ) →
      QuantifierProof t Γ (Formula.instantiate τ φ)
  | existsIntro {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      QuantifierProof t Γ (Formula.instantiate τ φ) →
      QuantifierProof t Γ (.existsE φ)

namespace QuantifierProof

def toDerivation {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
    QuantifierProof t Γ φ → QuantifierDerivation t Γ φ
  | base p => QuantifierDerivation.base p.toDerivation
  | forallElim p => QuantifierDerivation.forallElim p.toDerivation
  | existsIntro p => QuantifierDerivation.existsIntro p.toDerivation

theorem sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (p : QuantifierProof t Γ φ) :
    QuantifierThresholdConsequence.{u, v, w} t Γ φ :=
  quantifier_derivation_sound p.toDerivation

end QuantifierProof

inductive FoundationProof (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Type (max 1 u v) where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Proof t Γ φ → FoundationProof t Γ φ
  | weaken {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      FoundationProof t Γ φ →
      (∀ p ∈ Γ, p ∈ Δ) →
      FoundationProof t Δ φ
  | cut {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationProof t Γ φ →
      FoundationProof t (φ :: Γ) ψ →
      FoundationProof t Γ ψ
  | conjElimLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationProof t Γ (.conj φ ψ) →
      FoundationProof t Γ φ
  | conjElimRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationProof t Γ (.conj φ ψ) →
      FoundationProof t Γ ψ
  | disjIntroLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationProof t Γ φ →
      FoundationProof t Γ (.disj φ ψ)
  | disjIntroRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationProof t Γ ψ →
      FoundationProof t Γ (.disj φ ψ)
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      FoundationProof t Γ (.equal τ τ)
  | equalitySymm {Γ : List (Formula Func Pred)} {τ υ : Term Func} :
      FoundationProof t Γ (.equal τ υ) →
      FoundationProof t Γ (.equal υ τ)
  | equalityTrans {Γ : List (Formula Func Pred)} {τ υ χ : Term Func} :
      FoundationProof t Γ (.equal τ υ) →
      FoundationProof t Γ (.equal υ χ) →
      FoundationProof t Γ (.equal τ χ)
  | equalitySubst {Γ : List (Formula Func Pred)} {τ υ : Term Func}
      {φ : Formula Func Pred} :
      FoundationProof t Γ (.equal τ υ) →
      FoundationProof t Γ (Formula.instantiate τ φ) →
      FoundationProof t Γ (Formula.instantiate υ φ)
  | forallElim {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      FoundationProof t Γ (.forallE φ) →
      FoundationProof t Γ (Formula.instantiate τ φ)
  | existsIntro {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      FoundationProof t Γ (Formula.instantiate τ φ) →
      FoundationProof t Γ (.existsE φ)

namespace FoundationProof

def toDerivation {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
    FoundationProof t Γ φ → FoundationDerivation t Γ φ
  | base p => FoundationDerivation.base p.toDerivation
  | weaken p hsub => FoundationDerivation.weaken p.toDerivation hsub
  | cut p q => FoundationDerivation.cut p.toDerivation q.toDerivation
  | conjElimLeft p => FoundationDerivation.conjElimLeft p.toDerivation
  | conjElimRight p => FoundationDerivation.conjElimRight p.toDerivation
  | disjIntroLeft p => FoundationDerivation.disjIntroLeft p.toDerivation
  | disjIntroRight p => FoundationDerivation.disjIntroRight p.toDerivation
  | equalityRefl τ => FoundationDerivation.equalityRefl τ
  | equalitySymm p => FoundationDerivation.equalitySymm p.toDerivation
  | equalityTrans p q =>
      FoundationDerivation.equalityTrans p.toDerivation q.toDerivation
  | equalitySubst p q =>
      FoundationDerivation.equalitySubst p.toDerivation q.toDerivation
  | forallElim p => FoundationDerivation.forallElim p.toDerivation
  | existsIntro p => FoundationDerivation.existsIntro p.toDerivation

theorem sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (p : FoundationProof t Γ φ) :
    FoundationThresholdConsequence.{u, v, w} t Γ φ :=
  foundation_derivation_sound p.toDerivation

end FoundationProof

end Structure

end Foundation
end Cred
