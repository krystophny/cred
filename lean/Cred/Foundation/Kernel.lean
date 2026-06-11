/-
  Cred Foundation Kernel

  Type-level certificates for the first-order foundation calculus.  Certificates
  erase to `Structure.Derivation` and inherit semantic soundness.
-/

import Cred.Foundation.Quantifier

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

end Structure

end Foundation
end Cred
