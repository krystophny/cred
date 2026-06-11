/-
  Cred Foundation Examples

  Small proof certificates exercise the foundation kernel against equality and
  quantifier rules.
-/

import Cred.Foundation.Kernel

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def equalitySymmetryCertificate (t : Credence)
    (τ υ : Term Func) :
    FoundationProof t [@Formula.equal Func Pred τ υ] (Formula.equal υ τ) :=
  FoundationProof.equalitySymm
    (FoundationProof.base
      (Proof.hyp (List.mem_cons_self (Formula.equal τ υ) [])))

theorem equality_symmetry_certificate_sound (t : Credence)
    (τ υ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ] (Formula.equal υ τ) :=
  FoundationProof.sound (equalitySymmetryCertificate t τ υ)

def equalitySubstitutionCertificate (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationProof t
      [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  FoundationProof.equalitySubst
    (FoundationProof.base
      (Proof.hyp
        (List.mem_cons_self (Formula.equal τ υ)
          [Formula.instantiate τ φ])))
    (FoundationProof.base
      (Proof.hyp
        (List.mem_cons_of_mem (Formula.equal τ υ)
          (List.mem_cons_self (Formula.instantiate τ φ) []))))

theorem equality_substitution_certificate_sound (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  FoundationProof.sound (equalitySubstitutionCertificate t τ υ φ)

def forallElimCertificate (t : Credence)
    (φ : Formula Func Pred) (τ : Term Func) :
    FoundationProof t [Formula.forallE φ] (Formula.instantiate τ φ) :=
  FoundationProof.forallElim
    (FoundationProof.base
      (Proof.hyp (List.mem_cons_self (Formula.forallE φ) [])))

theorem forall_elim_certificate_sound (t : Credence)
    (φ : Formula Func Pred) (τ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [Formula.forallE φ] (Formula.instantiate τ φ) :=
  FoundationProof.sound (forallElimCertificate t φ τ)

def existsIntroCertificate (t : Credence)
    (φ : Formula Func Pred) (τ : Term Func) :
    FoundationProof t [Formula.instantiate τ φ] (Formula.existsE φ) :=
  FoundationProof.existsIntro
    (FoundationProof.base
      (Proof.hyp (List.mem_cons_self (Formula.instantiate τ φ) [])))

theorem exists_intro_certificate_sound (t : Credence)
    (φ : Formula Func Pred) (τ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [Formula.instantiate τ φ] (Formula.existsE φ) :=
  FoundationProof.sound (existsIntroCertificate t φ τ)

end Structure

end Foundation
end Cred
