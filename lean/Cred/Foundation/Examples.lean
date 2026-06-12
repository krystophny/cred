/-
  Cred Foundation Examples

  Small proof certificates exercise the foundation kernel against equality and
  quantifier rules.
-/

import Cred.Foundation.Checker

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

def forallElimCertificateTree (φ : Formula Func Pred) (τ : Term Func) :
    FoundationCertificateTree Func Pred :=
  .node (.forallElim τ)
    [.node (.hyp [Formula.forallE φ] (Formula.forallE φ)) []]

theorem forallElimCertificateTree_checks [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
  (checkFoundationCertificate t
      (forallElimCertificateTree φ τ)).isSome := by
  simp [forallElimCertificateTree, checkFoundationCertificate,
    checkFoundationCertificateList, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

theorem forallElimCertificateTree_missing_child_fails
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ : Term Func) :
    checkFoundationCertificate t
      (.node (FoundationRulePayload.forallElim (Func := Func) (Pred := Pred) τ)
        []) = none := by
  simp [checkFoundationCertificate, checkFoundationCertificateList,
    applyFoundationRule, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

def equalitySubstitutionCertificateTree
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node (.equalitySubst τ υ φ)
    [.node (.hyp [Formula.equal τ υ, Formula.instantiate τ φ]
      (Formula.equal τ υ)) [],
     .node (.hyp [Formula.equal τ υ, Formula.instantiate τ φ]
      (Formula.instantiate τ φ)) []]

theorem equalitySubstitutionCertificateTree_checks
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
  (checkFoundationCertificate t
      (equalitySubstitutionCertificateTree τ υ φ)).isSome := by
  simp [equalitySubstitutionCertificateTree, checkFoundationCertificate,
    checkFoundationCertificateList, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

theorem equalitySubstitutionCertificateTree_missing_child_fails
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    checkFoundationCertificate t
      (.node (FoundationRulePayload.equalitySubst τ υ φ)
        [.node
          (FoundationRulePayload.hyp
            [Formula.equal τ υ, Formula.instantiate τ φ]
            (Formula.equal τ υ)) []]) = none := by
  simp [checkFoundationCertificate, checkFoundationCertificateList,
    applyFoundationRule, applyFoundationRuleUnchecked,
    FoundationRulePayload.childCount, FoundationRulePayload.code,
    FoundationRuleCode.childCount]

end Structure

end Foundation
end Cred
