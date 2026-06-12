/-
  Cred Foundation Certificate Builder

  Builders assemble certificate trees from rule inputs instead of hand-written
  node lists. Acceptance lemmas show the checker accepts each builder's output.
-/

import Cred.Foundation.Examples

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def hypLeaf (Γ : List (Formula Func Pred)) (φ : Formula Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node (.hyp Γ φ) []

def equalitySymmNode (child : FoundationCertificateTree Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node .equalitySymm [child]

def forallElimNode (τ : Term Func)
    (child : FoundationCertificateTree Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node (.forallElim τ) [child]

def equalitySubstNode (τ υ : Term Func) (φ : Formula Func Pred)
    (eqChild instChild : FoundationCertificateTree Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node (.equalitySubst τ υ φ) [eqChild, instChild]

def existsIntroNode (φ : Formula Func Pred) (τ : Term Func)
    (child : FoundationCertificateTree Func Pred) :
    FoundationCertificateTree Func Pred :=
  .node (.existsIntro φ τ) [child]

theorem hypLeaf_checks_to [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : φ ∈ Γ) :
    checkFoundationCertificate t (hypLeaf Γ φ) =
      some (CheckedFoundationProof.mk Γ φ
        (FoundationProof.base (Proof.hyp h))) := by
  simp [hypLeaf, checkFoundationCertificate, checkFoundationCertificateList,
    applyFoundationRule, applyFoundationRuleUnchecked,
    FoundationRulePayload.childCount, FoundationRulePayload.code,
    FoundationRuleCode.childCount, h]

theorem hypLeaf_accepted [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : φ ∈ Γ) :
    (checkFoundationCertificate t (hypLeaf Γ φ)).isSome := by
  rw [hypLeaf_checks_to t h]
  rfl

theorem equalitySymmNode_checks_to [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {child : FoundationCertificateTree Func Pred}
    {Γ : List (Formula Func Pred)} {τ υ : Term Func}
    {p : FoundationProof t Γ (Formula.equal τ υ)}
    (hchild : checkFoundationCertificate t child =
      some (CheckedFoundationProof.mk Γ (Formula.equal τ υ) p)) :
    checkFoundationCertificate t (equalitySymmNode child) =
      some (CheckedFoundationProof.mk Γ (Formula.equal υ τ)
        (FoundationProof.equalitySymm p)) := by
  simp [equalitySymmNode, checkFoundationCertificate,
    checkFoundationCertificateList, hchild, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

theorem forallElimNode_checks_to [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {child : FoundationCertificateTree Func Pred}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} {τ : Term Func}
    {p : FoundationProof t Γ (Formula.forallE φ)}
    (hchild : checkFoundationCertificate t child =
      some (CheckedFoundationProof.mk Γ (Formula.forallE φ) p)) :
    checkFoundationCertificate t (forallElimNode τ child) =
      some (CheckedFoundationProof.mk Γ (Formula.instantiate τ φ)
        (FoundationProof.forallElim p)) := by
  simp [forallElimNode, checkFoundationCertificate,
    checkFoundationCertificateList, hchild, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

theorem equalitySubstNode_checks_to [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {eqChild instChild : FoundationCertificateTree Func Pred}
    {Γ : List (Formula Func Pred)} {τ υ : Term Func} {φ : Formula Func Pred}
    {p : FoundationProof t Γ (Formula.equal τ υ)}
    {q : FoundationProof t Γ (Formula.instantiate τ φ)}
    (heq : checkFoundationCertificate t eqChild =
      some (CheckedFoundationProof.mk Γ (Formula.equal τ υ) p))
    (hinst : checkFoundationCertificate t instChild =
      some (CheckedFoundationProof.mk Γ (Formula.instantiate τ φ) q)) :
    checkFoundationCertificate t (equalitySubstNode τ υ φ eqChild instChild) =
      some (CheckedFoundationProof.mk Γ (Formula.instantiate υ φ)
        (FoundationProof.equalitySubst p q)) := by
  simp [equalitySubstNode, checkFoundationCertificate,
    checkFoundationCertificateList, heq, hinst, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

theorem existsIntroNode_checks_to [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {child : FoundationCertificateTree Func Pred}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} {τ : Term Func}
    {p : FoundationProof t Γ (Formula.instantiate τ φ)}
    (hchild : checkFoundationCertificate t child =
      some (CheckedFoundationProof.mk Γ (Formula.instantiate τ φ) p)) :
    checkFoundationCertificate t (existsIntroNode φ τ child) =
      some (CheckedFoundationProof.mk Γ (Formula.existsE φ)
        (FoundationProof.existsIntro p)) := by
  simp [existsIntroNode, checkFoundationCertificate,
    checkFoundationCertificateList, hchild, applyFoundationRule,
    applyFoundationRuleUnchecked, FoundationRulePayload.childCount,
    FoundationRulePayload.code, FoundationRuleCode.childCount]

def buildEqualitySymmetryTree (τ υ : Term Func) :
    FoundationCertificateTree Func Pred :=
  equalitySymmNode (hypLeaf [Formula.equal τ υ] (Formula.equal τ υ))

def buildForallElimTree (φ : Formula Func Pred) (τ : Term Func) :
    FoundationCertificateTree Func Pred :=
  forallElimNode τ (hypLeaf [Formula.forallE φ] (Formula.forallE φ))

def buildEqualitySubstitutionTree (τ υ : Term Func)
    (φ : Formula Func Pred) :
    FoundationCertificateTree Func Pred :=
  equalitySubstNode τ υ φ
    (hypLeaf [Formula.equal τ υ, Formula.instantiate τ φ]
      (Formula.equal τ υ))
    (hypLeaf [Formula.equal τ υ, Formula.instantiate τ φ]
      (Formula.instantiate τ φ))

def buildExistsIntroTree (φ : Formula Func Pred) (τ : Term Func) :
    FoundationCertificateTree Func Pred :=
  existsIntroNode φ τ
    (hypLeaf [Formula.instantiate τ φ] (Formula.instantiate τ φ))

theorem buildForallElimTree_eq_example
    (φ : Formula Func Pred) (τ : Term Func) :
    buildForallElimTree φ τ = forallElimCertificateTree φ τ := rfl

theorem buildEqualitySubstitutionTree_eq_example
    (τ υ : Term Func) (φ : Formula Func Pred) :
    buildEqualitySubstitutionTree τ υ φ =
      equalitySubstitutionCertificateTree τ υ φ := rfl

theorem buildEqualitySymmetryTree_checks_to
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) :
    checkFoundationCertificate t
      (buildEqualitySymmetryTree (Pred := Pred) τ υ) =
      some (CheckedFoundationProof.mk
        [@Formula.equal Func Pred τ υ] (Formula.equal υ τ)
        (equalitySymmetryCertificate t τ υ)) :=
  equalitySymmNode_checks_to
    (hypLeaf_checks_to t (List.mem_cons_self _ _))

theorem buildForallElimTree_checks_to
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    checkFoundationCertificate t (buildForallElimTree φ τ) =
      some (CheckedFoundationProof.mk
        [Formula.forallE φ] (Formula.instantiate τ φ)
        (forallElimCertificate t φ τ)) :=
  forallElimNode_checks_to
    (hypLeaf_checks_to t (List.mem_cons_self _ _))

theorem buildEqualitySubstitutionTree_checks_to
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    checkFoundationCertificate t (buildEqualitySubstitutionTree τ υ φ) =
      some (CheckedFoundationProof.mk
        [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
        (Formula.instantiate υ φ)
        (equalitySubstitutionCertificate t τ υ φ)) :=
  equalitySubstNode_checks_to
    (hypLeaf_checks_to t (List.mem_cons_self _ _))
    (hypLeaf_checks_to t
      (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))

theorem buildExistsIntroTree_checks_to
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    checkFoundationCertificate t (buildExistsIntroTree φ τ) =
      some (CheckedFoundationProof.mk
        [Formula.instantiate τ φ] (Formula.existsE φ)
        (existsIntroCertificate t φ τ)) :=
  existsIntroNode_checks_to
    (hypLeaf_checks_to t (List.mem_cons_self _ _))

theorem buildEqualitySymmetryTree_accepted
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) :
    (checkFoundationCertificate t
      (buildEqualitySymmetryTree (Pred := Pred) τ υ)).isSome := by
  rw [buildEqualitySymmetryTree_checks_to]
  rfl

theorem buildForallElimTree_accepted
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    (checkFoundationCertificate t (buildForallElimTree φ τ)).isSome := by
  rw [buildForallElimTree_checks_to]
  rfl

theorem buildEqualitySubstitutionTree_accepted
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    (checkFoundationCertificate t
      (buildEqualitySubstitutionTree τ υ φ)).isSome := by
  rw [buildEqualitySubstitutionTree_checks_to]
  rfl

theorem buildExistsIntroTree_accepted
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    (checkFoundationCertificate t (buildExistsIntroTree φ τ)).isSome := by
  rw [buildExistsIntroTree_checks_to]
  rfl

theorem buildEqualitySymmetryTree_sound
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ] (Formula.equal υ τ) :=
  checkFoundationCertificate_sound (buildEqualitySymmetryTree_checks_to t τ υ)

theorem buildForallElimTree_sound
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [Formula.forallE φ] (Formula.instantiate τ φ) :=
  checkFoundationCertificate_sound (buildForallElimTree_checks_to t φ τ)

theorem buildEqualitySubstitutionTree_sound
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  checkFoundationCertificate_sound
    (buildEqualitySubstitutionTree_checks_to t τ υ φ)

theorem buildExistsIntroTree_sound
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    FoundationThresholdConsequence.{u, v, w} t
      [Formula.instantiate τ φ] (Formula.existsE φ) :=
  checkFoundationCertificate_sound (buildExistsIntroTree_checks_to t φ τ)

end Structure

end Foundation
end Cred
