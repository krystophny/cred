/-
  Cred Foundation Checker

  A checker step applies one rule payload to already checked children. Success
  returns a typed `FoundationProof`; failure returns `none`.
-/

import Cred.Foundation.RuleCode

namespace Cred
namespace Foundation

universe u v

namespace Structure

structure CheckedFoundationProof (t : Credence)
    (Func : Type u) (Pred : Type v) where
  premises : List (Formula Func Pred)
  conclusion : Formula Func Pred
  proof : FoundationProof t premises conclusion

inductive FoundationRulePayload (Func : Type u) (Pred : Type v) where
  | hyp : List (Formula Func Pred) → Formula Func Pred → FoundationRulePayload Func Pred
  | weaken : List (Formula Func Pred) → FoundationRulePayload Func Pred
  | cut : Formula Func Pred → FoundationRulePayload Func Pred
  | conjElimLeft : FoundationRulePayload Func Pred
  | conjElimRight : FoundationRulePayload Func Pred
  | disjIntroLeft : Formula Func Pred → FoundationRulePayload Func Pred
  | disjIntroRight : Formula Func Pred → FoundationRulePayload Func Pred
  | equalityRefl : List (Formula Func Pred) → Term Func → FoundationRulePayload Func Pred
  | equalitySymm : FoundationRulePayload Func Pred
  | equalityTrans : FoundationRulePayload Func Pred
  | equalitySubst : Term Func → Term Func → Formula Func Pred → FoundationRulePayload Func Pred
  | forallElim : Term Func → FoundationRulePayload Func Pred
  | existsIntro : Formula Func Pred → Term Func → FoundationRulePayload Func Pred
deriving Repr

def FoundationRulePayload.code :
    FoundationRulePayload Func Pred → FoundationRuleCode
  | .hyp _ _ => .hyp
  | .weaken _ => .weaken
  | .cut _ => .cut
  | .conjElimLeft => .conjElimLeft
  | .conjElimRight => .conjElimRight
  | .disjIntroLeft _ => .disjIntroLeft
  | .disjIntroRight _ => .disjIntroRight
  | .equalityRefl _ _ => .equalityRefl
  | .equalitySymm => .equalitySymm
  | .equalityTrans => .equalityTrans
  | .equalitySubst _ _ _ => .equalitySubst
  | .forallElim _ => .forallElim
  | .existsIntro _ _ => .existsIntro

def FoundationRulePayload.childCount
    (payload : FoundationRulePayload Func Pred) : Nat :=
  payload.code.childCount

theorem FoundationRulePayload.childCount_eq_code
    (payload : FoundationRulePayload Func Pred) :
    payload.childCount = payload.code.childCount := rfl

def applyFoundationRuleUnchecked [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    FoundationRulePayload Func Pred →
      List (CheckedFoundationProof t Func Pred) →
      Option (CheckedFoundationProof t Func Pred)
  | .hyp Γ φ, [] =>
      if h : φ ∈ Γ then
        some (CheckedFoundationProof.mk Γ φ
          (FoundationProof.base (Proof.hyp h)))
      else
        none
  | .weaken Δ, [⟨Γ, φ, p⟩] =>
      if hsub : ∀ ψ ∈ Γ, ψ ∈ Δ then
        some (CheckedFoundationProof.mk Δ φ
          (FoundationProof.weaken p hsub))
      else
        none
  | .cut mid, [⟨Γ, φ, p⟩, ⟨Δ, ψ, q⟩] =>
      if hp : φ = mid then
        if hq : Δ = mid :: Γ then
          some (CheckedFoundationProof.mk Γ ψ
            (by
              cases hp
              cases hq
              exact FoundationProof.cut p q))
        else
          none
      else
        none
  | .conjElimLeft, [⟨Γ, conclusion, p⟩] =>
      match conclusion with
      | .conj φ ψ =>
          some (CheckedFoundationProof.mk Γ φ
            (FoundationProof.conjElimLeft p))
      | _ => none
  | .conjElimRight, [⟨Γ, conclusion, p⟩] =>
      match conclusion with
      | .conj φ ψ =>
          some (CheckedFoundationProof.mk Γ ψ
            (FoundationProof.conjElimRight p))
      | _ => none
  | .disjIntroLeft ψ, [⟨Γ, φ, p⟩] =>
      some (CheckedFoundationProof.mk Γ (.disj φ ψ)
        (FoundationProof.disjIntroLeft p))
  | .disjIntroRight φ, [⟨Γ, ψ, p⟩] =>
      some (CheckedFoundationProof.mk Γ (.disj φ ψ)
        (FoundationProof.disjIntroRight p))
  | .equalityRefl Γ τ, [] =>
      some (CheckedFoundationProof.mk Γ (.equal τ τ)
        (FoundationProof.equalityRefl τ))
  | .equalitySymm, [⟨Γ, conclusion, p⟩] =>
      match conclusion with
      | .equal τ υ =>
          some (CheckedFoundationProof.mk Γ (.equal υ τ)
            (FoundationProof.equalitySymm p))
      | _ => none
  | .equalityTrans, [⟨Γ, conclusionP, p⟩, ⟨Δ, conclusionQ, q⟩] =>
      match conclusionP, conclusionQ with
      | .equal τ υ, .equal υ' χ =>
          if hctx : Γ = Δ then
            if hmid : υ = υ' then
              some (CheckedFoundationProof.mk Γ (.equal τ χ)
                (by
                  cases hctx
                  cases hmid
                  exact FoundationProof.equalityTrans p q))
            else
              none
          else
            none
      | _, _ => none
  | .equalitySubst τ υ φ, [⟨Γ, eqConclusion, p⟩, ⟨Δ, φConclusion, q⟩] =>
      if hp : eqConclusion = .equal τ υ then
        if hq : φConclusion = Formula.instantiate τ φ then
          if hctx : Γ = Δ then
            some (CheckedFoundationProof.mk Γ (Formula.instantiate υ φ)
              (by
                cases hp
                cases hq
                cases hctx
                exact FoundationProof.equalitySubst p q))
          else
            none
        else
          none
      else
        none
  | .forallElim τ, [⟨Γ, conclusion, p⟩] =>
      match conclusion with
      | .forallE φ =>
          some (CheckedFoundationProof.mk Γ (Formula.instantiate τ φ)
            (FoundationProof.forallElim p))
      | _ => none
  | .existsIntro φ τ, [⟨Γ, conclusion, p⟩] =>
      if h : conclusion = Formula.instantiate τ φ then
        some (CheckedFoundationProof.mk Γ (.existsE φ)
          (by
            cases h
            exact FoundationProof.existsIntro p))
      else
        none
  | _, _ => none

def applyFoundationRule [DecidableEq Func] [DecidableEq Pred]
    (t : Credence)
    (payload : FoundationRulePayload Func Pred)
    (children : List (CheckedFoundationProof t Func Pred)) :
    Option (CheckedFoundationProof t Func Pred) :=
  if children.length = payload.childCount then
    applyFoundationRuleUnchecked t payload children
  else
    none

theorem applyFoundationRule_some_childCount
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {payload : FoundationRulePayload Func Pred}
    {children : List (CheckedFoundationProof t Func Pred)}
    {checked : CheckedFoundationProof t Func Pred}
    (h : applyFoundationRule t payload children = some checked) :
    children.length = payload.childCount := by
  by_cases hcount : children.length = payload.childCount
  · exact hcount
  · simp [applyFoundationRule, hcount] at h

inductive FoundationCertificateTree (Func : Type u) (Pred : Type v) where
  | node :
      FoundationRulePayload Func Pred →
      List (FoundationCertificateTree Func Pred) →
      FoundationCertificateTree Func Pred
deriving Repr

mutual

def checkFoundationCertificate [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    FoundationCertificateTree Func Pred →
      Option (CheckedFoundationProof t Func Pred)
  | .node payload children => do
      let checkedChildren ← checkFoundationCertificateList t children
      applyFoundationRule t payload checkedChildren

def checkFoundationCertificateList [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    List (FoundationCertificateTree Func Pred) →
      Option (List (CheckedFoundationProof t Func Pred))
  | [] => some []
  | child :: children => do
      let checkedChild ← checkFoundationCertificate t child
      let checkedChildren ← checkFoundationCertificateList t children
      some (checkedChild :: checkedChildren)

end

end Structure

end Foundation
end Cred
