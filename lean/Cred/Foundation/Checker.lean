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

structure FoundationCertificateHeader where
  ruleName : String
  childCount : Nat
deriving Repr, DecidableEq

def FoundationCertificateHeader.ruleCode?
    (header : FoundationCertificateHeader) : Option FoundationRuleCode :=
  FoundationRuleCode.ofName header.ruleName

def FoundationCertificateHeader.shapeOK
    (header : FoundationCertificateHeader) : Bool :=
  match header.ruleCode? with
  | some code => header.childCount == code.childCount
  | none => false

def FoundationCertificateHeader.ofRuleCode
    (code : FoundationRuleCode) : FoundationCertificateHeader :=
  { ruleName := code.name, childCount := code.childCount }

theorem FoundationCertificateHeader.ofRuleCode_ruleCode?
    (code : FoundationRuleCode) :
    (FoundationCertificateHeader.ofRuleCode code).ruleCode? = some code := by
  cases code <;> rfl

theorem FoundationCertificateHeader.ofRuleCode_shapeOK
    (code : FoundationRuleCode) :
    (FoundationCertificateHeader.ofRuleCode code).shapeOK = true := by
  cases code <;> rfl

theorem FoundationCertificateHeader.shapeOK_true_ruleCode?_isSome
    {header : FoundationCertificateHeader}
    (h : header.shapeOK = true) :
    ∃ code, header.ruleCode? = some code := by
  unfold FoundationCertificateHeader.shapeOK at h
  cases hcode : header.ruleCode? with
  | none =>
      simp [hcode] at h
  | some code =>
      exact ⟨code, rfl⟩

theorem FoundationCertificateHeader.shapeOK_false_of_ruleCode?_none
    {header : FoundationCertificateHeader}
    (h : header.ruleCode? = none) :
    header.shapeOK = false := by
  simp [FoundationCertificateHeader.shapeOK, h]

theorem FoundationCertificateHeader.childCount_eq_of_shapeOK
    {header : FoundationCertificateHeader} {code : FoundationRuleCode}
    (hcode : header.ruleCode? = some code)
    (hshape : header.shapeOK = true) :
    header.childCount = code.childCount := by
  unfold FoundationCertificateHeader.shapeOK at hshape
  rw [hcode] at hshape
  simpa using hshape

inductive FoundationCertificateTree (Func : Type u) (Pred : Type v) where
  | node :
      FoundationRulePayload Func Pred →
      List (FoundationCertificateTree Func Pred) →
      FoundationCertificateTree Func Pred
deriving Repr

def FoundationCertificateTree.ruleCode :
    FoundationCertificateTree Func Pred → FoundationRuleCode
  | .node payload _ => payload.code

def FoundationCertificateTree.ruleName
    (tree : FoundationCertificateTree Func Pred) : String :=
  tree.ruleCode.name

def FoundationCertificateTree.childCount
    (tree : FoundationCertificateTree Func Pred) : Nat :=
  tree.ruleCode.childCount

def FoundationCertificateTree.children :
    FoundationCertificateTree Func Pred →
      List (FoundationCertificateTree Func Pred)
  | .node _ children => children

def FoundationCertificateTree.header
    (tree : FoundationCertificateTree Func Pred) : FoundationCertificateHeader :=
  { ruleName := tree.ruleName, childCount := tree.children.length }

theorem FoundationCertificateTree.header_ruleCode?
    (tree : FoundationCertificateTree Func Pred) :
    tree.header.ruleCode? = some tree.ruleCode := by
  cases tree
  simp [FoundationCertificateTree.header, FoundationCertificateTree.ruleName,
    FoundationCertificateTree.ruleCode, FoundationCertificateHeader.ruleCode?,
    FoundationRuleCode.ofName_name]

def FoundationCertificateTree.arityMatches
    (tree : FoundationCertificateTree Func Pred) : Prop :=
  tree.children.length = tree.childCount

theorem FoundationCertificateTree.header_shapeOK_true_iff
    (tree : FoundationCertificateTree Func Pred) :
    tree.header.shapeOK = true ↔ tree.arityMatches := by
  cases tree
  simp [FoundationCertificateTree.header, FoundationCertificateTree.ruleName,
    FoundationCertificateTree.ruleCode, FoundationCertificateTree.children,
    FoundationCertificateTree.childCount, FoundationCertificateTree.arityMatches,
    FoundationCertificateHeader.shapeOK, FoundationCertificateHeader.ruleCode?,
    FoundationRuleCode.ofName_name]

mutual

def FoundationCertificateTree.allAritiesMatch :
    FoundationCertificateTree Func Pred → Prop
  | tree@(.node _ children) =>
      tree.arityMatches ∧ FoundationCertificateTree.allAritiesMatchList children

def FoundationCertificateTree.allAritiesMatchList :
    List (FoundationCertificateTree Func Pred) → Prop
  | [] => True
  | tree :: trees =>
      tree.allAritiesMatch ∧ FoundationCertificateTree.allAritiesMatchList trees

end

mutual

def FoundationCertificateTree.shapeOK :
    FoundationCertificateTree Func Pred → Bool
  | .node payload children =>
      (children.length == payload.childCount) &&
        FoundationCertificateTree.shapeOKList children

def FoundationCertificateTree.shapeOKList :
    List (FoundationCertificateTree Func Pred) → Bool
  | [] => true
  | tree :: trees => tree.shapeOK && FoundationCertificateTree.shapeOKList trees

end

mutual

def FoundationCertificateTree.headersShapeOK :
    FoundationCertificateTree Func Pred → Bool
  | tree@(.node _ children) =>
      tree.header.shapeOK && FoundationCertificateTree.headersShapeOKList children

def FoundationCertificateTree.headersShapeOKList :
    List (FoundationCertificateTree Func Pred) → Bool
  | [] => true
  | tree :: trees =>
      tree.headersShapeOK && FoundationCertificateTree.headersShapeOKList trees

end

theorem FoundationCertificateTree.ruleName_roundtrip
    (tree : FoundationCertificateTree Func Pred) :
    FoundationRuleCode.ofName tree.ruleName = some tree.ruleCode := by
  cases tree
  simp [FoundationCertificateTree.ruleName, FoundationCertificateTree.ruleCode,
    FoundationRuleCode.ofName_name]

mutual

def checkFoundationCertificate [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    FoundationCertificateTree Func Pred →
      Option (CheckedFoundationProof t Func Pred)
  | .node payload children => do
      if children.length = payload.childCount then
        let checkedChildren ← checkFoundationCertificateList t children
        applyFoundationRule t payload checkedChildren
      else
        none

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
