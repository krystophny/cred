/-
  Cred Foundation Certificates

  External certificates carry a serialized header next to the typed payload.
  The envelope checker rejects a node before recursion unless the header,
  payload, and child count agree.
-/

import Cred.Foundation.CheckerSoundness

namespace Cred
namespace Foundation

universe u v w

namespace Structure

inductive FoundationCertificateEnvelope (Func : Type u) (Pred : Type v) where
  | node :
      FoundationCertificateHeader →
      FoundationRulePayload Func Pred →
      List (FoundationCertificateEnvelope Func Pred) →
      FoundationCertificateEnvelope Func Pred
deriving Repr

def FoundationCertificateEnvelope.header :
    FoundationCertificateEnvelope Func Pred → FoundationCertificateHeader
  | .node header _ _ => header

def FoundationCertificateEnvelope.payload :
    FoundationCertificateEnvelope Func Pred → FoundationRulePayload Func Pred
  | .node _ payload _ => payload

def FoundationCertificateEnvelope.children :
    FoundationCertificateEnvelope Func Pred →
      List (FoundationCertificateEnvelope Func Pred)
  | .node _ _ children => children

def FoundationCertificateEnvelope.localShapeOK
    (envelope : FoundationCertificateEnvelope Func Pred) : Bool :=
  envelope.header.matchesPayload envelope.payload &&
    (envelope.children.length == envelope.payload.childCount)

mutual

def FoundationCertificateEnvelope.shapeOK :
    FoundationCertificateEnvelope Func Pred → Bool
  | .node header payload children =>
      header.matchesPayload payload &&
        children.length == payload.childCount &&
          FoundationCertificateEnvelope.shapeOKList children

def FoundationCertificateEnvelope.shapeOKList :
    List (FoundationCertificateEnvelope Func Pred) → Bool
  | [] => true
  | envelope :: envelopes =>
      envelope.shapeOK &&
        FoundationCertificateEnvelope.shapeOKList envelopes

end

mutual

def checkFoundationCertificateEnvelope [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    FoundationCertificateEnvelope Func Pred →
      Option (CheckedFoundationProof t Func Pred)
  | .node header payload children =>
      if header.matchesPayload payload &&
          (children.length == payload.childCount) then
        match checkFoundationCertificateEnvelopeList t children with
        | some checkedChildren => applyFoundationRule t payload checkedChildren
        | none => none
      else
        none

def checkFoundationCertificateEnvelopeList [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) :
    List (FoundationCertificateEnvelope Func Pred) →
      Option (List (CheckedFoundationProof t Func Pred))
  | [] => some []
  | envelope :: envelopes =>
      match checkFoundationCertificateEnvelope t envelope,
          checkFoundationCertificateEnvelopeList t envelopes with
      | some checked, some checkedRest => some (checked :: checkedRest)
      | _, _ => none

end

theorem checkFoundationCertificateEnvelope_sound
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence}
    {envelope : FoundationCertificateEnvelope Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (_h : checkFoundationCertificateEnvelope t envelope = some checked) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checked.sound

theorem checkFoundationCertificateEnvelope_some_localShapeOK
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence}
    {envelope : FoundationCertificateEnvelope Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificateEnvelope t envelope = some checked) :
    envelope.localShapeOK = true := by
  unfold checkFoundationCertificateEnvelope at h
  cases envelope with
  | node header payload children =>
      by_cases hshape :
          (header.matchesPayload payload &&
            (children.length == payload.childCount)) = true
      · simpa [FoundationCertificateEnvelope.localShapeOK,
          FoundationCertificateEnvelope.header,
          FoundationCertificateEnvelope.payload,
          FoundationCertificateEnvelope.children] using hshape
      · simp [hshape] at h

theorem checkFoundationCertificateEnvelope_some_matchesPayload
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence}
    {envelope : FoundationCertificateEnvelope Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificateEnvelope t envelope = some checked) :
    envelope.header.matchesPayload envelope.payload = true := by
  have hshape :=
    checkFoundationCertificateEnvelope_some_localShapeOK
      (t := t) (envelope := envelope) h
  have hsplit :
      envelope.header.matchesPayload envelope.payload = true ∧
        envelope.children.length = envelope.payload.childCount := by
    simpa [FoundationCertificateEnvelope.localShapeOK] using hshape
  exact hsplit.left

end Structure

end Foundation
end Cred
