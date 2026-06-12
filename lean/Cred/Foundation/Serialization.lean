/-
  Cred Foundation Serialization

  Raw certificate headers become trusted headers only after rule-name and
  arity checks.
-/

import Cred.Foundation.Checker

namespace Cred
namespace Foundation

namespace Structure

structure SerializedFoundationHeader where
  ruleName : String
  childCount : Nat
deriving Repr, DecidableEq

def SerializedFoundationHeader.toHeader
    (header : SerializedFoundationHeader) : FoundationCertificateHeader :=
  { ruleName := header.ruleName, childCount := header.childCount }

def SerializedFoundationHeader.decode
    (header : SerializedFoundationHeader) : Option FoundationCertificateHeader :=
  let typed := header.toHeader
  if typed.shapeOK = true then
    some typed
  else
    none

def SerializedFoundationHeader.decodeForPayload
    (header : SerializedFoundationHeader)
    (payload : FoundationRulePayload Func Pred) :
    Option FoundationCertificateHeader :=
  match header.decode with
  | some typed =>
      if typed.matchesPayload payload then
        some typed
      else
        none
  | none => none

theorem SerializedFoundationHeader.decode_ofRuleCode
    (code : FoundationRuleCode) :
    (SerializedFoundationHeader.mk code.name code.childCount).decode =
      some (FoundationCertificateHeader.ofRuleCode code) := by
  cases code <;> rfl

theorem SerializedFoundationHeader.decode_some_shapeOK
    {raw : SerializedFoundationHeader}
    {header : FoundationCertificateHeader}
    (h : raw.decode = some header) :
    header.shapeOK = true := by
  unfold SerializedFoundationHeader.decode at h
  by_cases hshape : raw.toHeader.shapeOK = true
  · simp [hshape] at h
    cases h
    exact hshape
  · simp [hshape] at h

theorem SerializedFoundationHeader.decode_none_of_unknown
    {raw : SerializedFoundationHeader}
    (h : FoundationRuleCode.ofName raw.ruleName = none) :
    raw.decode = none := by
  simp [SerializedFoundationHeader.decode,
    SerializedFoundationHeader.toHeader,
    FoundationCertificateHeader.shapeOK,
    FoundationCertificateHeader.ruleCode?, h]

theorem SerializedFoundationHeader.decode_none_of_bad_childCount
    {raw : SerializedFoundationHeader} {code : FoundationRuleCode}
    (hcode : FoundationRuleCode.ofName raw.ruleName = some code)
    (hcount : raw.childCount ≠ code.childCount) :
    raw.decode = none := by
  simp [SerializedFoundationHeader.decode,
    SerializedFoundationHeader.toHeader,
    FoundationCertificateHeader.shapeOK,
    FoundationCertificateHeader.ruleCode?, hcode, hcount]

theorem SerializedFoundationHeader.decode_some_ruleCode?_isSome
    {raw : SerializedFoundationHeader}
    {header : FoundationCertificateHeader}
    (h : raw.decode = some header) :
    ∃ code, header.ruleCode? = some code :=
  FoundationCertificateHeader.shapeOK_true_ruleCode?_isSome
    (SerializedFoundationHeader.decode_some_shapeOK h)

theorem SerializedFoundationHeader.decode_some_childCount
    {raw : SerializedFoundationHeader}
    {header : FoundationCertificateHeader}
    {code : FoundationRuleCode}
    (h : raw.decode = some header)
    (hcode : header.ruleCode? = some code) :
    header.childCount = code.childCount :=
  FoundationCertificateHeader.childCount_eq_of_shapeOK hcode
    (SerializedFoundationHeader.decode_some_shapeOK h)

theorem SerializedFoundationHeader.decodeForPayload_payload_header
    (payload : FoundationRulePayload Func Pred) :
    (SerializedFoundationHeader.mk
      payload.code.name payload.childCount).decodeForPayload payload =
        some payload.header := by
  cases payload <;> rfl

theorem SerializedFoundationHeader.decodeForPayload_some_decode
    {raw : SerializedFoundationHeader}
    {payload : FoundationRulePayload Func Pred}
    {header : FoundationCertificateHeader}
    (h : raw.decodeForPayload payload = some header) :
    raw.decode = some header := by
  unfold SerializedFoundationHeader.decodeForPayload at h
  cases hdecode : raw.decode with
  | none =>
      simp [hdecode] at h
  | some typed =>
      by_cases hmatch : typed.matchesPayload payload = true
      · simp [hdecode, hmatch] at h
        subst header
        rfl
      · simp [hdecode, hmatch] at h

theorem SerializedFoundationHeader.decodeForPayload_some_matchesPayload
    {raw : SerializedFoundationHeader}
    {payload : FoundationRulePayload Func Pred}
    {header : FoundationCertificateHeader}
    (h : raw.decodeForPayload payload = some header) :
    header.matchesPayload payload = true := by
  unfold SerializedFoundationHeader.decodeForPayload at h
  cases hdecode : raw.decode with
  | none =>
      simp [hdecode] at h
  | some typed =>
      by_cases hmatch : typed.matchesPayload payload = true
      · simp [hdecode, hmatch] at h
        cases h
        exact hmatch
      · simp [hdecode, hmatch] at h

end Structure

end Foundation
end Cred
