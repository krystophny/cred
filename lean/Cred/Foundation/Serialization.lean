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

end Structure

end Foundation
end Cred
