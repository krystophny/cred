/-
  Cred Foundation Certificate Examples

  Small envelope checks exercise the external-header boundary.
-/

import Cred.Foundation.Serialization
import Cred.Foundation.Certificate

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def forallElimEnvelope (φ : Formula Func Pred) (τ : Term Func) :
    FoundationCertificateEnvelope Func Pred :=
  .node (FoundationCertificateHeader.ofRuleCode .forallElim) (.forallElim τ)
    [.node (FoundationCertificateHeader.ofRuleCode .hyp)
      (.hyp [Formula.forallE φ] (Formula.forallE φ)) []]

def forallElimEnvelopeBadHeader
    (φ : Formula Func Pred) (τ : Term Func) :
    FoundationCertificateEnvelope Func Pred :=
  .node (FoundationCertificateHeader.ofRuleCode .hyp) (.forallElim τ)
    [.node (FoundationCertificateHeader.ofRuleCode .hyp)
      (.hyp [Formula.forallE φ] (Formula.forallE φ)) []]

def serializedForallElimEnvelope
    (φ : Formula Func Pred) (τ : Term Func) :
    SerializedFoundationEnvelope Func Pred :=
  .node (SerializedFoundationHeader.mk "forallElim" 1) (.forallElim τ)
    [.node (SerializedFoundationHeader.mk "hyp" 0)
      (.hyp [Formula.forallE φ] (Formula.forallE φ)) []]

def serializedForallElimEnvelopeBadHeader
    (φ : Formula Func Pred) (τ : Term Func) :
    SerializedFoundationEnvelope Func Pred :=
  .node (SerializedFoundationHeader.mk "hyp" 0) (.forallElim τ)
    [.node (SerializedFoundationHeader.mk "hyp" 0)
      (.hyp [Formula.forallE φ] (Formula.forallE φ)) []]

def serializedForallElimEnvelopeBadChildCount
    (τ : Term Func) :
    SerializedFoundationEnvelope Func Pred :=
  .node (SerializedFoundationHeader.mk "forallElim" 1) (.forallElim τ)
    []

theorem forallElimEnvelope_localShapeOK
    (φ : Formula Func Pred) (τ : Term Func) :
    (forallElimEnvelope φ τ).localShapeOK = true := by
  simp [forallElimEnvelope, FoundationCertificateEnvelope.localShapeOK,
    FoundationCertificateEnvelope.header, FoundationCertificateEnvelope.payload,
    FoundationCertificateEnvelope.children,
    FoundationCertificateHeader.matchesPayload,
    FoundationCertificateHeader.ofRuleCode,
    FoundationCertificateHeader.ofRuleCode_ruleCode?,
    FoundationCertificateHeader.ruleCode?, FoundationRuleCode.ofName_name,
    FoundationRulePayload.childCount, FoundationRulePayload.code,
    FoundationRuleCode.childCount]

theorem forallElimEnvelope_bad_header_localShapeFails
    (φ : Formula Func Pred) (τ : Term Func) :
    (forallElimEnvelopeBadHeader φ τ).localShapeOK = false := by
  simp [forallElimEnvelopeBadHeader,
    FoundationCertificateEnvelope.localShapeOK,
    FoundationCertificateEnvelope.header, FoundationCertificateEnvelope.payload,
    FoundationCertificateEnvelope.children,
    FoundationCertificateHeader.matchesPayload,
    FoundationCertificateHeader.ofRuleCode,
    FoundationCertificateHeader.ofRuleCode_ruleCode?,
    FoundationCertificateHeader.ruleCode?, FoundationRuleCode.ofName_name,
    FoundationRulePayload.childCount, FoundationRulePayload.code,
    FoundationRuleCode.childCount]

theorem forallElimEnvelope_bad_header_fails
    [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    checkFoundationCertificateEnvelope t
      (forallElimEnvelopeBadHeader φ τ) = none := by
  simp [forallElimEnvelopeBadHeader, checkFoundationCertificateEnvelope,
    FoundationRulePayload.childCount, FoundationRulePayload.code,
    FoundationCertificateHeader.matchesPayload,
    FoundationCertificateHeader.ofRuleCode,
    FoundationCertificateHeader.ofRuleCode_ruleCode?,
    FoundationCertificateHeader.ruleCode?, FoundationRuleCode.ofName_name,
    FoundationRuleCode.childCount]

theorem serialized_forall_elim_header_decodes :
    (SerializedFoundationHeader.mk "forallElim" 1).decode =
      some (FoundationCertificateHeader.ofRuleCode .forallElim) := by
  rfl

theorem serialized_unknown_header_fails :
    (SerializedFoundationHeader.mk "unknownRule" 0).decode = none := by
  rfl

theorem serialized_bad_arity_header_fails :
    (SerializedFoundationHeader.mk "forallElim" 0).decode = none := by
  rfl

theorem serialized_header_decodes_for_matching_payload
    (τ : Term Func) :
    (SerializedFoundationHeader.mk "forallElim" 1).decodeForPayload
        (.forallElim τ : FoundationRulePayload Func Pred) =
      some (FoundationCertificateHeader.ofRuleCode .forallElim) := by
  rfl

theorem serialized_header_fails_for_wrong_payload :
    (SerializedFoundationHeader.mk "forallElim" 1).decodeForPayload
        (.conjElimLeft : FoundationRulePayload Func Pred) = none := by
  rfl

theorem serialized_forall_elim_envelope_decodes
    (φ : Formula Func Pred) (τ : Term Func) :
    (serializedForallElimEnvelope φ τ).decode =
      some (forallElimEnvelope φ τ) := by
  rfl

theorem serialized_forall_elim_envelope_bad_header_fails
    (φ : Formula Func Pred) (τ : Term Func) :
    (serializedForallElimEnvelopeBadHeader φ τ).decode = none := by
  rfl

theorem serialized_forall_elim_envelope_bad_child_count_fails
    (τ : Term Func) :
    (serializedForallElimEnvelopeBadChildCount τ :
      SerializedFoundationEnvelope Func Pred).decode = none := by
  rfl

end Structure

end Foundation
end Cred
