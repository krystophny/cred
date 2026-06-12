/-
  Cred Foundation Certificate Examples

  Small envelope checks exercise the external-header boundary.
-/

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

end Structure

end Foundation
end Cred
