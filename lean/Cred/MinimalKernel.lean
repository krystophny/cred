/-
  Cred Minimal Trusted Kernel

  This module pins the minimal trusted surface for the foundation proof
  system in one place. It re-exports the existing definitions and the
  existing soundness theorem; it introduces no new axioms and no new
  trusted code. Everything below is a thin wrapper over names already
  defined and verified in `Cred.Foundation.Checker` and
  `Cred.Foundation.CheckerSoundness`.

  Trusted base (what soundness ultimately rests on):
  - `Foundation.Structure.evalFormula` and `FoundationThresholdConsequence`
    fix the intended meaning a checked certificate must satisfy.
  - `Foundation.Structure.FoundationProof` is the inductive whose
    constructors are the only admissible inference steps; its rule-by-rule
    soundness lives in `FoundationProof.sound`.

  Checked, not trusted (each is a total function or theorem over the base):
  - `CheckedFoundationProof` carries a `FoundationProof` together with its
    premises and conclusion, so possessing one is already evidence.
  - `applyFoundationRule` is the one-step checker: it consumes a rule
    payload and already-checked children, and returns a checked proof only
    when the constructor side-conditions hold.
  - `checkFoundationCertificate` is the recursive driver: it walks a
    certificate tree, checks each node via `applyFoundationRule`, and
    returns a `CheckedFoundationProof` for the root or `none`.
  - `checkFoundationCertificate_sound` is the end-to-end guarantee: any
    accepted certificate yields a true `FoundationThresholdConsequence`.

  To audit the kernel one reviews exactly the names re-exported here plus
  the constructors of `FoundationProof`. Nothing else is trusted.
-/

import Cred.Foundation.CheckerSoundness

namespace Cred
namespace MinimalKernel

universe u v w

open Cred.Foundation
open Cred.Foundation.Structure

-- Certificate carrier: a foundation proof with its premises and conclusion.
export Cred.Foundation.Structure (CheckedFoundationProof)

-- One-step rule checker and its payload/tree inputs.
export Cred.Foundation.Structure
  (FoundationRulePayload applyFoundationRule
   FoundationCertificateTree checkFoundationCertificate)

-- End-to-end soundness, reused verbatim (not reproved here).
export Cred.Foundation.Structure (checkFoundationCertificate_sound)

variable {Func : Type u} {Pred : Type v}

/-- A checked certificate already witnesses the threshold consequence it
    claims. Convenience restatement of the carrier's own soundness. -/
theorem CheckedFoundationProof.consequence
    {t : Credence} (checked : CheckedFoundationProof t Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checked.sound

/-- Accepting a certificate tree yields a checked proof whose conclusion is
    a true consequence of its premises. Packaged form of the trusted result. -/
theorem accepted_certificate_sound
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checkFoundationCertificate_sound h

end MinimalKernel
end Cred
