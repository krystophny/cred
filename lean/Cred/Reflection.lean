/-
  Cred Reflection

  Verified reflection for the foundation certificate checker (issue #522).

  The checker `checkFoundationCertificate` is a decision procedure run inside
  Lean. Its soundness lemmas (`checkFoundationCertificate_sound`,
  `CheckedFoundationProof.sound`) already live at the meta level: Lean, acting
  as the level-(n+1) verifier, proves that a level-n object certificate which
  the checker accepts denotes a genuine object-level consequence.

  This module repackages those meta-level facts into reflection form. Nothing
  here is reproved; the content is the explicit statement "checker acceptance
  reflects object consequence", with the stratification made visible.
-/

import Cred.Foundation.CheckerSoundness

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

/--
  Reflection predicate at the object level: the foundation consequence that a
  successfully checked certificate stands for.

  Reading the stratification: the checker (an executable, level-n artifact)
  produces a `CheckedFoundationProof`; `Reflects` names the level-(n+1)
  proposition that Lean discharges about it.
-/
def CheckedFoundationProof.Reflects
    {t : Credence} (checked : CheckedFoundationProof t Func Pred) : Prop :=
  FoundationThresholdConsequence.{u, v, w} t
    checked.premises checked.conclusion

/--
  Reflection for a single accepted certificate: checker acceptance entails the
  object-level consequence it reflects. A faithful restatement of
  `CheckedFoundationProof.sound` against the `Reflects` predicate.
-/
theorem CheckedFoundationProof.reflects_of_sound
    {t : Credence} (checked : CheckedFoundationProof t Func Pred) :
    checked.Reflects :=
  checked.sound

/--
  The reflection theorem (issue #522): if the checker accepts `tree`, the
  object-level foundation consequence holds for the premises and conclusion of
  the checked proof it returns.

  Stratification: the hypothesis is a level-(n+1) statement *about* the level-n
  checker run; the conclusion is the level-n object consequence. Lean verifies
  the implication, so a higher level certifies the lower one.
-/
theorem checkFoundationCertificate_reflects
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    checked.Reflects :=
  checkFoundationCertificate_sound h

/--
  Reflection stated directly on premises and conclusion, without naming the
  `Reflects` predicate. Convenient object-facing form: an accepted certificate
  yields its consequence judgement.
-/
theorem checkFoundationCertificate_reflects_consequence
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checkFoundationCertificate_sound h

/--
  Existential reflection: if the checker accepts `tree` at all, there is an
  object consequence it reflects. The witness is the checked proof returned.
-/
theorem checkFoundationCertificate_reflects_exists
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    (h : ∃ checked, checkFoundationCertificate t tree = some checked) :
    ∃ checked : CheckedFoundationProof t Func Pred,
      checkFoundationCertificate t tree = some checked ∧
        checked.Reflects := by
  obtain ⟨checked, hchecked⟩ := h
  exact ⟨checked, hchecked, checkFoundationCertificate_reflects hchecked⟩

end Structure

end Foundation
end Cred
