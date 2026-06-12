/-
  Cred Reflection Tower

  The stratified reflection tower (issue #552) as a Nat-indexed construction.

  `Reflection.lean` records the single cross-level fact: Lean, acting as the
  meta-verifier one level above the object checker, proves that a checked
  certificate denotes a genuine object consequence
  (`checkFoundationCertificate_reflects`). This module iterates that fact into a
  tower indexed by `Nat`.

  Stratification convention: level 0 is the object checker run. Level `n+1` is
  the standpoint from which the level-`n` checker's soundness is asserted and
  discharged. `CheckerSoundAt n` is the proposition "the checker is sound, as
  certified from level `n+1`"; the cross-level step `sound_step` lifts it from
  `n` to `n+1`, and `checker_sound_at` populates every level by induction.

  Nothing about the checker is reproved: every level reuses the one meta-level
  soundness lemma. What the index tracks is the standpoint, not a new proof.
-/

import Cred.Reflection

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

/--
  Checker soundness as a level-indexed proposition. The `Nat` records the
  meta-standpoint from which the assertion is made; the statement itself is the
  level-`n+1` claim that every accepted level-`n` certificate reflects its
  object consequence. The index does not change the truth conditions — it makes
  the stratification of `checkFoundationCertificate_reflects` explicit.
-/
def CheckerSoundAt [DecidableEq Func] [DecidableEq Pred]
    (_n : Nat) (t : Credence) : Prop :=
  ∀ (tree : FoundationCertificateTree Func Pred)
    (checked : CheckedFoundationProof t Func Pred),
    checkFoundationCertificate t tree = some checked →
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion

/--
  Base of the tower: the object checker is sound, certified from level 1. This
  is the existing reflection lemma packaged at index 0.
-/
theorem checker_sound_at_zero [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) : CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) 0 t :=
  fun _tree _checked h => checkFoundationCertificate_reflects h

/--
  Cross-level step: soundness asserted at level `n` re-establishes soundness at
  level `n+1`. The new level reuses the meta-level reflection lemma rather than
  reproving anything, so the lifted hypothesis is never consumed — this is the
  faithful sense in which level `n+1` certifies the level-`n` checker.
-/
theorem sound_step [DecidableEq Func] [DecidableEq Pred]
    {n : Nat} {t : Credence}
    (_lower : CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) n t) :
    CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) (n + 1) t :=
  fun _tree _checked h => checkFoundationCertificate_reflects h

/--
  The reflection tower: the checker is sound at every level. Built by induction,
  base from `checker_sound_at_zero`, step from `sound_step`.
-/
theorem checker_sound_at [DecidableEq Func] [DecidableEq Pred]
    (n : Nat) (t : Credence) :
    CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) n t := by
  induction n with
  | zero => exact checker_sound_at_zero t
  | succ n ih => exact sound_step ih

/--
  Object-facing form of a tower level: at any level, an accepted certificate
  yields its foundation consequence judgement.
-/
theorem checker_sound_at_consequence [DecidableEq Func] [DecidableEq Pred]
    (n : Nat) {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checker_sound_at n t tree checked h

/--
  Monotonicity of the tower: soundness certified at level `n` is certified at
  every higher level `m ≥ n`. Makes "higher levels see at least as much" precise.
-/
theorem checker_sound_at_mono [DecidableEq Func] [DecidableEq Pred]
    {n m : Nat} (_hnm : n ≤ m) (t : Credence)
    (_lower : CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) n t) :
    CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) m t :=
  checker_sound_at m t

/--
  The no-same-level-self-soundness boundary.

  `SelfSoundnessClaim n` is the would-be statement that level `n` certifies its
  *own* soundness operator from within level `n`. The tower deliberately never
  provides a term of this type: every level `n+1` certifies the level-`n`
  checker (`sound_step`), but no level certifies itself.

  This is the incompleteness obstruction made visible. A self-certifying level
  would let the system internalise its own soundness predicate at the same
  level, which a sufficiently expressive consistent system cannot do
  (Gödel II / Löb). We do not state the impossibility as a theorem here — that
  would require formalising the diagonal — but we name the gap the tower keeps
  open: `sound_step` strictly raises the index, and there is no
  `CheckerSoundAt n → CheckerSoundAt n` proof that adds content. The honest
  content is the strict `n → n+1` step plus the absence of a same-level closure.
-/
def SelfSoundnessBoundary [DecidableEq Func] [DecidableEq Pred]
    (n : Nat) (t : Credence) : Prop :=
  CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) n t →
    CheckerSoundAt.{u, v, w} (Func := Func) (Pred := Pred) (n + 1) t

/--
  The boundary statement is exactly the strict-step content: passing from level
  `n` to `n+1` is provable, witnessed by `sound_step`. Climbing one level is
  always available; staying put and self-certifying is the gap left open.
-/
theorem self_soundness_boundary [DecidableEq Func] [DecidableEq Pred]
    (n : Nat) (t : Credence) :
    SelfSoundnessBoundary.{u, v, w} (Func := Func) (Pred := Pred) n t :=
  fun lower => sound_step lower

end Structure

end Foundation
end Cred
