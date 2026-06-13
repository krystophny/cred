/-
  Cred Cond Proof: Admissibility Proof Theory

  The primitive conditional judgment is relational:
    Adm(c; j, e) iff c ⊗ e = j.
  `Cond j e` is the external fiber of this judgment, not a primitive object
  language set former.  This file gives that scalar judgment a proof theory and
  connects closed derivability exactly to membership in `Cond`.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Credence

/-- A scalar admissibility judgment `Adm(c; j, e)`. -/
structure AdmJudgment where
  cond : Credence
  joint : Credence
  evidence : Credence

namespace AdmJudgment

/-- Semantic satisfaction of the admissibility judgment. -/
def Satisfied (J : AdmJudgment) : Prop :=
  J.cond ∈ Cond J.joint J.evidence

/-- The judgment as a `Conditioning` witness. -/
def toConditioning {J : AdmJudgment} (hJ : J.Satisfied) :
    Conditioning J.joint J.evidence where
  condCred := J.cond
  chainRule := hJ

end AdmJudgment

/-- A context of scalar admissibility assumptions. -/
abbrev AdmContext := List AdmJudgment

namespace AdmContext

/-- A scalar context is satisfied when every admissibility assumption holds. -/
def Satisfied (Γ : AdmContext) : Prop :=
  ∀ J ∈ Γ, J.Satisfied

end AdmContext

/-! ## Derivations -/

/-- Proof theory for scalar admissibility judgments. -/
inductive AdmDerivation : AdmContext → AdmJudgment → Prop where
  | hyp {Γ : AdmContext} {J : AdmJudgment} :
      J ∈ Γ → AdmDerivation Γ J
  | weaken {Γ Δ : AdmContext} {J : AdmJudgment} :
      AdmDerivation Γ J →
      (∀ K ∈ Γ, K ∈ Δ) →
      AdmDerivation Δ J
  | cut {Γ : AdmContext} {mid J : AdmJudgment} :
      AdmDerivation Γ mid →
      AdmDerivation (mid :: Γ) J →
      AdmDerivation Γ J
  | chainIntro {Γ : AdmContext} {c j e : Credence} :
      c ⊗ e = j →
      AdmDerivation Γ { cond := c, joint := j, evidence := e }
  | zeroEvidence {Γ : AdmContext} {c : Credence} :
      AdmDerivation Γ { cond := c, joint := 0, evidence := 0 }
  | certainEvidence {Γ : AdmContext} {j : Credence} :
      AdmDerivation Γ { cond := j, joint := j, evidence := 1 }
  | positiveEvidence {Γ : AdmContext} {j e : Credence}
      (he : 0 < e.val) (hle : j.val ≤ e.val) :
      AdmDerivation Γ
        { cond := (conditioning_mk j e he hle).condCred,
          joint := j,
          evidence := e }

namespace AdmDerivation

/-- Scalar admissibility derivations are sound. -/
theorem sound {Γ : AdmContext} {J : AdmJudgment}
    (h : AdmDerivation Γ J) :
    Γ.Satisfied → J.Satisfied := by
  induction h with
  | hyp hJ =>
      intro hΓ
      exact hΓ _ hJ
  | weaken _ hsub ih =>
      intro hΔ
      exact ih (fun K hK => hΔ K (hsub K hK))
  | cut _ _ ihmid ihJ =>
      intro hΓ
      apply ihJ
      intro K hK
      simp only [List.mem_cons] at hK
      rcases hK with rfl | hK
      · exact ihmid hΓ
      · exact hΓ K hK
  | chainIntro hchain =>
      intro _
      exact hchain
  | zeroEvidence =>
      intro _
      exact conditioning_zero_trivial _
  | certainEvidence =>
      intro _
      show _ ⊗ 1 = _
      simp
  | positiveEvidence he hle =>
      intro _
      exact (conditioning_mk _ _ he hle).chainRule

/-- Closed scalar derivability entails membership in the admissible fiber. -/
theorem closed_sound {J : AdmJudgment}
    (h : AdmDerivation [] J) : J.Satisfied :=
  h.sound (by intro K hK; cases hK)

/-- Every member of an admissible fiber has a closed derivation. -/
theorem closed_complete {c j e : Credence}
    (h : c ∈ Cond j e) :
    AdmDerivation [] { cond := c, joint := j, evidence := e } :=
  .chainIntro h

/-- Closed scalar derivability is exactly membership in `Cond`. -/
theorem closed_iff_mem_cond (c j e : Credence) :
    AdmDerivation [] { cond := c, joint := j, evidence := e } ↔
    c ∈ Cond j e :=
  ⟨closed_sound, closed_complete⟩

end AdmDerivation

/-! ## Derived Rules and Boundary Facts -/

/-- Zero evidence with zero joint proves every conditional value. -/
theorem zeroEvidence_derivable (c : Credence) :
    AdmDerivation [] { cond := c, joint := 0, evidence := 0 } :=
  .zeroEvidence

/-- Positive evidence proves the unique division value. -/
theorem positiveEvidence_derivable (j e : Credence)
    (he : 0 < e.val) (hle : j.val ≤ e.val) :
    AdmDerivation []
      { cond := (conditioning_mk j e he hle).condCred,
        joint := j,
        evidence := e } :=
  .positiveEvidence he hle

/-- Closed derivations at positive evidence are unique. -/
theorem closed_unique_of_pos {c₁ c₂ j e : Credence}
    (he : 0 < e.val)
    (h₁ : AdmDerivation [] { cond := c₁, joint := j, evidence := e })
    (h₂ : AdmDerivation [] { cond := c₂, joint := j, evidence := e }) :
    c₁ = c₂ := by
  have hc₁ : c₁.val * e.val = j.val := congrArg val h₁.closed_sound
  have hc₂ : c₂.val * e.val = j.val := congrArg val h₂.closed_sound
  ext
  nlinarith

/-- Closed derivability is nonempty exactly for coherent pairs `j ≤ e`. -/
theorem closed_nonempty_iff (j e : Credence) :
    (∃ c : Credence,
      AdmDerivation [] { cond := c, joint := j, evidence := e }) ↔
    j.val ≤ e.val := by
  constructor
  · rintro ⟨c, h⟩
    exact (cond_nonempty_iff j e).mp ⟨c, h.closed_sound⟩
  · intro hle
    rcases (cond_nonempty_iff j e).mpr hle with ⟨c, hc⟩
    exact ⟨c, AdmDerivation.closed_complete hc⟩

end Credence

end Cred
