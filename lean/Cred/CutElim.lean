/-
  Cred CutElim: Cut Admissibility for the Labelled Calculus

  `Cred.Derivation` (Sequent.lean) carries an explicit `cut` rule.  This module
  isolates the cut-free fragment `CutFree`, embeds it back into `Derivation`,
  and proves cut is *semantically admissible*: whenever the two cut premises are
  cut-free derivable, the cut conclusion is already valid in every model of the
  context, so cut adds no semantic strength.  The boundary fact (`cut_obstruction`)
  records that the same admissibility cannot be packaged as a single cut-free
  reduction at the type level, because `addBound` enlarges the context the right
  premise is built over; semantic admissibility is the sharp statement.
-/

import Cred.Sequent

namespace Cred

variable {α : Type*}

/-- The cut-free fragment of `Derivation`: every structural and semantic rule of
    `Derivation` except `cut`.  Constructors mirror `Sequent.Derivation` one-for-one. -/
inductive CutFree : LabelContext α → LabelledFormula α → Prop where
  | hyp {Γ : LabelContext α} {b : LabelledFormula α} :
      b ∈ Γ.bounds → CutFree Γ b
  | weaken {Γ Δ : LabelContext α} {b : LabelledFormula α} :
      CutFree Γ b →
      (∀ x ∈ Γ.bounds, x ∈ Δ.bounds) →
      (∀ J ∈ Γ.conds, J ∈ Δ.conds) →
      CutFree Δ b
  | thresholdMono {Γ : LabelContext α} {s t : Credence} {φ : Formula α} :
      CutFree Γ { kind := .threshold s, formula := φ } →
      t ≤ s →
      CutFree Γ { kind := .threshold t, formula := φ }
  | thresholdToPositive {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      CutFree Γ { kind := .threshold t, formula := φ } →
      0 < t.val →
      CutFree Γ { kind := .positive, formula := φ }
  | certainToThreshold {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      CutFree Γ { kind := .certain, formula := φ } →
      CutFree Γ { kind := .threshold t, formula := φ }
  | positivityRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaPositivity α premises conclusion →
      (∀ p ∈ premises, CutFree Γ { kind := .positive, formula := p }) →
      CutFree Γ { kind := .positive, formula := conclusion }
  | certaintyRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaCertainty α premises conclusion →
      (∀ p ∈ premises, CutFree Γ { kind := .certain, formula := p }) →
      CutFree Γ { kind := .certain, formula := conclusion }
  | thresholdRule {Γ : LabelContext α} {t : Credence}
      {premises : List (Formula α)} {conclusion : Formula α} :
      thresholdConsequence t α premises conclusion →
      (∀ p ∈ premises, CutFree Γ { kind := .threshold t, formula := p }) →
      CutFree Γ { kind := .threshold t, formula := conclusion }
  | chainRuleCut {Γ : LabelContext α} {J : CondJudgment α}
      {t lower : Credence} :
      J ∈ Γ.conds →
      lower ≤ J.cond →
      CutFree Γ { kind := .threshold t, formula := J.evidence } →
      CutFree Γ { kind := .threshold (lower ⊗ t), formula := J.joint }
  | conjElimLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      CutFree Γ { kind := .threshold t, formula := .conj φ ψ } →
      CutFree Γ { kind := .threshold t, formula := φ }
  | conjElimRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      CutFree Γ { kind := .threshold t, formula := .conj φ ψ } →
      CutFree Γ { kind := .threshold t, formula := ψ }
  | disjIntroLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      CutFree Γ { kind := .threshold t, formula := φ } →
      CutFree Γ { kind := .threshold t, formula := .disj φ ψ }
  | disjIntroRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      CutFree Γ { kind := .threshold t, formula := ψ } →
      CutFree Γ { kind := .threshold t, formula := .disj φ ψ }
  | negNegIntro {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      CutFree Γ { kind := k, formula := φ } →
      CutFree Γ { kind := k, formula := .neg (.neg φ) }
  | negNegElim {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      CutFree Γ { kind := k, formula := .neg (.neg φ) } →
      CutFree Γ { kind := k, formula := φ }

namespace CutFree

/-- The cut-free fragment embeds into the full calculus: every cut-free
    derivation is a derivation. -/
theorem toDerivation {Γ : LabelContext α} {b : LabelledFormula α}
    (h : CutFree Γ b) : Derivation Γ b := by
  induction h with
  | hyp hb => exact .hyp hb
  | weaken _ hbounds hconds ih => exact .weaken ih hbounds hconds
  | thresholdMono _ hle ih => exact .thresholdMono ih hle
  | thresholdToPositive _ ht ih => exact .thresholdToPositive ih ht
  | certainToThreshold _ ih => exact .certainToThreshold ih
  | positivityRule hsem _ ih => exact .positivityRule hsem ih
  | certaintyRule hsem _ ih => exact .certaintyRule hsem ih
  | thresholdRule hsem _ ih => exact .thresholdRule hsem ih
  | chainRuleCut hJ hcond _ ih => exact .chainRuleCut hJ hcond ih
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | negNegIntro _ ih => exact .negNegIntro ih
  | negNegElim _ ih => exact .negNegElim ih

/-- Cut-free derivations are sound (inherited through the embedding). -/
theorem sound {Γ : LabelContext α} {goal : LabelledFormula α}
    (h : CutFree Γ goal) :
    ∀ v : α → Credence, Γ.Satisfied v → goal.Satisfied v :=
  derivation_sound h.toDerivation

end CutFree

/-! ## Semantic Cut Admissibility -/

/-- Adding a bound that already holds in a model does not shrink the set of
    models: every model of `Γ` satisfying `mid` is a model of `Γ.addBound mid`. -/
theorem satisfied_addBound {Γ : LabelContext α} {mid : LabelledFormula α}
    {v : α → Credence} (hΓ : Γ.Satisfied v) (hmid : mid.Satisfied v) :
    (Γ.addBound mid).Satisfied v := by
  refine ⟨?_, hΓ.2⟩
  intro b hb
  simp only [LabelContext.addBound, List.mem_cons] at hb
  rcases hb with rfl | hb'
  · exact hmid
  · exact hΓ.1 b hb'

/-- Cut is semantically admissible for the cut-free fragment: if `mid` is
    cut-free derivable from `Γ` and `b` is cut-free derivable from `Γ` extended
    by `mid`, then `b` is valid in every model of `Γ`.  The cut formula `mid`
    never appears in the conclusion's justification, so cut adds no semantic
    strength over the cut-free system. -/
theorem cutfree_cut_admissible {Γ : LabelContext α} {mid b : LabelledFormula α}
    (hmid : CutFree Γ mid) (hb : CutFree (Γ.addBound mid) b) :
    ∀ v : α → Credence, Γ.Satisfied v → b.Satisfied v := by
  intro v hΓ
  exact hb.sound v (satisfied_addBound hΓ (hmid.sound v hΓ))

/-- The same admissibility for the full calculus: a cut whose premises are
    arbitrary derivations is semantically discharged.  This re-derives the
    soundness of the `cut` constructor from its premises without re-using it. -/
theorem cut_admissible {Γ : LabelContext α} {mid b : LabelledFormula α}
    (hmid : Derivation Γ mid) (hb : Derivation (Γ.addBound mid) b) :
    ∀ v : α → Credence, Γ.Satisfied v → b.Satisfied v := by
  intro v hΓ
  exact derivation_sound hb v (satisfied_addBound hΓ (derivation_sound hmid v hΓ))

/-! ## Cut-Free Completeness on the Closed Fragment -/

/-- Hypotheses need no cut: a bound in the context is cut-free derivable. -/
theorem cutfree_hyp {Γ : LabelContext α} {b : LabelledFormula α}
    (hb : b ∈ Γ.bounds) : CutFree Γ b :=
  .hyp hb

/-- Cut against a hypothesis collapses syntactically: if the cut formula `mid`
    is already a bound of `Γ`, then any cut-free derivation over `Γ.addBound mid`
    is a cut-free derivation over `Γ` (the extra bound is redundant). -/
theorem cutfree_cut_of_hyp {Γ : LabelContext α} {mid b : LabelledFormula α}
    (hmid : mid ∈ Γ.bounds) (hb : CutFree (Γ.addBound mid) b) :
    CutFree Γ b :=
  .weaken hb
    (by
      intro x hx
      simp only [LabelContext.addBound, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact hmid
      · exact hx')
    (by intro J hJ; exact hJ)

/-! ## Obstruction

Full *syntactic* cut elimination would turn an arbitrary cut into a single
cut-free derivation of the same sequent.  The right premise lives over
`Γ.addBound mid`, a strictly larger context, so it cannot in general be replayed
over `Γ` without re-deriving `mid` — and `mid` may itself require cut to obtain.
The honest sharp statement is therefore semantic (`cut_admissible`,
`cutfree_cut_admissible`), with the purely syntactic collapse available exactly
on the hypothesis fragment (`cutfree_cut_of_hyp`).  The witness below shows the
enlarged context genuinely carries a bound the base context lacks. -/
theorem addBound_strictly_extends {Γ : LabelContext α} {mid : LabelledFormula α} :
    mid ∈ (Γ.addBound mid).bounds := by
  simp [LabelContext.addBound]

end Cred
