/-
  Cred Sequent: Labelled External Conditioning Calculus

  This module is the proof-layer interface.  Formula has no implication
  constructor.  Conditioning appears only as a side judgment
  `cond ∈ Cond(joint,evidence)`, and the chain rule is used as a labelled
  cut on bounds.
-/

import Cred.Threshold

namespace Cred

open Credence

variable {α : Type*}

/-! ## Labels and Contexts -/

/-- A label says how a formula is designated. -/
inductive LabelKind where
  | positive : LabelKind
  | certain : LabelKind
  | threshold : Credence → LabelKind

namespace LabelKind

/-- Semantic satisfaction of a label by a credence. -/
def Satisfied : LabelKind → Credence → Prop
  | positive, c => 0 < c.val
  | certain, c => c = 1
  | threshold t, c => t ≤ c

end LabelKind

/-- A labelled formula. -/
structure LabelledFormula (α : Type*) where
  kind : LabelKind
  formula : Formula α

namespace LabelledFormula

/-- A valuation satisfies a labelled formula when the formula value satisfies
    the label. -/
def Satisfied (v : α → Credence) (b : LabelledFormula α) : Prop :=
  b.kind.Satisfied (evalCred v b.formula)

end LabelledFormula

/-- A conditioning side judgment.  It is external to Formula. -/
structure CondJudgment (α : Type*) where
  cond : Credence
  joint : Formula α
  evidence : Formula α

namespace CondJudgment

/-- A valuation satisfies a conditioning side judgment when the supplied
    conditional value is admissible for the evaluated joint and evidence. -/
def Satisfied (v : α → Credence) (J : CondJudgment α) : Prop :=
  J.cond ∈ Cond (evalCred v J.joint) (evalCred v J.evidence)

theorem chain_rule (v : α → Credence) {J : CondJudgment α}
    (hJ : J.Satisfied v) :
    J.cond ⊗ evalCred v J.evidence = evalCred v J.joint :=
  hJ

end CondJudgment

/-- A labelled sequent context: formula bounds plus external conditioning
    side judgments. -/
structure LabelContext (α : Type*) where
  bounds : List (LabelledFormula α)
  conds : List (CondJudgment α)

namespace LabelContext

/-- A valuation satisfies a context when it satisfies every bound and every
    conditioning side judgment. -/
def Satisfied (v : α → Credence) (Γ : LabelContext α) : Prop :=
  (∀ b ∈ Γ.bounds, b.Satisfied v) ∧ (∀ J ∈ Γ.conds, J.Satisfied v)

/-- Add a formula bound to a context. -/
def addBound (Γ : LabelContext α) (b : LabelledFormula α) : LabelContext α :=
  { bounds := b :: Γ.bounds, conds := Γ.conds }

end LabelContext

/-- The empty labelled context. -/
def emptyContext (α : Type*) : LabelContext α :=
  { bounds := [], conds := [] }

/-- Context generated from ordinary formula premises under one label. -/
def formulaContext (k : LabelKind) (premises : List (Formula α)) :
    LabelContext α :=
  { bounds := premises.map (fun φ => { kind := k, formula := φ }), conds := [] }

/-! ## Basic Order Lemmas -/

theorem conj_mono (a b c d : Credence) (hab : a ≤ b) (hcd : c ≤ d) :
    a ⊗ c ≤ b ⊗ d := by
  change a.val * c.val ≤ b.val * d.val
  calc
    a.val * c.val ≤ b.val * c.val := by
      exact mul_le_mul_of_nonneg_right hab c.nonneg
    _ ≤ b.val * d.val := by
      exact mul_le_mul_of_nonneg_left hcd b.nonneg

theorem conj_le_left (a b : Credence) : a ⊗ b ≤ a := by
  change a.val * b.val ≤ a.val
  calc
    a.val * b.val ≤ a.val * 1 := by
      exact mul_le_mul_of_nonneg_left b.le_one a.nonneg
    _ = a.val := by ring

theorem conj_le_right (a b : Credence) : a ⊗ b ≤ b := by
  rw [Credence.conj_comm]
  exact conj_le_left b a

theorem le_disj_left (a b : Credence) : a ≤ a ⊔ b := by
  change a.val ≤ (a ⊔ b).val
  rw [Credence.disj_val]
  have h : 0 ≤ b.val * (1 - a.val) :=
    mul_nonneg b.nonneg (by linarith [a.le_one])
  linarith

theorem le_disj_right (a b : Credence) : b ≤ a ⊔ b := by
  rw [Credence.disj_comm]
  exact le_disj_left b a

/-! ## Derivations -/

/-- Labelled derivations.  The rules are structural plus semantic imports from
    the already-verified consequence relations.  Conditioning is only a side
    judgment, used by `chainRuleCut`. -/
inductive Derivation : LabelContext α → LabelledFormula α → Prop where
  | hyp {Γ : LabelContext α} {b : LabelledFormula α} :
      b ∈ Γ.bounds → Derivation Γ b
  | weaken {Γ Δ : LabelContext α} {b : LabelledFormula α} :
      Derivation Γ b →
      (∀ x ∈ Γ.bounds, x ∈ Δ.bounds) →
      (∀ J ∈ Γ.conds, J ∈ Δ.conds) →
      Derivation Δ b
  | cut {Γ : LabelContext α} {mid b : LabelledFormula α} :
      Derivation Γ mid →
      Derivation (Γ.addBound mid) b →
      Derivation Γ b
  | thresholdMono {Γ : LabelContext α} {s t : Credence} {φ : Formula α} :
      Derivation Γ { kind := .threshold s, formula := φ } →
      t ≤ s →
      Derivation Γ { kind := .threshold t, formula := φ }
  | thresholdToPositive {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      Derivation Γ { kind := .threshold t, formula := φ } →
      0 < t.val →
      Derivation Γ { kind := .positive, formula := φ }
  | certainToThreshold {Γ : LabelContext α} {t : Credence} {φ : Formula α} :
      Derivation Γ { kind := .certain, formula := φ } →
      Derivation Γ { kind := .threshold t, formula := φ }
  | positivityRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaPositivity α premises conclusion →
      (∀ p ∈ premises, Derivation Γ { kind := .positive, formula := p }) →
      Derivation Γ { kind := .positive, formula := conclusion }
  | certaintyRule {Γ : LabelContext α} {premises : List (Formula α)}
      {conclusion : Formula α} :
      formulaCertainty α premises conclusion →
      (∀ p ∈ premises, Derivation Γ { kind := .certain, formula := p }) →
      Derivation Γ { kind := .certain, formula := conclusion }
  | thresholdRule {Γ : LabelContext α} {t : Credence}
      {premises : List (Formula α)} {conclusion : Formula α} :
      thresholdConsequence t α premises conclusion →
      (∀ p ∈ premises, Derivation Γ { kind := .threshold t, formula := p }) →
      Derivation Γ { kind := .threshold t, formula := conclusion }
  | chainRuleCut {Γ : LabelContext α} {J : CondJudgment α}
      {t lower : Credence} :
      J ∈ Γ.conds →
      lower ≤ J.cond →
      Derivation Γ { kind := .threshold t, formula := J.evidence } →
      Derivation Γ { kind := .threshold (lower ⊗ t), formula := J.joint }
  | conjElimLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Derivation Γ { kind := .threshold t, formula := .conj φ ψ } →
      Derivation Γ { kind := .threshold t, formula := φ }
  | conjElimRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Derivation Γ { kind := .threshold t, formula := .conj φ ψ } →
      Derivation Γ { kind := .threshold t, formula := ψ }
  | disjIntroLeft {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Derivation Γ { kind := .threshold t, formula := φ } →
      Derivation Γ { kind := .threshold t, formula := .disj φ ψ }
  | disjIntroRight {Γ : LabelContext α} {t : Credence} {φ ψ : Formula α} :
      Derivation Γ { kind := .threshold t, formula := ψ } →
      Derivation Γ { kind := .threshold t, formula := .disj φ ψ }
  | negNegIntro {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      Derivation Γ { kind := k, formula := φ } →
      Derivation Γ { kind := k, formula := .neg (.neg φ) }
  | negNegElim {Γ : LabelContext α} {k : LabelKind} {φ : Formula α} :
      Derivation Γ { kind := k, formula := .neg (.neg φ) } →
      Derivation Γ { kind := k, formula := φ }

/-! ## Soundness -/

theorem derivation_sound {Γ : LabelContext α} {goal : LabelledFormula α}
    (h : Derivation Γ goal) :
    ∀ v : α → Credence, Γ.Satisfied v → goal.Satisfied v := by
  induction h with
  | hyp hb =>
      intro v hΓ
      exact hΓ.1 _ hb
  | weaken h hbounds hconds ih =>
      intro v hΔ
      exact ih v ⟨fun b hb => hΔ.1 b (hbounds b hb),
        fun J hJ => hΔ.2 J (hconds J hJ)⟩
  | cut hmid hgoal ihmid ihgoal =>
      intro v hΓ
      have hmid_sat := ihmid v hΓ
      apply ihgoal v
      constructor
      · intro b hb
        simp only [LabelContext.addBound, List.mem_cons] at hb
        rcases hb with rfl | hb'
        · exact hmid_sat
        · exact hΓ.1 b hb'
      · exact hΓ.2
  | thresholdMono hder hle ih =>
      intro v hΓ
      exact le_trans hle (ih v hΓ)
  | thresholdToPositive hder ht ih =>
      intro v hΓ
      exact lt_of_lt_of_le ht (ih v hΓ)
  | certainToThreshold hder ih =>
      intro v hΓ
      have hc := ih v hΓ
      simp [LabelledFormula.Satisfied, LabelKind.Satisfied] at hc ⊢
      rw [hc]
      exact Credence.le_one' _
  | positivityRule hsem hprems ihprems =>
      intro v hΓ
      exact hsem v (fun p hp => ihprems p hp v hΓ)
  | certaintyRule hsem hprems ihprems =>
      intro v hΓ
      exact hsem v (fun p hp => ihprems p hp v hΓ)
  | thresholdRule hsem hprems ihprems =>
      intro v hΓ
      exact hsem v (fun p hp => ihprems p hp v hΓ)
  | chainRuleCut hJ hcond hEvidence ih =>
      intro v hΓ
      have hcondSat := hΓ.2 _ hJ
      have hEvidenceSat := ih v hΓ
      have hchain := CondJudgment.chain_rule v hcondSat
      change _ ≤ evalCred v _
      rw [← hchain]
      exact conj_mono _ _ _ _ hcond hEvidenceSat
  | conjElimLeft hder ih =>
      intro v hΓ
      exact le_trans (ih v hΓ) (conj_le_left _ _)
  | conjElimRight hder ih =>
      intro v hΓ
      exact le_trans (ih v hΓ) (conj_le_right _ _)
  | disjIntroLeft hder ih =>
      intro v hΓ
      exact le_trans (ih v hΓ) (le_disj_left _ _)
  | disjIntroRight hder ih =>
      intro v hΓ
      exact le_trans (ih v hΓ) (le_disj_right _ _)
  | negNegIntro hder ih =>
      intro v hΓ
      simpa [LabelledFormula.Satisfied, evalCred] using ih v hΓ
  | negNegElim hder ih =>
      intro v hΓ
      simpa [LabelledFormula.Satisfied, evalCred] using ih v hΓ

theorem derivation_sound_thresholdConsequence {t : Credence}
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : Derivation (formulaContext (.threshold t) premises)
      { kind := .threshold t, formula := conclusion }) :
    thresholdConsequence t α premises conclusion := by
  intro v hprem
  apply derivation_sound h v
  constructor
  · intro b hb
    rcases List.mem_map.mp hb with ⟨φ, hφ, rfl⟩
    exact hprem φ hφ
  · intro J hJ
    cases hJ

theorem derivation_sound_formulaCertainty
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : Derivation (formulaContext .certain premises)
      { kind := .certain, formula := conclusion }) :
    formulaCertainty α premises conclusion := by
  intro v hprem
  apply derivation_sound h v
  constructor
  · intro b hb
    rcases List.mem_map.mp hb with ⟨φ, hφ, rfl⟩
    exact hprem φ hφ
  · intro J hJ
    cases hJ

theorem derivation_sound_formulaPositivity
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : Derivation (formulaContext .positive premises)
      { kind := .positive, formula := conclusion }) :
    formulaPositivity α premises conclusion := by
  intro v hprem
  apply derivation_sound h v
  constructor
  · intro b hb
    rcases List.mem_map.mp hb with ⟨φ, hφ, rfl⟩
    exact hprem φ hφ
  · intro J hJ
    cases hJ

/-! ## No Ex Falso -/

def noExFalsoContext : LabelContext (Fin 2) :=
  { bounds :=
      [ { kind := .positive, formula := .atom 0 },
        { kind := .positive, formula := .neg (.atom 0) } ],
    conds := [] }

/-- The labelled calculus has no ex-falso derivation from `A` and `~A` to an
    unrelated positive conclusion. -/
theorem labelled_no_ex_falso :
    ¬ Derivation noExFalsoContext { kind := .positive, formula := .atom 1 } := by
  intro h
  have hs := derivation_sound h
    (fun i : Fin 2 => if i = 0 then half else 0) ?_
  · simp [LabelledFormula.Satisfied, LabelKind.Satisfied, evalCred, zero_val] at hs
  · constructor
    · intro b hb
      simp only [noExFalsoContext, List.mem_cons, List.mem_singleton] at hb
      rcases hb with rfl | hb
      · simp [LabelledFormula.Satisfied, LabelKind.Satisfied, evalCred, half_val]
      rcases hb with rfl | hnil
      · simp [LabelledFormula.Satisfied, LabelKind.Satisfied, evalCred, half_val,
          Credence.neg_val]
        norm_num
      · cases hnil
    · intro J hJ
      cases hJ

end Cred
