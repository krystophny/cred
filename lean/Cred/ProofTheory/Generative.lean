/-
  Cred ProofTheory: Generative Labelled Calculus (issue #642)

  A small, fully local labelled calculus.  Unlike `Cred.Sequent`, which
  imports already-verified semantic-consequence relations as oracle rules,
  every rule here is a *local* introduction/elimination or structural step.
  Soundness is proved by induction on the derivation against the credence
  semantics, with no semantic-consequence oracle.

  There is NO implication or conditional formula constructor.  Conjunction,
  disjunction and negation are the only connectives; chain-rule conditioning
  never appears as a formula arrow.

  Premises carry their own designation labels (`LForm`), so the demanded level
  of a premise is decoupled from the level of the conclusion.  This is what
  makes the cross-label lifting rules (certain → threshold, threshold →
  positive) sound.
-/

import Cred.ProofTheory.Labels

namespace Cred.ProofTheory

open Cred

/-! ## Toy Formulas -/

/-- Toy propositional formulas: atoms (named by a type `α`), negation,
    conjunction and disjunction.  No implication, no conditional. -/
inductive Formula (α : Type*) where
  | atom : α → Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α

variable {α : Type*}

/-- Evaluate a formula into a credence under an atom assignment. -/
noncomputable def eval (v : α → Credence) : Formula α → Credence
  | .atom a => v a
  | .neg φ => ~ (eval v φ)
  | .conj φ ψ => eval v φ ⊗ eval v ψ
  | .disj φ ψ => eval v φ ⊔ eval v ψ

/-- A labelled formula: a formula together with the designation level demanded
    of it. -/
structure LForm (α : Type*) where
  label : Label
  formula : Formula α

/-- A valuation designates a labelled formula when its evaluated credence meets
    the demanded label. -/
def LForm.Designated (v : α → Credence) (b : LForm α) : Prop :=
  b.label.designates (eval v b.formula)

/-- A valuation designates a whole context. -/
def Designated (v : α → Credence) (Γ : List (LForm α)) : Prop :=
  ∀ b ∈ Γ, b.Designated v

/-! ## Local Order Lemmas

These are the only semantic facts the calculus rules rely on; each is a small
monotonicity statement, proved locally so the calculus stays self-contained. -/

theorem conj_mono {a b c d : Credence} (hab : a.val ≤ b.val) (hcd : c.val ≤ d.val) :
    (a ⊗ c).val ≤ (b ⊗ d).val := by
  simp only [Credence.conj_val]
  calc a.val * c.val ≤ b.val * c.val :=
        mul_le_mul_of_nonneg_right hab c.nonneg
    _ ≤ b.val * d.val := mul_le_mul_of_nonneg_left hcd b.nonneg

theorem conj_le_left (a b : Credence) : (a ⊗ b).val ≤ a.val := by
  simp only [Credence.conj_val]
  calc a.val * b.val ≤ a.val * 1 := mul_le_mul_of_nonneg_left b.le_one a.nonneg
    _ = a.val := mul_one _

theorem conj_le_right (a b : Credence) : (a ⊗ b).val ≤ b.val := by
  rw [Credence.conj_comm]; exact conj_le_left b a

theorem le_disj_left (a b : Credence) : a.val ≤ (a ⊔ b).val := by
  rw [Credence.disj_val]
  have h : 0 ≤ b.val * (1 - a.val) := mul_nonneg b.nonneg (by linarith [a.le_one])
  linarith

theorem le_disj_right (a b : Credence) : b.val ≤ (a ⊔ b).val := by
  rw [Credence.disj_comm]; exact le_disj_left b a

/-! ## The Generative Calculus

`Derives Γ k φ` reads: from the labelled premise list `Γ`, the conclusion `φ`
is derivable at designation level `k`.  Every constructor is a local rule;
none imports a semantic-consequence relation. -/

inductive Derives : List (LForm α) → Label → Formula α → Prop where
  /-- A premise is derivable at its own demanded level. -/
  | hyp {Γ : List (LForm α)} {k : Label} {φ : Formula α} :
      ⟨k, φ⟩ ∈ Γ → Derives Γ k φ
  /-- Adding premises preserves derivability. -/
  | weaken {Γ Δ : List (LForm α)} {k : Label} {φ : Formula α} :
      Derives Γ k φ → (∀ b ∈ Γ, b ∈ Δ) → Derives Δ k φ
  /-- Cut on a derived intermediate formula at level `k`. -/
  | cut {Γ : List (LForm α)} {k : Label} {mid φ : Formula α} :
      Derives Γ k mid → Derives (⟨k, mid⟩ :: Γ) k φ → Derives Γ k φ
  /-- Conjunction introduction: from `φ` at threshold `s` and `ψ` at threshold
      `t`, conclude `φ ∧ ψ` at threshold `s ⊗ t`.  Sound because conjunction
      evaluates as the product `s.val * t.val ≤ (eval φ).val * (eval ψ).val`. -/
  | conjIntro {Γ : List (LForm α)} {s t : Credence} {φ ψ : Formula α} :
      Derives Γ (.threshold s) φ → Derives Γ (.threshold t) ψ →
      Derives Γ (.threshold (s ⊗ t)) (.conj φ ψ)
  /-- Conjunction elimination (left), at any threshold. -/
  | conjElimLeft {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α} :
      Derives Γ (.threshold t) (.conj φ ψ) → Derives Γ (.threshold t) φ
  /-- Conjunction elimination (right), at any threshold. -/
  | conjElimRight {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α} :
      Derives Γ (.threshold t) (.conj φ ψ) → Derives Γ (.threshold t) ψ
  /-- Disjunction introduction (left), at any threshold. -/
  | disjIntroLeft {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α} :
      Derives Γ (.threshold t) φ → Derives Γ (.threshold t) (.disj φ ψ)
  /-- Disjunction introduction (right), at any threshold. -/
  | disjIntroRight {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α} :
      Derives Γ (.threshold t) ψ → Derives Γ (.threshold t) (.disj φ ψ)
  /-- Lowering a threshold (monotonicity in the designation level). -/
  | thresholdMono {Γ : List (LForm α)} {s t : Credence} {φ : Formula α} :
      Derives Γ (.threshold s) φ → t.val ≤ s.val →
      Derives Γ (.threshold t) φ
  /-- A strictly positive threshold derivation lifts to positivity. -/
  | thresholdToPositive {Γ : List (LForm α)} {t : Credence} {φ : Formula α} :
      Derives Γ (.threshold t) φ → 0 < t.val → Derives Γ .positive φ
  /-- A certain derivation lifts to any threshold. -/
  | certainToThreshold {Γ : List (LForm α)} {t : Credence} {φ : Formula α} :
      Derives Γ .certain φ → Derives Γ (.threshold t) φ
  /-- A certain derivation lifts to positivity. -/
  | certainToPositive {Γ : List (LForm α)} {φ : Formula α} :
      Derives Γ .certain φ → Derives Γ .positive φ
  /-- Excluded-middle axiom: `φ ⊔ ~φ` is derivable from no premises at any
      threshold up to `3/4`.  This is a local axiom schema (justified by
      `certainty_ge_three_quarters`), not an imported consequence relation. -/
  | excludedMiddle {Γ : List (LForm α)} {t : Credence} {φ : Formula α} :
      t.val ≤ (3 : ℝ) / 4 → Derives Γ (.threshold t) (.disj φ (.neg φ))
  /-- Double-negation introduction, at any label. -/
  | negNegIntro {Γ : List (LForm α)} {k : Label} {φ : Formula α} :
      Derives Γ k φ → Derives Γ k (.neg (.neg φ))
  /-- Double-negation elimination, at any label. -/
  | negNegElim {Γ : List (LForm α)} {k : Label} {φ : Formula α} :
      Derives Γ k (.neg (.neg φ)) → Derives Γ k φ

/-! ## Soundness -/

/-- The generative calculus is sound: if `Γ ⊢ φ` at level `k`, then every
    valuation designating all of `Γ` designates `φ` at `k`.  Proved by
    induction over the local rules, with no appeal to a semantic-consequence
    oracle. -/
theorem generative_sound {Γ : List (LForm α)} {k : Label} {φ : Formula α}
    (h : Derives Γ k φ) :
    ∀ v : α → Credence, Designated v Γ → k.designates (eval v φ) := by
  induction h with
  | hyp hmem =>
      intro v hΓ; exact hΓ _ hmem
  | weaken _ hsub ih =>
      intro v hΔ; exact ih v (fun b hb => hΔ b (hsub b hb))
  | cut _ _ ihmid ihgoal =>
      intro v hΓ
      have hmid := ihmid v hΓ
      apply ihgoal v
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hmid
      · exact hΓ b hb'
  | conjIntro _ _ ihφ ihψ =>
      intro v hΓ
      have hφ := ihφ v hΓ
      have hψ := ihψ v hΓ
      simp only [Label.designates, eval, Credence.conj_val] at hφ hψ ⊢
      exact conj_mono hφ hψ
  | conjElimLeft _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      simp only [Label.designates, eval] at hc ⊢
      exact le_trans hc (conj_le_left _ _)
  | conjElimRight _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      simp only [Label.designates, eval] at hc ⊢
      exact le_trans hc (conj_le_right _ _)
  | disjIntroLeft _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      simp only [Label.designates, eval] at hc ⊢
      exact le_trans hc (le_disj_left _ _)
  | disjIntroRight _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      simp only [Label.designates, eval] at hc ⊢
      exact le_trans hc (le_disj_right _ _)
  | thresholdMono _ hts ih =>
      intro v hΓ
      exact le_trans hts (ih v hΓ)
  | thresholdToPositive _ ht ih =>
      intro v hΓ
      exact Label.threshold_designates_positive (ih v hΓ) ht
  | certainToThreshold _ ih =>
      intro v hΓ
      exact Label.certain_designates_threshold _ (ih v hΓ)
  | certainToPositive _ ih =>
      intro v hΓ
      exact Label.certain_designates_positive (ih v hΓ)
  | @excludedMiddle Γ t φ ht =>
      intro v _
      show t.val ≤ (eval v φ ⊔ ~ (eval v φ)).val
      have hge : (3 : ℝ) / 4 ≤ (eval v φ ⊔ ~ (eval v φ)).val := by
        have := Credence.certainty_ge_three_quarters (eval v φ)
        simpa [Credence.certainty, ge_iff_le] using this
      exact le_trans ht hge
  | negNegIntro _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      cases k <;>
        simp only [Label.designates, eval, Credence.neg_neg] at hc ⊢ <;> exact hc
  | negNegElim _ ih =>
      intro v hΓ
      have hc := ih v hΓ
      cases k <;>
        simp only [Label.designates, eval, Credence.neg_neg] at hc ⊢ <;> exact hc

/-! ## Per-rule soundness corollaries

Each names the soundness consequence of one rule directly, as a one-line
specialization of `generative_sound`. -/

/-- Conjunction introduction is sound: premises designated at thresholds `s`, `t`
    designate the conjunction at threshold `s ⊗ t`. -/
theorem conjIntro_sound {Γ : List (LForm α)} {s t : Credence} {φ ψ : Formula α}
    (hφ : Derives Γ (.threshold s) φ) (hψ : Derives Γ (.threshold t) ψ) :
    ∀ v : α → Credence, Designated v Γ →
      (Label.threshold (s ⊗ t)).designates (eval v (.conj φ ψ)) :=
  generative_sound (Derives.conjIntro hφ hψ)

/-- Conjunction elimination (left) is sound. -/
theorem conjElimLeft_sound {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α}
    (h : Derives Γ (.threshold t) (.conj φ ψ)) :
    ∀ v : α → Credence, Designated v Γ →
      (Label.threshold t).designates (eval v φ) :=
  generative_sound (Derives.conjElimLeft h)

/-- Conjunction elimination (right) is sound. -/
theorem conjElimRight_sound {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α}
    (h : Derives Γ (.threshold t) (.conj φ ψ)) :
    ∀ v : α → Credence, Designated v Γ →
      (Label.threshold t).designates (eval v ψ) :=
  generative_sound (Derives.conjElimRight h)

/-- Disjunction introduction (left) is sound. -/
theorem disjIntroLeft_sound {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α}
    (h : Derives Γ (.threshold t) φ) :
    ∀ v : α → Credence, Designated v Γ →
      (Label.threshold t).designates (eval v (.disj φ ψ)) :=
  generative_sound (Derives.disjIntroLeft h)

/-- Disjunction introduction (right) is sound. -/
theorem disjIntroRight_sound {Γ : List (LForm α)} {t : Credence} {φ ψ : Formula α}
    (h : Derives Γ (.threshold t) ψ) :
    ∀ v : α → Credence, Designated v Γ →
      (Label.threshold t).designates (eval v (.disj φ ψ)) :=
  generative_sound (Derives.disjIntroRight h)

end Cred.ProofTheory
