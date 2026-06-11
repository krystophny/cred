/-
  Cred Threshold Consequence

  The threshold parameter t designates the interval [t,1]. This module packages
  the parametric consequence relation and records the two sharp boundary facts:
  explosion has a countermodel exactly up to 1/2 for positive thresholds, and
  excluded middle holds exactly up to 3/4.
-/

import Cred.Core.Consequence
import Cred.Fixpoint

namespace Cred

variable {α : Type*}

/-- Formula-level threshold consequence: every valuation that puts all premises
    in [t,1] also puts the conclusion in [t,1]. -/
def thresholdConsequence (t : Credence) (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) : Prop :=
  ∀ v : α → Credence,
    (∀ p ∈ premises, t ≤ evalCred v p) → t ≤ evalCred v conclusion

theorem threshold_reflexivity (t : Credence) (φ : Formula α) :
    thresholdConsequence t α [φ] φ := by
  intro v hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem threshold_monotonicity (t : Credence)
    (h : thresholdConsequence t α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    thresholdConsequence t α Δ φ := by
  intro v hprem
  exact h v (fun p hp => hprem p (hsub p hp))

theorem threshold_cut (t : Credence)
    (h1 : thresholdConsequence t α Γ φ)
    (h2 : thresholdConsequence t α (φ :: Γ) ψ) :
    thresholdConsequence t α Γ ψ := by
  intro v hprem
  have hφ := h1 v hprem
  exact h2 v (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

theorem threshold_one_iff_certainty (premises : List (Formula α))
    (conclusion : Formula α) :
    thresholdConsequence 1 α premises conclusion ↔
    formulaCertainty α premises conclusion := by
  constructor
  · intro h v hprem
    have hge := h v (fun p hp => by rw [hprem p hp])
    exact le_antisymm (evalCred v conclusion).le_one hge
  · intro h v hprem
    have hprem' : ∀ p ∈ premises, evalCred v p = 1 := by
      intro p hp
      exact le_antisymm (evalCred v p).le_one (hprem p hp)
    rw [h v hprem']

/-- Positivity is the union of positive thresholds. -/
theorem formulaPositivity_iff_exists_threshold (premises : List (Formula α))
    (conclusion : Formula α) :
    formulaPositivity α premises conclusion ↔
    ∀ v : α → Credence,
      (∀ p ∈ premises, ∃ t : Credence, 0 < t.val ∧ t ≤ evalCred v p) →
      ∃ t : Credence, 0 < t.val ∧ t ≤ evalCred v conclusion := by
  constructor
  · intro h v hprem
    have hpos := h v (fun p hp => by
      rcases hprem p hp with ⟨t, htpos, htle⟩
      exact lt_of_lt_of_le htpos htle)
    exact ⟨⟨(evalCred v conclusion).val, (evalCred v conclusion).nonneg,
      (evalCred v conclusion).le_one⟩, hpos, le_refl _⟩
  · intro h v hprem
    rcases h v (fun p hp =>
      ⟨⟨(evalCred v p).val, (evalCred v p).nonneg, (evalCred v p).le_one⟩,
        hprem p hp, le_refl _⟩) with ⟨t, htpos, htle⟩
    exact lt_of_lt_of_le htpos htle

/-! ## Sharp Thresholds -/

def thresholdExplosionCountermodel (t : Credence) : Prop :=
  ∃ v : Fin 2 → Credence,
    t ≤ v 0 ∧ t ≤ Credence.neg (v 0) ∧ ¬ (t ≤ v 1)

theorem threshold_explosion_countermodel_iff (t : Credence) (htpos : 0 < t.val) :
    thresholdExplosionCountermodel t ↔ t.val ≤ (1 : ℝ) / 2 := by
  constructor
  · rintro ⟨v, h0, hneg, _⟩
    have h0v : t.val ≤ (v 0).val := h0
    have hnegv : t.val ≤ 1 - (v 0).val := by
      simpa [Credence.le_def, Credence.neg_val] using hneg
    nlinarith only [h0v, hnegv]
  · intro ht
    rcases graded_no_explosion t ht htpos with ⟨v, h0, hneg, hfail⟩
    exact ⟨v, h0, hneg, hfail⟩

def thresholdExcludedMiddle (t : Credence) : Prop :=
  ∀ c : Credence, t ≤ c ⊔ Credence.neg c

theorem threshold_excluded_middle_iff (t : Credence) :
    thresholdExcludedMiddle t ↔ t.val ≤ (3 : ℝ) / 4 := by
  constructor
  · intro h
    have hhalf := h Credence.half
    have hval : t.val ≤ (Credence.half ⊔ Credence.neg Credence.half).val := hhalf
    norm_num [Credence.disj_val, Credence.neg_val, Credence.half_val] at hval
    exact hval
  · intro ht c
    change t.val ≤ (Credence.certainty c).val
    exact le_trans ht (Credence.certainty_ge_three_quarters c)

theorem threshold_window_nonempty :
    ∃ t : Credence, (1 : ℝ) / 2 < t.val ∧ t.val ≤ (3 : ℝ) / 4 := by
  refine ⟨⟨(3 : ℝ) / 4, by norm_num, by norm_num⟩, ?_, ?_⟩
  · norm_num
  · norm_num

end Cred
