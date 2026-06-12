/-
  Cred Reductio as Countermodel Elimination

  Reductio establishes Γ ⊢ φ by refuting every countermodel: a valuation that
  keeps the premises designated yet drops the conclusion below threshold. The
  legitimate ground is emptiness of that countermodel set, not the mere presence
  of a contradiction among the premises. Explosion is the contrasting failure
  mode: a contradictory premise pair leaves a surviving countermodel, so reductio
  does not license an arbitrary conclusion.
-/

import Cred.Threshold

namespace Cred

variable {α : Type*}

/-- A reductio countermodel for `Γ ⊢ φ` at threshold `t`: a valuation that puts
    every premise in `[t,1]` while the conclusion drops below `t`. -/
def reductioCountermodels (t : Credence) (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) : Set (α → Credence) :=
  {v | (∀ p ∈ premises, t ≤ evalCred v p) ∧ evalCred v conclusion < t}

@[simp] theorem mem_reductioCountermodels (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α) (v : α → Credence) :
    v ∈ reductioCountermodels t α premises conclusion ↔
    (∀ p ∈ premises, t ≤ evalCred v p) ∧ evalCred v conclusion < t :=
  Iff.rfl

/-- Reductio as countermodel elimination: if the conclusion's threshold claim has
    no surviving countermodel under the premises, the entailment holds. The
    refuted hypothesis is the conclusion's failure `evalCred v φ < t`, the
    semantic negation of the target. -/
theorem reductio_of_countermodels_empty (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α)
    (h : reductioCountermodels t α premises conclusion = ∅) :
    thresholdConsequence t α premises conclusion := by
  intro v hprem
  by_contra hlt
  have hfail : evalCred v conclusion < t :=
    (Credence.lt_def _ _).mpr (lt_of_not_le (fun hle => hlt ((Credence.le_def _ _).mpr hle)))
  have hmem : v ∈ reductioCountermodels t α premises conclusion := ⟨hprem, hfail⟩
  rw [h] at hmem
  exact (Set.mem_empty_iff_false v).mp hmem

/-- Converse: an entailment leaves no countermodel. Together with the previous
    theorem, emptiness of the countermodel set is exactly the entailment. -/
theorem countermodels_empty_of_reductio (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α)
    (h : thresholdConsequence t α premises conclusion) :
    reductioCountermodels t α premises conclusion = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro v hmem
  have : (t.val ≤ (evalCred v conclusion).val) := (Credence.le_def _ _).mp (h v hmem.1)
  exact absurd this (not_le_of_lt ((Credence.lt_def _ _).mp hmem.2))

theorem reductio_iff_countermodels_empty (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α) :
    thresholdConsequence t α premises conclusion ↔
    reductioCountermodels t α premises conclusion = ∅ :=
  ⟨countermodels_empty_of_reductio t premises conclusion,
   reductio_of_countermodels_empty t premises conclusion⟩

/-- Reductio elimination as a single-valuation refutation: ruling out the
    conclusion's failure for every valuation that satisfies the premises is the
    entailment, by definition. This is the operational form a proof search uses. -/
theorem reductio_of_no_failing_valuation (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α)
    (h : ∀ v : α → Credence,
      (∀ p ∈ premises, t ≤ evalCred v p) → ¬ (evalCred v conclusion < t)) :
    thresholdConsequence t α premises conclusion := by
  intro v hprem
  have : t.val ≤ (evalCred v conclusion).val :=
    le_of_not_lt (fun hlt => h v hprem ((Credence.lt_def _ _).mpr hlt))
  exact (Credence.le_def _ _).mpr this

/-! ## Contrast with Explosion

Explosion is `[A, ~A] ⊢ B` for arbitrary `B`. The contradiction `A ∧ ~A` is
present among the premises, yet at a positive threshold `t ≤ 1/2` a countermodel
survives. So the contradiction is not the ground of entailment; emptiness of the
countermodel set is, and here that set is nonempty. -/

/-- The explosion sequent over `Fin 2`: premises `A`, `~A`, conclusion `B`. -/
def explosionPremises : List (Formula (Fin 2)) :=
  [Formula.atom 0, Formula.neg (Formula.atom 0)]

def explosionConclusion : Formula (Fin 2) := Formula.atom 1

/-- For a positive threshold `t ≤ 1/2`, the explosion sequent has a genuine
    reductio countermodel. The premises pin a contradiction, but the
    countermodel set is nonempty, so reductio supplies no entailment of `B`. -/
theorem explosion_has_reductio_countermodel (t : Credence)
    (htpos : 0 < t.val) (ht : t.val ≤ (1 : ℝ) / 2) :
    (reductioCountermodels t (Fin 2) explosionPremises explosionConclusion).Nonempty := by
  rcases graded_no_explosion t ht htpos with ⟨v, h0, hneg, hfail⟩
  refine ⟨v, ?_, ?_⟩
  · intro p hp
    simp only [explosionPremises, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h
    · subst h; exact h0
    · subst h; exact hneg
  · show evalCred v explosionConclusion < t
    have : (v 1).val < t.val :=
      lt_of_not_le (fun hle => hfail ((Credence.le_def _ _).mpr hle))
    exact (Credence.lt_def _ _).mpr this

/-- The contradiction is genuinely present: both premises sit in `[t,1]` at the
    witnessing valuation, so the failure is not a missing premise but a surviving
    countermodel. -/
theorem explosion_premises_designated (t : Credence)
    (htpos : 0 < t.val) (ht : t.val ≤ (1 : ℝ) / 2) :
    ∃ v : Fin 2 → Credence,
      (∀ p ∈ explosionPremises, t ≤ evalCred v p) ∧
      ¬ thresholdConsequence t (Fin 2) explosionPremises explosionConclusion := by
  rcases explosion_has_reductio_countermodel t htpos ht with ⟨v, hprem, hfail⟩
  refine ⟨v, hprem, ?_⟩
  rw [reductio_iff_countermodels_empty, Set.eq_empty_iff_forall_not_mem]
  intro hempty
  exact hempty v ⟨hprem, hfail⟩

/-- The discriminating statement: the legitimate ground of reductio is emptiness
    of the countermodel set, not the presence of a contradiction. The explosion
    sequent has both premises designated (a contradiction in the premises) yet a
    nonempty countermodel set, so it is not a valid entailment; reductio fires
    only when the set is empty. -/
theorem reductio_ground_is_emptiness_not_contradiction (t : Credence)
    (htpos : 0 < t.val) (ht : t.val ≤ (1 : ℝ) / 2) :
    (reductioCountermodels t (Fin 2) explosionPremises explosionConclusion).Nonempty ∧
    ¬ thresholdConsequence t (Fin 2) explosionPremises explosionConclusion := by
  refine ⟨explosion_has_reductio_countermodel t htpos ht, ?_⟩
  rw [reductio_iff_countermodels_empty]
  exact Set.nonempty_iff_ne_empty.mp (explosion_has_reductio_countermodel t htpos ht)

end Cred
