/-
  Cred CrossingOut: Reductio as Case Elimination

  "Crossing out" an impossible case means showing that no admissible valuation
  occupies it.  When every potential countermodel to Γ ⊢ φ is crossed out, the
  entailment holds by reductio.  The contrast is explosion: a contradictory pair
  of premises leaves a surviving valuation at credence 1/2, so nothing is forced.

  Two families of concrete examples over Fin 2 (two atoms) are given:
  1. Crossing-out tautology: ¬(A ∧ ¬A) has no countermodel for t ≤ 3/4; every
     row is crossed out and the empty-premise sequent holds.
  2. Crossing-out via premise: A ∧ B ⊢ B; the premise eliminates every row
     where B falls below threshold.
  3. No-crossing-out: A, ¬A ⊢ B fails; the row v(A)=1/2, v(B)=0 survives.
-/

import Cred.Reductio
import Cred.Threshold

namespace Cred

/-! ## Shared atom names -/

-- atom 0 = A, atom 1 = B throughout this file
private abbrev A : Formula (Fin 2) := Formula.atom 0
private abbrev B : Formula (Fin 2) := Formula.atom 1

/-! ## Example 1: crossing out — ¬(A ∧ ¬A) is a threshold tautology

Every row has evalCred v (A ∧ ¬A) = v(A) * (1 - v(A)) ≤ 1/4 < t for t > 1/4.
At t ≤ 3/4, the De Morgan dual certainty c ⊔ ¬c ≥ 3/4 ≥ t, so ¬(A ∧ ¬A)
sits above threshold everywhere.  The countermodel set is empty; all rows
are crossed out.
-/

/-- The formula ¬(A ∧ ¬A) at atom 0. -/
private def notContradiction : Formula (Fin 2) :=
  Formula.neg (Formula.conj A (Formula.neg A))

/-- evalCred of notContradiction equals certainty applied to v(A). -/
private theorem eval_notContradiction (v : Fin 2 → Credence) :
    (evalCred v notContradiction).val = (Credence.certainty (v 0)).val := by
  simp only [notContradiction, evalCred, Credence.certainty, Credence.disj_val,
             Credence.neg_val, Credence.conj_val]
  ring

/-- For t ≤ 3/4, ¬(A ∧ ¬A) has no countermodel: every row is crossed out.
    The countermodel set is empty, so the tautology holds. -/
theorem notContradiction_no_countermodel (t : Credence) (ht : t.val ≤ 3 / 4) :
    reductioCountermodels t (Fin 2) [] notContradiction = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro v hmem
  simp only [mem_reductioCountermodels, List.forall_mem_nil, true_and] at hmem
  have hge : (3 : ℝ) / 4 ≤ (Credence.certainty (v 0)).val :=
    Credence.certainty_ge_three_quarters (v 0)
  have hlt : (evalCred v notContradiction).val < t.val :=
    (Credence.lt_def _ _).mp hmem.2
  rw [eval_notContradiction] at hlt
  linarith

/-- ¬(A ∧ ¬A) is a threshold tautology for t ≤ 3/4.
    Proof: the countermodel set is empty (every case is crossed out). -/
theorem notContradiction_tautology (t : Credence) (ht : t.val ≤ 3 / 4) :
    thresholdConsequence t (Fin 2) [] notContradiction :=
  reductio_of_countermodels_empty t [] notContradiction
    (notContradiction_no_countermodel t ht)

/-! ## Example 2: crossing out via premise — A ∧ B ⊢ B

The premise A ∧ B pins evalCred v (A ∧ B) = v(A)*v(B) ≥ t.
With v(A) ≤ 1, this forces v(B) ≥ t, crossing out every row where B < t.
-/

private def conjAB : Formula (Fin 2) := Formula.conj A B

/-- Under any threshold, every countermodel to B given premise A ∧ B is crossed
    out: v(A)*v(B) ≥ t forces v(B) ≥ t since v(A) ≤ 1. -/
theorem conjAB_to_B_no_countermodel (t : Credence) :
    reductioCountermodels t (Fin 2) [conjAB] B = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro v hmem
  simp only [mem_reductioCountermodels] at hmem
  obtain ⟨hprem, hlt⟩ := hmem
  have hge : t ≤ evalCred v conjAB := by
    apply hprem
    simp
  simp only [conjAB, evalCred, Credence.le_def, Credence.conj_val] at hge
  have hB_val : (v 1).val < t.val := (Credence.lt_def _ _).mp hlt
  have hA_le : (v 0).val ≤ 1 := (v 0).le_one
  nlinarith [(v 0).nonneg, (v 1).nonneg]

/-- A ∧ B ⊢ B by crossing out: every valuation where B falls below threshold
    violates the premise A ∧ B, so all such rows are eliminated. -/
theorem conjAB_to_B_by_crossing_out (t : Credence) :
    thresholdConsequence t (Fin 2) [conjAB] B :=
  reductio_of_countermodels_empty t [conjAB] B (conjAB_to_B_no_countermodel t)

/-! ## Contrast: no crossing out — explosion is blocked

The pair A, ¬A at threshold t ≤ 1/2 has a surviving countermodel at v(A)=1/2.
This row is NOT crossed out: A and ¬A are both above threshold 1/2 there, yet B
can sit at 0.  Reductio fires only when the set is empty; here it is nonempty,
so nothing is forced.
-/

/-- The surviving row: v(A)=1/2, v(B)=0.  Both A and ¬A sit at exactly 1/2,
    while B = 0.  This row is not crossed out. -/
noncomputable def survivingRow : Fin 2 → Credence
  | 0 => Credence.half
  | 1 => 0

theorem survivingRow_A : evalCred survivingRow A = Credence.half := by
  simp [survivingRow, evalCred]

theorem survivingRow_negA : evalCred survivingRow (Formula.neg A) = Credence.half := by
  simp [survivingRow, evalCred, Credence.liar_fixed_point]

theorem survivingRow_B : evalCred survivingRow B = 0 := by
  simp [survivingRow, evalCred]

/-- At t = 1/2, the contradiction pair A, ¬A has a genuine surviving row:
    the countermodel set is nonempty, so no crossing-out occurs and nothing
    beyond the explicit premises is forced. -/
theorem explosion_row_survives :
    (reductioCountermodels Credence.half (Fin 2)
      [A, Formula.neg A] B).Nonempty := by
  refine ⟨survivingRow, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [survivingRow_A]
    · rw [survivingRow_negA]
  · rw [survivingRow_B, Credence.lt_def, Credence.zero_val, Credence.half_val]
    norm_num

/-- Because the countermodel row survives, explosion is not a valid entailment:
    A, ¬A do not entail B at threshold 1/2. -/
theorem no_explosion_at_half_by_surviving_row :
    ¬ thresholdConsequence Credence.half (Fin 2) [A, Formula.neg A] B := by
  rw [reductio_iff_countermodels_empty]
  exact Set.nonempty_iff_ne_empty.mp explosion_row_survives

/-! ## Summary theorem

The two regimes in a single statement: for t ≤ 3/4 the tautology ¬(A ∧ ¬A)
holds (all rows crossed out), while at t = 1/2 the explosion sequent A, ¬A ⊢ B
fails (a row survives). -/

theorem crossing_out_vs_explosion :
    thresholdConsequence ⟨3/4, by norm_num, by norm_num⟩ (Fin 2) [] notContradiction ∧
    ¬ thresholdConsequence Credence.half (Fin 2) [A, Formula.neg A] B :=
  ⟨notContradiction_tautology _ (le_refl _),
   no_explosion_at_half_by_surviving_row⟩

end Cred
