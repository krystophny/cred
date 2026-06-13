/-
  Cred.Probability.Credal: credal sets over a valuation space.

  A `FinMeasureFamily V` is a nonempty finite family of `FinMeasure V`. It is
  the imprecise-probability layer: instead of a single measure it carries a set
  of admissible measures. The lower and upper probability of an event `S` are
  the smallest and largest probability `P μ S` over the family.

  `lowerP_le_upperP` is the basic interval property; a one-measure family is
  precise (`lowerP_eq_upperP_of_singleton`). The lower probability dominates
  every member (`lowerP_le_member`) and is dominated by them
  (`member_le_upperP`), so logical entailment lifts to the family corner:
  inclusion of events forces lower-probability domination
  (`entails_le_lowerP`).

  No measure theory: the family is a `Finset` of explicit `FinMeasure V` and
  bounds are `Finset.inf'`/`sup'` over rational probabilities.
-/

import Cred.Probability.Valuations

namespace Cred.Probability

open Finset

variable {V : Type*} [Fintype V]

/-- A nonempty finite family of finite measures over `V`: the credal set. -/
structure FinMeasureFamily (V : Type*) [Fintype V] where
  measures : Finset (FinMeasure V)
  nonempty : measures.Nonempty

/-- Lower probability of `S`: the least probability over the family. -/
def lowerP (M : FinMeasureFamily V) (S : Finset V) : ℚ :=
  M.measures.inf' M.nonempty (fun μ => P μ S)

/-- Upper probability of `S`: the greatest probability over the family. -/
def upperP (M : FinMeasureFamily V) (S : Finset V) : ℚ :=
  M.measures.sup' M.nonempty (fun μ => P μ S)

/-- Every member's probability dominates the lower probability. -/
theorem lowerP_le_member (M : FinMeasureFamily V) (S : Finset V)
    {μ : FinMeasure V} (hμ : μ ∈ M.measures) : lowerP M S ≤ P μ S :=
  Finset.inf'_le (fun μ => P μ S) hμ

/-- Every member's probability is dominated by the upper probability. -/
theorem member_le_upperP (M : FinMeasureFamily V) (S : Finset V)
    {μ : FinMeasure V} (hμ : μ ∈ M.measures) : P μ S ≤ upperP M S :=
  Finset.le_sup' (fun μ => P μ S) hμ

/-- The lower probability never exceeds the upper probability. -/
theorem lowerP_le_upperP (M : FinMeasureFamily V) (S : Finset V) :
    lowerP M S ≤ upperP M S := by
  obtain ⟨μ, hμ⟩ := M.nonempty
  exact le_trans (lowerP_le_member M S hμ) (member_le_upperP M S hμ)

/-- The lower probability is nonnegative. -/
theorem lowerP_nonneg (M : FinMeasureFamily V) (S : Finset V) :
    0 ≤ lowerP M S := by
  rw [lowerP, Finset.le_inf'_iff]
  exact fun μ _ => P_nonneg μ S

/-- A one-measure family is precise: lower and upper probability coincide. -/
theorem lowerP_eq_upperP_of_singleton (μ : FinMeasure V) (S : Finset V)
    (hne : ({μ} : Finset (FinMeasure V)).Nonempty) :
    lowerP ⟨{μ}, hne⟩ S = upperP ⟨{μ}, hne⟩ S := by
  simp [lowerP, upperP]

/-- Lower probability is monotone in the event: inclusion forces lower-bound
    domination. This is the credal-family corner of logical entailment. -/
theorem entails_le_lowerP (M : FinMeasureFamily V) {S T : Finset V}
    (h : S ⊆ T) : lowerP M S ≤ lowerP M T := by
  simp only [lowerP, Finset.le_inf'_iff]
  intro μ hμ
  exact le_trans (lowerP_le_member M S hμ) (P_mono h)

/-- Upper probability is likewise monotone in the event. -/
theorem entails_le_upperP (M : FinMeasureFamily V) {S T : Finset V}
    (h : S ⊆ T) : upperP M S ≤ upperP M T := by
  rw [upperP, Finset.sup'_le_iff]
  intro μ hμ
  exact le_trans (P_mono h) (member_le_upperP M T hμ)

end Cred.Probability
