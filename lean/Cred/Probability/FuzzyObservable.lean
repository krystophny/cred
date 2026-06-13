/-
  Cred.Probability.FuzzyObservable: graded observables and their expectations.

  A fuzzy observable is a function `f : V → ℚ` assigning a graded value to each
  valuation. Its expectation under a finite measure `μ` is the mass-weighted
  sum `∑ v, μ.mass v * f v`. The crisp special case is the indicator of an
  event `S`: `expectation_indicator` shows its expectation equals the
  probability `P μ S`, so probability is the expectation of a 0/1 observable.

  Over a credal family the lower and upper expectations are the least and
  greatest expectations over the family, with `lowerE_le_upperE` the interval
  property. No measure theory: everything is a finite rational sum.
-/

import Cred.Probability.Credal

namespace Cred.Probability

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Expectation of a fuzzy observable `f` under a finite measure `μ`. -/
def Expectation (μ : FinMeasure V) (f : V → ℚ) : ℚ := ∑ v, μ.mass v * f v

/-- The crisp indicator of an event `S`: `1` on `S`, `0` off it. -/
def indicator (S : Finset V) (v : V) : ℚ := if v ∈ S then 1 else 0

/-- Expectation of the indicator of `S` is the probability of `S`: probability
    is the expectation of a 0/1 observable. -/
theorem expectation_indicator (μ : FinMeasure V) (S : Finset V) :
    Expectation μ (indicator S) = P μ S := by
  unfold Expectation indicator P
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [DecidableEq V] in
/-- Expectation of the zero observable is zero. -/
theorem expectation_zero (μ : FinMeasure V) :
    Expectation μ (fun _ => (0 : ℚ)) = 0 := by
  simp [Expectation]

omit [DecidableEq V] in
/-- Expectation of the constant-one observable is one. -/
theorem expectation_one (μ : FinMeasure V) :
    Expectation μ (fun _ => (1 : ℚ)) = 1 := by
  unfold Expectation
  simpa using μ.total

/-- Lower expectation of `f` over a credal family: least expectation. -/
def lowerE (M : FinMeasureFamily V) (f : V → ℚ) : ℚ :=
  M.measures.inf' M.nonempty (fun μ => Expectation μ f)

/-- Upper expectation of `f` over a credal family: greatest expectation. -/
def upperE (M : FinMeasureFamily V) (f : V → ℚ) : ℚ :=
  M.measures.sup' M.nonempty (fun μ => Expectation μ f)

omit [DecidableEq V] in
/-- Every member's expectation dominates the lower expectation. -/
theorem lowerE_le_member (M : FinMeasureFamily V) (f : V → ℚ)
    {μ : FinMeasure V} (hμ : μ ∈ M.measures) : lowerE M f ≤ Expectation μ f :=
  Finset.inf'_le (fun μ => Expectation μ f) hμ

omit [DecidableEq V] in
/-- Every member's expectation is dominated by the upper expectation. -/
theorem member_le_upperE (M : FinMeasureFamily V) (f : V → ℚ)
    {μ : FinMeasure V} (hμ : μ ∈ M.measures) : Expectation μ f ≤ upperE M f :=
  Finset.le_sup' (fun μ => Expectation μ f) hμ

omit [DecidableEq V] in
/-- The lower expectation never exceeds the upper expectation. -/
theorem lowerE_le_upperE (M : FinMeasureFamily V) (f : V → ℚ) :
    lowerE M f ≤ upperE M f := by
  obtain ⟨μ, hμ⟩ := M.nonempty
  exact le_trans (lowerE_le_member M f hμ) (member_le_upperE M f hμ)

/-- Lower expectation of the indicator of `S` equals the lower probability of
    `S`: the credal-family analogue of `expectation_indicator`. -/
theorem lowerE_indicator (M : FinMeasureFamily V) (S : Finset V) :
    lowerE M (indicator S) = lowerP M S := by
  unfold lowerE lowerP
  have hfun : (fun μ => Expectation μ (indicator S)) = (fun μ : FinMeasure V => P μ S) := by
    funext μ
    exact expectation_indicator μ S
  rw [hfun]

end Cred.Probability
