/-
  Cred.Probability.Valuations: real probability over a valuation space.

  A valuation space `V` (the worlds/valuations) carries a finite probability
  measure `FinMeasure V`: a nonnegative rational mass on each valuation summing
  to one. `P μ S` is the probability of a `Finset` of valuations, `Pcond μ T S`
  the conditional probability of `T` given `S`, and `dirac v` the point mass at
  one valuation.

  The logical layer sits inside this measure layer as a degenerate corner.
  Logical entailment `S ⊆ T` between truth sets is exactly:

  - "domination under every measure", `P μ S ≤ P μ T` for all `μ`
    (`entails_iff_dominated`); and
  - "conditional probability one under every measure",
    `Pcond μ T S = 1` whenever `P μ S ≠ 0` (`entails_iff_cond_one`).

  The converse directions use a Dirac mass at a point of `S \ T`. So the
  universal quantifier of logic ("at every valuation") is the all-measures /
  conditional-probability-one corner of probability over valuations.

  The measured conditional obeys the same chain rule as Cred's value-level
  fiber: `Pcond μ T S * P μ S = P μ (S ∩ T)` (`cond_chain_rule`), matching
  Cred's `c * e = j`. Zero-probability evidence is unconstrained
  (`zero_evidence_unconstrained`), the measure-layer image of `Cond(0,0) =
  [0,1]`.

  No measure theory: probability is an explicit `Finset.sum` of rationals.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Cred.Probability

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite probability measure over a valuation space `V`: a nonnegative
    rational mass on each valuation, summing to one. -/
structure FinMeasure (V : Type*) [Fintype V] where
  mass : V → ℚ
  nonneg : ∀ v, 0 ≤ mass v
  total : (∑ v, mass v) = 1

/-- Probability of a set of valuations: the total mass it carries. -/
def P (μ : FinMeasure V) (S : Finset V) : ℚ := ∑ v ∈ S, μ.mass v

/-- Conditional probability of `T` given `S`. -/
def Pcond (μ : FinMeasure V) (T S : Finset V) : ℚ := P μ (S ∩ T) / P μ S

/-- Point mass at a single valuation. -/
def dirac (v : V) : FinMeasure V where
  mass := fun u => if u = v then 1 else 0
  nonneg := by
    intro u
    by_cases h : u = v <;> simp [h]
  total := by
    simp [Fintype.sum_ite_eq']

omit [DecidableEq V] in
/-- Probability is nonnegative. -/
theorem P_nonneg (μ : FinMeasure V) (S : Finset V) : 0 ≤ P μ S := by
  unfold P
  exact Finset.sum_nonneg (fun v _ => μ.nonneg v)

omit [DecidableEq V] in
/-- Probability is monotone in the event. -/
theorem P_mono {μ : FinMeasure V} {S T : Finset V} (h : S ⊆ T) :
    P μ S ≤ P μ T := by
  unfold P
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun v _ _ => μ.nonneg v)

/-- The probability of `S` under the Dirac mass at `v` is `1` if `v ∈ S`, else
    `0`. -/
theorem P_dirac (v : V) (S : Finset V) :
    P (dirac v) S = if v ∈ S then 1 else 0 := by
  unfold P dirac
  rw [Finset.sum_ite_eq' S v (fun _ => (1 : ℚ))]

omit [DecidableEq V] in
/-- The total mass of the whole valuation space is `1`. -/
theorem P_univ (μ : FinMeasure V) : P μ Finset.univ = 1 := by
  unfold P
  simpa using μ.total

/-- Inclusion of truth sets is exactly domination under every measure: this is
    the all-measures corner where the universal quantifier of logic lives.
    The converse uses a Dirac mass at a point of `S \ T`. -/
theorem entails_iff_dominated (S T : Finset V) :
    S ⊆ T ↔ ∀ μ : FinMeasure V, P μ S ≤ P μ T := by
  constructor
  · intro h μ
    exact P_mono h
  · intro h
    by_contra hst
    rw [Finset.not_subset] at hst
    obtain ⟨v, hvS, hvT⟩ := hst
    have hd := h (dirac v)
    rw [P_dirac v S, P_dirac v T, if_pos hvS, if_neg hvT] at hd
    exact absurd hd (by norm_num)

/-- The measured chain rule: `Pcond μ T S * P μ S = P μ (S ∩ T)` when `S` has
    positive probability. This is exactly Cred's value-level fiber `c * e = j`
    with `c = Pcond`, `e = P μ S`, `j = P μ (S ∩ T)`. -/
theorem cond_chain_rule {μ : FinMeasure V} {S T : Finset V} (h : P μ S ≠ 0) :
    Pcond μ T S * P μ S = P μ (S ∩ T) := by
  unfold Pcond
  exact div_mul_cancel₀ (P μ (S ∩ T)) h

/-- Zero-probability evidence leaves the conditional equation unconstrained:
    every rational `c` satisfies `c * P μ S = P μ (S ∩ T)`. The measure-layer
    image of `Cond(0,0) = [0,1]`. -/
theorem zero_evidence_unconstrained {μ : FinMeasure V} {S T : Finset V}
    (h : P μ S = 0) : ∀ c : ℚ, c * P μ S = P μ (S ∩ T) := by
  have hsub : S ∩ T ⊆ S := Finset.inter_subset_left
  have hle : P μ (S ∩ T) ≤ P μ S := P_mono hsub
  have hge : 0 ≤ P μ (S ∩ T) := P_nonneg μ (S ∩ T)
  rw [h] at hle
  have hzero : P μ (S ∩ T) = 0 := le_antisymm hle hge
  intro c
  rw [h, hzero, mul_zero]

/-- Inclusion of truth sets is exactly conditional probability one under every
    measure: entailment is the `= 1` corner of a measure. The converse uses a
    Dirac mass at a point of `S \ T`. -/
theorem entails_iff_cond_one (S T : Finset V) :
    S ⊆ T ↔ ∀ μ : FinMeasure V, P μ S ≠ 0 → Pcond μ T S = 1 := by
  constructor
  · intro h μ hpos
    have hinter : S ∩ T = S := Finset.inter_eq_left.mpr h
    unfold Pcond
    rw [hinter]
    exact div_self hpos
  · intro h
    by_contra hst
    rw [Finset.not_subset] at hst
    obtain ⟨v, hvS, hvT⟩ := hst
    have hpos : P (dirac v) S ≠ 0 := by
      rw [P_dirac v S, if_pos hvS]; norm_num
    have hone := h (dirac v) hpos
    unfold Pcond at hone
    have hinter : v ∉ S ∩ T := by
      simp only [Finset.mem_inter]
      exact fun hc => hvT hc.2
    rw [P_dirac v (S ∩ T), if_neg hinter, P_dirac v S, if_pos hvS] at hone
    norm_num at hone

end Cred.Probability
