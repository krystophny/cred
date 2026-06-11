/-
  Cred Bridge: Comparison Layer

  Comparison theorems pinning admissible-set conditioning to its nearest
  neighbors:
  1. Credal-set reading: Cond j e is the largest set of posteriors coherent
     with the chain rule (cond_maximal_coherent).
  2. The trivalent de Finetti conditional fails the conditional bridge
     (df_cond_fails_bridge, df_cond_fails_at), as a corollary of
     no_truthfunctional_cond_bridge.
  3. Ratio agreement: with positive evidence, Cond j e is the singleton at
     the Bayesian ratio j/e (cond_ratio_singleton).
-/

import Cred.Bridge.CondBridge

namespace Cred

open Credence

/-! ## Credal-Set Reading

`Cond j e` collects every conditional credence coherent with the chain rule
c ⊗ e = j.  Read as imprecise probability, it is the credal set of admissible
posteriors. -/

/-- Credal-set reading: any set of conditional credences coherent with the
    chain rule is contained in `Cond j e`, so `Cond j e` is the largest
    coherent posterior set, the natural extension in Walley's sense. -/
theorem cond_maximal_coherent (j e : Credence) (S : Set Credence)
    (h : ∀ c ∈ S, c ⊗ e = j) : S ⊆ Cond j e :=
  fun c hc => h c hc

/-! ## The Trivalent de Finetti Conditional

de Finetti's three-valued conditional B|A takes the value of the consequent
when the antecedent is true and the third value otherwise.  It is the nearest
neighbor of admissible conditioning in the many-valued literature, and it
fails the conditional bridge. -/

namespace ThreeVal

/-- Trivalent de Finetti conditional: dfCond a b is the value of the
    consequent b when the antecedent a is one, and half (the third value,
    "void") otherwise. -/
def dfCond : ThreeVal → ThreeVal → ThreeVal
  | one, b => b
  | _, _ => half

/-! ### Complete de Finetti Conditional Table

       | 0 | 1/2 | 1
   ----+---+-----+---
   0   |1/2| 1/2 |1/2    (void row: false antecedent)
   1/2 |1/2| 1/2 |1/2    (void row: undetermined antecedent)
   1   | 0 | 1/2 | 1     (value of the consequent)
-/

theorem dfCond_zero_zero : dfCond zero zero = half := rfl
theorem dfCond_zero_half : dfCond zero half = half := rfl
theorem dfCond_zero_one : dfCond zero one = half := rfl
theorem dfCond_half_zero : dfCond half zero = half := rfl
theorem dfCond_half_half : dfCond half half = half := rfl
theorem dfCond_half_one : dfCond half one = half := rfl
theorem dfCond_one_zero : dfCond one zero = zero := rfl
theorem dfCond_one_half : dfCond one half = half := rfl
theorem dfCond_one_one : dfCond one one = one := rfl

/-- The void rows: a false or undetermined antecedent yields the third value.
    Unlike RM3 and Gödel (0 → b = 1), there is no ex falso row. -/
theorem dfCond_not_one_void (a b : ThreeVal) (ha : a ≠ one) :
    dfCond a b = half := by
  cases a
  · rfl
  · rfl
  · exact absurd rfl ha

end ThreeVal

/-- The trivalent de Finetti conditional fails the conditional bridge:
    collapse of the min-copula conditional does not factor through dfCond
    on the collapsed values.  Corollary of no_truthfunctional_cond_bridge
    instantiated at dfCond. -/
theorem df_cond_fails_bridge :
    ¬ ∀ a b : Credence, ∀ hb : 0 < b.val,
      collapse (minCopulaCond a b hb) = ThreeVal.dfCond (collapse b) (collapse a) :=
  fun h => no_truthfunctional_cond_bridge ⟨ThreeVal.dfCond, h⟩

/-- The failing pair, exhibited: a = 7/10, b = 3/10.  The min-copula
    conditional is min(7/10, 3/10)/(3/10) = 1, which collapses to one,
    while dfCond(half, half) = half. -/
theorem df_cond_fails_at :
    ∃ a b : Credence, ∃ hb : 0 < b.val,
      collapse (minCopulaCond a b hb) ≠
      ThreeVal.dfCond (collapse b) (collapse a) := by
  refine ⟨⟨7/10, by norm_num, by norm_num⟩, ⟨3/10, by norm_num, by norm_num⟩,
    by norm_num, ?_⟩
  have hcond : minCopulaCond ⟨7/10, by norm_num, by norm_num⟩
      ⟨3/10, by norm_num, by norm_num⟩ (by norm_num : (0:ℝ) < 3/10) = 1 :=
    minCopulaCond_ge _ _ _ (by norm_num)
  rw [hcond, collapse_one]
  rw [collapse_interior ⟨3/10, by norm_num, by norm_num⟩ (by norm_num) (by norm_num)]
  rw [collapse_interior ⟨7/10, by norm_num, by norm_num⟩ (by norm_num) (by norm_num)]
  decide

/-! ## Ratio Agreement

With positive evidence and the coherence condition j ≤ e, the admissible set
is the singleton at the Bayesian ratio j/e: admissible conditioning agrees
with the ratio definition wherever the ratio is defined. -/

namespace Credence

/-- Ratio agreement: with positive evidence e and coherent joint j ≤ e,
    `Cond j e` is the singleton whose value is the ratio j.val / e.val.
    Corollary of cond_singleton_of_pos with the ratio explicit. -/
theorem cond_ratio_singleton (j e : Credence) (he : 0 < e.val)
    (hle : j.val ≤ e.val) :
    Cond j e = {c : Credence | c.val = j.val / e.val} := by
  rw [cond_singleton_of_pos j e he hle]
  ext c
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    ext
    exact h

end Credence

end Cred
