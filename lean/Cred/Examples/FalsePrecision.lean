/-
  Cred Examples: False Precision from a Hidden Joint Policy (issue #668)

  Marginals `a = 3/5`, `b = 7/10`. Two analysts each report a single confident
  number for `cred(A | B)`, differing only in an unstated joint policy:

  - Hidden independence: joint `= a ⊗ b = 21/50`, conditional `= (21/50)/(7/10)
    = 3/5 = a`. The posterior equals the prior; the evidence did nothing.
  - Hidden min (maximal positive dependence): joint `= min(a,b) = 3/5`,
    conditional `= (3/5)/(7/10) = 6/7`.

  The Cred audit refuses the single number. The joint is only known to its
  Fréchet band `[3/10, 3/5]`, so the conditional is the band `[3/7, 6/7]`. The
  two hidden-assumption point estimates `3/5` and `6/7` straddle the threshold
  `4/5`, which the audit flags as dependence-sensitive false precision; the
  low threshold `1/3` is robust across the whole band.

  Reuses the `Examples.RobustConditioning` marginals and band facts.
-/

import Cred.Examples.RobustConditioning
import Cred.Audit.AssumptionLedger

namespace Cred

namespace Examples

namespace FalsePrecision

open Cred.Credence
open Cred.Dependence
open Cred.Examples.RobustConditioning

/-! ## Hidden independence workflow -/

/-- Hidden independence: with the product joint `a ⊗ b = 21/50` and positive
    evidence `b`, the unique admissible conditional is the prior `a = 3/5`. The
    reported single number is `a`; the evidence is irrelevant. -/
theorem hidden_independence_conditional :
    Cond (a ⊗ b) b = {a} :=
  Cred.Audit.independence_makes_evidence_irrelevant a b b_pos

/-- The independence conditional, as a bare value: `(21/50)/(7/10) = 3/5`. -/
theorem hidden_independence_value :
    (a ⊗ b).val / b.val = 3 / 5 := by
  rw [conj_val, a_val, b_val]; norm_num

/-! ## Hidden min workflow -/

/-- The min joint value: `min(a, b) = 3/5`. -/
theorem hidden_min_joint : min a.val b.val = 3 / 5 := frechet_upper

/-- Hidden min: with the maximal-dependence joint `min(a,b) = 3/5` and positive
    evidence `b`, the reported single number is `(3/5)/(7/10) = 6/7`. -/
theorem hidden_min_conditional : min a.val b.val / b.val = 6 / 7 := by
  rw [hidden_min_joint, b_val]; norm_num

/-! ## Cred audit: the conditional band

The Fréchet joint band `[3/10, 3/5]` divides by `b = 7/10` to the conditional
band `[3/7, 6/7]`. Both hidden-assumption point estimates lie in this band:
`3/5 = 27/45` and `6/7 = 30/35`. -/

/-- The Cred audit conditional band: `[(3/10)/b, (3/5)/b] = [3/7, 6/7]`. -/
theorem cred_audit_interval :
    (3 / 10 : ℝ) / b.val = 3 / 7 ∧ (3 / 5 : ℝ) / b.val = 6 / 7 :=
  cond_interval

/-- Both hidden single numbers sit inside the audit band `[3/7, 6/7]`:
    the independence value `3/5` and the min value `6/7`. -/
theorem hidden_points_in_band :
    (3 / 7 : ℝ) ≤ 3 / 5 ∧ (3 / 5 : ℝ) ≤ 6 / 7 ∧
    (3 / 7 : ℝ) ≤ 6 / 7 ∧ (6 / 7 : ℝ) ≤ 6 / 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_refl _⟩

/-! ## Threshold verdicts -/

/-- The threshold `4/5` falls strictly inside the conditional band
    `(3/7, 6/7)`: the two hidden-assumption numbers `3/5 < 4/5` and `6/7 > 4/5`
    straddle it. The verdict is dependence-sensitive false precision. -/
theorem threshold_four_fifths_sensitive :
    (3 / 7 : ℝ) < 4 / 5 ∧ (4 / 5 : ℝ) < 6 / 7 ∧
    (3 / 5 : ℝ) < 4 / 5 ∧ (4 / 5 : ℝ) < 6 / 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- The low threshold `1/3` sits at or below the whole conditional band
    `[3/7, 6/7]`: `1/3 ≤ 3/7` and `1/3 ≤ 6/7`. The verdict is robust to the
    unknown joint policy. -/
theorem threshold_one_third_robust :
    (1 / 3 : ℝ) ≤ 3 / 7 ∧ (1 / 3 : ℝ) ≤ 6 / 7 :=
  robust_at_low_threshold

end FalsePrecision

end Examples

end Cred
