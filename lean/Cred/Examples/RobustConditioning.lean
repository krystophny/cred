/-
  Cred Examples: A Worked Robust-Conditioning Instance (issue #639)

  Marginals `a = 3/5` and `b = 7/10`. The supplied joint is unknown beyond its
  Fréchet band `[max(a+b-1,0), min(a,b)] = [3/10, 3/5]`. Conditioning on `b`
  (positive) maps this joint band to the conditional band `[3/7, 6/7]`.

  - At a low threshold `1/3` the whole conditional band sits above the
    threshold: the verdict is robust to the unknown dependence.
  - At a high threshold `4/5` the band straddles the threshold: the verdict is
    dependence-sensitive.

  Theorem names here are cited by the paper; keep them stable.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Examples

namespace RobustConditioning

open Cred.Credence

/-- First marginal `a = 3/5`. -/
noncomputable def a : Credence := Credence.mk' (3 / 5) (by norm_num) (by norm_num)

/-- Second marginal `b = 7/10` (the evidence). -/
noncomputable def b : Credence := Credence.mk' (7 / 10) (by norm_num) (by norm_num)

@[simp] theorem a_val : a.val = 3 / 5 := rfl
@[simp] theorem b_val : b.val = 7 / 10 := rfl

/-- The evidence `b` has positive credence. -/
theorem b_pos : 0 < b.val := by rw [b_val]; norm_num

/-! ## Fréchet band of the joint -/

/-- Fréchet lower joint value: `max(a + b - 1, 0) = 3/10`. -/
theorem frechet_lower : max (a.val + b.val - 1) 0 = 3 / 10 := by
  rw [a_val, b_val]; norm_num

/-- Fréchet upper joint value: `min a b = 3/5`. -/
theorem frechet_upper : min a.val b.val = 3 / 5 := by
  rw [a_val, b_val]; norm_num

/-- Product (independence) joint value: `(a ⊗ b).val = 21/50`. -/
theorem product_joint : (a ⊗ b).val = 21 / 50 := by
  rw [conj_val, a_val, b_val]; norm_num

/-! ## Conditional band

Dividing the joint band `[3/10, 3/5]` by the evidence `b = 7/10` gives the
conditional band `[3/7, 6/7]`. -/

/-- Conditional band lower endpoint: `(3/10) / (7/10) = 3/7`. -/
theorem cond_interval_lower : (3 / 10 : ℝ) / b.val = 3 / 7 := by
  rw [b_val]; norm_num

/-- Conditional band upper endpoint: `(3/5) / (7/10) = 6/7`. -/
theorem cond_interval_upper : (3 / 5 : ℝ) / b.val = 6 / 7 := by
  rw [b_val]; norm_num

/-- The conditional band `[3/7, 6/7]` as a single pair of facts. -/
theorem cond_interval :
    (3 / 10 : ℝ) / b.val = 3 / 7 ∧ (3 / 5 : ℝ) / b.val = 6 / 7 :=
  ⟨cond_interval_lower, cond_interval_upper⟩

/-! ## Robust vs. dependence-sensitive thresholds -/

/-- At the low threshold `1/3`, the whole conditional band `[3/7, 6/7]` lies at
    or above the threshold: `1/3 ≤ 3/7` and `1/3 ≤ 6/7`. The verdict is robust. -/
theorem robust_at_low_threshold :
    (1 / 3 : ℝ) ≤ 3 / 7 ∧ (1 / 3 : ℝ) ≤ 6 / 7 := by
  constructor <;> norm_num

/-- At the high threshold `4/5`, the threshold falls strictly inside the
    conditional band: `3/7 < 4/5 < 6/7`. The verdict is dependence-sensitive. -/
theorem sensitive_at_high_threshold :
    (3 / 7 : ℝ) < 4 / 5 ∧ (4 / 5 : ℝ) < 6 / 7 := by
  constructor <;> norm_num

end RobustConditioning

end Examples

end Cred
