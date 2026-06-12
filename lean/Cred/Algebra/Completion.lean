/-
  Cred Algebra Completion: the value algebra is the completion of its rationals.

  Issue #549, completion part. The rational value algebra `RatUnit` is real-free
  (`Algebra/Rational.lean`); the hosted `Credence` algebra is its order-completion,
  the standard completion of the rationals to the reals that mathlib builds. Two
  facts close this, both reused from mathlib rather than rebuilt:
  - density: the rational values are dense in the credence interval
    (`rat_dense_in_credence`, from `exists_rat_near` and a nonexpansive clamp);
  - completeness: every credence-valued family has an infimum and a supremum
    (`credInf`/`credSup` are genuine glb/lub via mathlib's conditional completeness
    of the reals), which is what the inf/sup quantifiers use.
  By `commitment_conservation` (#580) the completion relocates the reals into the
  cut data; it does not remove them.
-/

import Cred.Algebra.Rational
import Cred.Predicate

namespace Cred
namespace RatUnit

/-- Clamp a rational into the unit interval. -/
def clamp (r : ℚ) : RatUnit := ⟨max 0 (min 1 r), by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

/-- The rational values are dense in the credence interval: every credence is
    approximated to any precision by a rational unit value. -/
theorem rat_dense_in_credence (c : Credence) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : RatUnit, |(toCredence q).val - c.val| < ε := by
  obtain ⟨r, hr⟩ := exists_rat_near c.val hε
  rw [abs_sub_comm] at hr
  refine ⟨clamp r, ?_⟩
  have h0c : (0 : ℝ) ≤ c.val := c.nonneg
  have h1c : c.val ≤ 1 := c.le_one
  have hcast : ((toCredence (clamp r)).val) = max 0 (min 1 (r : ℝ)) := by
    rw [toCredence_val]; simp only [clamp]; push_cast; rfl
  rw [hcast]
  have hproj : |max 0 (min 1 (r : ℝ)) - c.val| ≤ |(r : ℝ) - c.val| := by
    rcases le_total (r : ℝ) 0 with hr0 | hr0
    · have hcl : max 0 (min 1 (r : ℝ)) = 0 := by
        rw [min_eq_right (by linarith)]; exact max_eq_left hr0
      rw [hcl]
      rcases abs_cases ((0 : ℝ) - c.val) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases ((r : ℝ) - c.val) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [e1, e2] <;> linarith
    · rcases le_total 1 (r : ℝ) with hr1 | hr1
      · have hcl : max 0 (min 1 (r : ℝ)) = 1 := by
          rw [min_eq_left hr1]; exact max_eq_right (by norm_num)
        rw [hcl]
        rcases abs_cases ((1 : ℝ) - c.val) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
          rcases abs_cases ((r : ℝ) - c.val) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e1, e2] <;> linarith
      · have hcl : max 0 (min 1 (r : ℝ)) = (r : ℝ) := by
          rw [min_eq_right hr1]; exact max_eq_right hr0
        rw [hcl]
  linarith [hproj, hr]

/-- Completeness for the quantifiers: every credence-valued family over a nonempty
    index has an infimum below every instance and a supremum above every instance,
    the existing `credInf`/`credSup` (genuine glb/lub via mathlib's conditional
    completeness of the reals). This is the order completeness the inf/sup
    quantifiers need; the rational algebra completes to this. -/
theorem value_algebra_complete {α : Type*} [Nonempty α] (f : α → Credence) :
    (∀ a, (GradedPredicate.forall' f).val ≤ (f a).val) ∧
      (∀ a, (f a).val ≤ (GradedPredicate.exists' f).val) :=
  ⟨fun a => GradedPredicate.forall_le f a, fun a => GradedPredicate.le_exists f a⟩

end RatUnit
end Cred
