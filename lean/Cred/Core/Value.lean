/-
  Cred Core: Credence Values (Axis B)

  Credences are values in [0,1] with:
  - Negation (complement): ~c = 1 - c
  - Independence product (multiplication on values): c₁ ⊗ c₂ = c₁.val * c₂.val.
    Under a probabilistic interpretation this equals cred(A ∧ B) only when A and B
    are independent; in general joint credence is a separate parameter.
  - Disjunction (De Morgan dual): c₁ ⊔ c₂ = ~(~c₁ ⊗ ~c₂)

  IMPORTANT: The binary operations ⊗ and ⊔ are algebraic operations on credence
  values; they do not, in general, determine joint credences of propositions
  from marginals alone. Under an independence assumption one may set
  cred(A ∧ B) = cred(A) ⊗ cred(B) (and similarly for disjunction), but in
  general joint credence is separate data (it is an explicit parameter in
  Conditioning, defined in Cred.Cond.Admissible).

  PAPER CROSS-REFERENCES (part1/paper.tex):
  -----------------------------------------
  thm:algebraic        → neg_neg, neg_zero, neg_one, conj_comm, conj_assoc, conj_one,
                         conj_zero, disj_comm, disj_assoc, disj_zero, disj_one,
                         de_morgan_conj, de_morgan_disj
  thm:idempotence      → conj_idempotent_iff
  thm:nondistrib       → conj_disj_not_distrib
  thm:liar             → liar_fixed_point
  thm:fixedunique      → neg_fixed_point_unique
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

namespace Cred

/-! ## Credence Type -/

/-- A credence is a real number in [0,1] -/
@[ext]
structure Credence where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

namespace Credence

instance : Zero Credence := ⟨⟨0, le_refl 0, zero_le_one⟩⟩
instance : One Credence := ⟨⟨1, zero_le_one, le_refl 1⟩⟩

@[simp] theorem zero_val : (0 : Credence).val = 0 := rfl
@[simp] theorem one_val : (1 : Credence).val = 1 := rfl

/-- Create a credence from a real, with proof of bounds -/
def mk' (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Credence := ⟨x, h0, h1⟩

/-! ## Negation (Complement) -/

/-- Negation: ~c = 1 - c -/
def neg (c : Credence) : Credence where
  val := 1 - c.val
  nonneg := by linarith [c.le_one]
  le_one := by linarith [c.nonneg]

prefix:80 "~" => neg

@[simp] theorem neg_val (c : Credence) : (~c).val = 1 - c.val := rfl

/-- Negation is involutive: ~~c = c -/
@[simp] theorem neg_neg (c : Credence) : ~~c = c := by
  ext
  simp only [neg_val]
  ring

/-- Negation of 0 is 1 -/
@[simp] theorem neg_zero : ~(0 : Credence) = 1 := by
  ext
  simp only [neg_val, zero_val, one_val]
  ring

/-- Negation of 1 is 0 -/
@[simp] theorem neg_one : ~(1 : Credence) = 0 := by
  ext
  simp only [neg_val, one_val, zero_val]
  ring

/-! ## Conjunction (Multiplication) -/

/-- Conjunction: c₁ ⊗ c₂ (product of credences) -/
def conj (c₁ c₂ : Credence) : Credence where
  val := c₁.val * c₂.val
  nonneg := mul_nonneg c₁.nonneg c₂.nonneg
  le_one := by
    calc c₁.val * c₂.val ≤ c₁.val * 1 := by apply mul_le_mul_of_nonneg_left c₂.le_one c₁.nonneg
                        _ = c₁.val := mul_one _
                        _ ≤ 1 := c₁.le_one

infixl:70 " ⊗ " => conj

@[simp] theorem conj_val (c₁ c₂ : Credence) : (c₁ ⊗ c₂).val = c₁.val * c₂.val := rfl

/-- Conjunction is commutative -/
theorem conj_comm (c₁ c₂ : Credence) : c₁ ⊗ c₂ = c₂ ⊗ c₁ := by
  ext
  simp only [conj_val]
  ring

/-- Conjunction is associative -/
theorem conj_assoc (c₁ c₂ c₃ : Credence) : (c₁ ⊗ c₂) ⊗ c₃ = c₁ ⊗ (c₂ ⊗ c₃) := by
  ext
  simp only [conj_val]
  ring

/-- 1 is the identity for conjunction -/
@[simp] theorem conj_one (c : Credence) : c ⊗ 1 = c := by
  ext
  simp only [conj_val, one_val, mul_one]

@[simp] theorem one_conj (c : Credence) : (1 : Credence) ⊗ c = c := by
  rw [conj_comm, conj_one]

/-- 0 is absorbing for conjunction -/
@[simp] theorem conj_zero (c : Credence) : c ⊗ 0 = 0 := by
  ext
  simp only [conj_val, zero_val, mul_zero]

@[simp] theorem zero_conj (c : Credence) : (0 : Credence) ⊗ c = 0 := by
  rw [conj_comm, conj_zero]

/-! ## Ordering -/

instance : LE Credence := ⟨fun c₁ c₂ => c₁.val ≤ c₂.val⟩
instance : LT Credence := ⟨fun c₁ c₂ => c₁.val < c₂.val⟩

theorem le_def (c₁ c₂ : Credence) : c₁ ≤ c₂ ↔ c₁.val ≤ c₂.val := Iff.rfl
theorem lt_def (c₁ c₂ : Credence) : c₁ < c₂ ↔ c₁.val < c₂.val := Iff.rfl

/-- 0 ≤ c for all credences -/
theorem zero_le (c : Credence) : (0 : Credence) ≤ c := c.nonneg

/-- c ≤ 1 for all credences -/
theorem le_one' (c : Credence) : c ≤ (1 : Credence) := c.le_one

/-- Negation reverses order -/
theorem neg_le_neg_iff (c₁ c₂ : Credence) : c₁ ≤ c₂ ↔ ~c₂ ≤ ~c₁ := by
  simp only [le_def, neg_val]
  constructor <;> intro h <;> linarith

instance : Preorder Credence where
  le_refl c := le_refl c.val
  le_trans _ _ _ h1 h2 := le_trans (α := ℝ) h1 h2
  lt_iff_le_not_le c₁ c₂ := by
    simp only [le_def, lt_def]
    exact lt_iff_le_not_le

instance : PartialOrder Credence where
  le_antisymm c₁ c₂ h1 h2 := by
    ext
    exact le_antisymm (α := ℝ) h1 h2

/-- Conjunction idempotent only at 0 and 1 -/
theorem conj_idempotent_iff (c : Credence) : c ⊗ c = c ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have hv : c.val * c.val = c.val := congrArg (·.val) h
    simp only [conj_val] at hv
    have hsub : c.val * (c.val - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp hsub with hz | h1
    · left; ext; exact hz
    · right; ext; simp only [one_val]; linarith
  · intro h
    rcases h with rfl | rfl
    · simp
    · simp

/-! ## Fixed Points -/

/-- The fixed point credence for self-referential negation: L = ~L implies L = 1/2 -/
noncomputable def half : Credence where
  val := (1 : ℝ) / 2
  nonneg := by norm_num
  le_one := by norm_num

@[simp] theorem half_val : half.val = (1 : ℝ) / 2 := rfl

/-- Conjunction is NOT idempotent: c ⊗ c ≠ c in general (fails at 1/2) -/
theorem conj_not_idempotent : ∃ c : Credence, c ⊗ c ≠ c := by
  use half
  intro h
  have : half.val * half.val = half.val := congrArg (·.val) h
  simp only [half_val] at this
  norm_num at this

/-- The liar sentence has credence 1/2 -/
theorem liar_fixed_point : ~half = half := by
  ext
  simp only [neg_val, half_val]
  ring

/-- 1/2 is the unique fixed point of negation -/
theorem neg_fixed_point_unique (c : Credence) (h : ~c = c) : c = half := by
  ext
  have hval : c.val = 1 - c.val := by
    have := congrArg val h
    simp only [neg_val] at this
    exact this.symm
  simp only [half_val]
  linarith

/-! ## Disjunction (De Morgan dual) -/

/-- Disjunction via De Morgan: A ∨ B = ~(~A ⊗ ~B) -/
def disj (c₁ c₂ : Credence) : Credence := ~(~c₁ ⊗ ~c₂)

infixl:65 " ⊔ " => disj

theorem disj_val (c₁ c₂ : Credence) : (c₁ ⊔ c₂).val = c₁.val + c₂.val - c₁.val * c₂.val := by
  simp only [disj, neg_val, conj_val]
  ring

/-- Disjunction is commutative -/
theorem disj_comm (c₁ c₂ : Credence) : c₁ ⊔ c₂ = c₂ ⊔ c₁ := by
  ext
  simp only [disj_val]
  ring

/-- Disjunction is associative -/
theorem disj_assoc (c₁ c₂ c₃ : Credence) : (c₁ ⊔ c₂) ⊔ c₃ = c₁ ⊔ (c₂ ⊔ c₃) := by
  ext
  simp only [disj_val]
  ring

/-- 0 is identity for disjunction -/
@[simp] theorem disj_zero (c : Credence) : c ⊔ 0 = c := by
  ext
  simp only [disj_val, zero_val, mul_zero, add_zero, sub_zero]

@[simp] theorem zero_disj (c : Credence) : (0 : Credence) ⊔ c = c := by
  rw [disj_comm, disj_zero]

/-- 1 is absorbing for disjunction -/
@[simp] theorem disj_one (c : Credence) : c ⊔ 1 = 1 := by
  ext
  simp only [disj_val, one_val, mul_one]
  linarith [c.le_one]

@[simp] theorem one_disj (c : Credence) : (1 : Credence) ⊔ c = 1 := by
  rw [disj_comm, disj_one]

/-- De Morgan: ~(A ⊗ B) = ~A ⊔ ~B -/
theorem de_morgan_conj (c₁ c₂ : Credence) : ~(c₁ ⊗ c₂) = ~c₁ ⊔ ~c₂ := by
  ext
  simp only [neg_val, conj_val, disj_val]
  ring

/-- De Morgan: ~(A ⊔ B) = ~A ⊗ ~B -/
theorem de_morgan_disj (c₁ c₂ : Credence) : ~(c₁ ⊔ c₂) = ~c₁ ⊗ ~c₂ := by
  simp only [disj]
  exact neg_neg _

/-! ## Non-Distributivity

Unlike Boolean algebra, conjunction does NOT distribute over disjunction
in general (and vice versa). This is a key feature of graded logic.
-/

/-- Conjunction does NOT distribute over disjunction in general -/
theorem conj_disj_not_distrib :
    ∃ c₁ c₂ c₃ : Credence, c₁ ⊗ (c₂ ⊔ c₃) ≠ (c₁ ⊗ c₂) ⊔ (c₁ ⊗ c₃) := by
  use half, half, half
  intro h
  have heq : (half ⊗ (half ⊔ half)).val = ((half ⊗ half) ⊔ (half ⊗ half)).val :=
    congrArg (·.val) h
  simp only [conj_val, disj_val, half_val] at heq
  norm_num at heq

/-! ## Spread (Bernoulli Variance)

The expression c * (1-c) is the variance of a Bernoulli random variable with
parameter c. This is a well-known quantity in probability theory.

Algebraically, c ⊗ ~c applies the independence conjunction to a credence and
its complement. This does NOT compute cred(A ∧ ~A), which is always 0 (a
contradiction is impossible). Rather, it is a derived algebraic quantity
measuring how far a credence is from certainty.

Properties:
- Maximum value 1/4 at c = 1/2 (maximum uncertainty)
- Zero at c = 0 or c = 1 (certainty)
- The De Morgan dual c ⊔ ~c = 1 - c*(1-c) is the certainty (min 3/4 at c=1/2)
-/

/-- Spread (Bernoulli variance): c ⊗ ~c = c * (1-c). Measures distance from certainty. -/
def spread (c : Credence) : Credence := c ⊗ ~c

theorem spread_val (c : Credence) : (spread c).val = c.val * (1 - c.val) := by
  simp only [spread, conj_val, neg_val]

/-- Maximum spread at c = 1/2 gives 1/4 (maximum uncertainty) -/
theorem spread_half : (spread half).val = (1 : ℝ) / 4 := by
  simp only [spread_val, half_val]
  norm_num

/-- Spread is always ≤ 1/4 -/
theorem spread_le_quarter (c : Credence) :
    (spread c).val ≤ (1 : ℝ) / 4 := by
  simp only [spread_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - (1 : ℝ) / 2)]

/-- Spread is 0 only at extremes (certainty) -/
theorem spread_eq_zero_iff (c : Credence) :
    spread c = 0 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have hv : c.val * (1 - c.val) = 0 := by
      have := congrArg (·.val) h
      simp only [spread_val, zero_val] at this
      exact this
    rcases mul_eq_zero.mp hv with hz | h1
    · left; ext; exact hz
    · right; ext; simp only [one_val]; linarith
  · intro h
    rcases h with rfl | rfl
    · ext; simp [spread_val]
    · ext; simp [spread_val]

/-- Certainty: c ⊔ ~c = 1 - c*(1-c). De Morgan dual of spread. -/
def certainty (c : Credence) : Credence := c ⊔ ~c

theorem certainty_val (c : Credence) : (certainty c).val = 1 - c.val * (1 - c.val) := by
  simp only [certainty, disj_val, neg_val]
  ring

/-- Certainty equals 1 at extremes -/
theorem certainty_zero : certainty (0 : Credence) = 1 := by
  ext
  simp only [certainty_val, zero_val, one_val]
  norm_num

theorem certainty_one : certainty (1 : Credence) = 1 := by
  ext
  simp only [certainty_val, one_val, sub_self, mul_zero, sub_zero]

/-- Minimum certainty at half gives 3/4 (maximum uncertainty) -/
theorem certainty_half : (certainty half).val = (3 : ℝ) / 4 := by
  simp only [certainty_val, half_val]
  norm_num

/-- Certainty is always at least 3/4 -/
theorem certainty_ge_three_quarters (c : Credence) :
    (certainty c).val ≥ (3 : ℝ) / 4 := by
  simp only [certainty_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - (1 : ℝ) / 2)]

/-- Certainty equals 1 only at extremes -/
theorem certainty_eq_one_iff (c : Credence) :
    certainty c = 1 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have hv : 1 - c.val * (1 - c.val) = 1 := by
      have := congrArg (·.val) h
      simp only [certainty_val, one_val] at this
      exact this
    have hzero : c.val * (1 - c.val) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hz | h1
    · left; ext; exact hz
    · right; ext; simp only [one_val]; linarith
  · intro h
    rcases h with rfl | rfl
    · exact certainty_zero
    · exact certainty_one

/-! ### Dynamics: Self-Conjunction and Self-Disjunction

Self-conjunction strictly decreases interior credences (c² < c for c ∈ (0,1)),
self-disjunction strictly increases them (c ⊔ c > c for c ∈ (0,1)),
and the power sequence c^n is strictly decreasing for interior credences.
These facts formalize the "three attractors" picture:
- {0,1} are the conjunction-idempotent fixed points (Theorem conj_idempotent_iff)
- {1/2} is the negation fixed point (Theorem neg_fixed_point_unique)
- Interior credences are driven toward 0 by self-conjunction and toward 1
  by self-disjunction. -/

/-- Self-conjunction strictly decreases interior credences: c² < c for c ∈ (0,1). -/
theorem self_conj_lt (c : Credence) (h0 : 0 < c.val) (h1 : c.val < 1) :
    (c ⊗ c).val < c.val := by
  simp only [conj_val]
  nlinarith

/-- Self-disjunction strictly increases interior credences: c ⊔ c > c for c ∈ (0,1). -/
theorem self_disj_gt (c : Credence) (h0 : 0 < c.val) (h1 : c.val < 1) :
    c.val < (c ⊔ c).val := by
  simp only [disj_val]
  nlinarith

/-- Powers of interior credences are strictly decreasing: c^(n+1) < c^n for c ∈ (0,1). -/
theorem pow_strictly_decreasing (c : Credence) (h0 : 0 < c.val) (h1 : c.val < 1) (n : ℕ) :
    c.val ^ (n + 1) < c.val ^ n := by
  rw [pow_succ]
  calc c.val ^ n * c.val < c.val ^ n * 1 :=
        mul_lt_mul_of_pos_left h1 (pow_pos h0 n)
    _ = c.val ^ n := mul_one _

/-- The equilibria {0, 1/2, 1} are exactly the conjunction-idempotent values
    together with the negation fixed point. -/
theorem equilibria_characterization (c : Credence) :
    (c ⊗ c = c ∨ ~c = c) ↔ (c = 0 ∨ c = 1 ∨ c = half) := by
  constructor
  · intro h
    rcases h with hconj | hneg
    · rcases (conj_idempotent_iff c).mp hconj with rfl | rfl
      · left; rfl
      · right; left; rfl
    · right; right; exact neg_fixed_point_unique c hneg
  · intro h
    rcases h with rfl | rfl | rfl
    · left; simp
    · left; simp
    · right; exact liar_fixed_point

end Credence

end Cred
