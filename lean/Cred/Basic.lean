/-
  Cred: A Foundation for Graded Mathematics

  This formalizes the credence algebra and its core properties.
  Credences are values in [0,1] with:
  - Conjunction (multiplication): assumes independence, i.e., cred(A) * cred(B)
  - Negation (complement): ~c = 1 - c
  - Disjunction (De Morgan): c₁ + c₂ - c₁*c₂ (independence formula)
  - Conditioning (primitive, via chain rule)

  PHILOSOPHY: Inference as Constraint
  -----------------------------------
  Inference narrows possibilities from uncertainty toward specificity.
  - Prior: Start with maximal uncertainty (flat prior, credence 0.5)
  - Evidence constrains: Each piece of evidence narrows consistent beliefs
  - No evidence = no constraint: Credence 0 evidence cannot narrow anything

  This is why conditioning is primitive (inference IS constraining) and why
  there is no ex falso (impossible evidence provides no constraint).

  IMPORTANT: The binary operations ⊗ and ⊔ compute the credence of conjunctions
  and disjunctions under an INDEPENDENCE assumption. For dependent propositions,
  the joint credence cred(A ∧ B) ≠ cred(A) * cred(B) in general.

  The Conditioning structure handles the general case where joint credences
  are provided as parameters, not computed from marginals.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
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

/-- Conjunction: c₁ * c₂ (product of credences) -/
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

/-! ## Conditioning (Primitive) -/

/--
Conditioning is a primitive operation satisfying the chain rule.

Parameters:
- `joint`: the credence cred(A ∧ B) of the conjunction (given, not computed)
- `evidence`: the credence cred(B) of the evidence

The chain rule states: cred(A | B) * cred(B) = cred(A ∧ B)

Note: `joint` is NOT assumed to equal `evidence * something`; it is an
independent parameter representing the actual joint credence, which may
differ from the product of marginals for dependent propositions.

Edge case when evidence = 0:
The chain rule requires condCred * 0 = joint. Since anything times 0 equals 0,
this forces joint = 0 but leaves condCred unconstrained (any value satisfies
c * 0 = 0). Conditioning on impossible evidence provides no constraint on belief.
See `conditioning_zero_any` for the proof that any credence works.
This is intentional: there is no ex falso in graded logic.
-/
structure Conditioning (joint evidence : Credence) where
  /-- The conditional credence cred(A | B) -/
  condCred : Credence
  /-- Chain rule: cred(A | B) * cred(B) = cred(A ∧ B) -/
  chainRule : condCred ⊗ evidence = joint

/-- When evidence = 0, any conditioning produces 0 -/
theorem conditioning_zero_trivial (c : Credence) :
    c ⊗ (0 : Credence) = 0 := by simp

/-- When evidence = 0, conditioning requires joint = 0, but condCred is unconstrained -/
theorem conditioning_zero_any (c : Credence) :
    ∃ cond : Conditioning 0 0, cond.condCred = c := by
  use ⟨c, by simp⟩

/-- When evidence = 0, the chain rule forces joint = 0 -/
theorem conditioning_zero_forces_joint_zero (joint : Credence)
    (cond : Conditioning joint 0) : joint = 0 := by
  have h := cond.chainRule
  simp only [conj_zero] at h
  exact h.symm

/-- When evidence = 1, cred(A | B) = cred(A ∧ B) -/
theorem conditioning_one (joint : Credence) :
    ∃ cond : Conditioning joint 1, cond.condCred = joint := by
  use ⟨joint, by simp⟩

/-- Construct conditioning when evidence > 0 and joint ≤ evidence -/
noncomputable def conditioning_mk (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) : Conditioning joint evidence where
  condCred := ⟨joint.val / evidence.val,
    div_nonneg joint.nonneg (le_of_lt h_pos),
    by rw [div_le_one h_pos]; exact h_le⟩
  chainRule := by ext; simp only [conj_val]; field_simp

/-- If a Conditioning structure exists, then joint ≤ evidence.
    Proof: joint = condCred * evidence ≤ 1 * evidence = evidence.
    Note: For evidence > 0, this is the converse of conditioning_mk precondition.
    For evidence = 0, conditioning_zero_forces_joint_zero gives the stronger result joint = 0. -/
theorem conditioning_implies_joint_le_evidence (joint evidence : Credence)
    (cond : Conditioning joint evidence) : joint.val ≤ evidence.val := by
  have h := congrArg (·.val) cond.chainRule
  simp only [conj_val] at h
  calc joint.val = cond.condCred.val * evidence.val := h.symm
    _ ≤ 1 * evidence.val := by
        apply mul_le_mul_of_nonneg_right cond.condCred.le_one evidence.nonneg
    _ = evidence.val := one_mul _

/-- Uniqueness of conditioning when evidence > 0 -/
theorem conditioning_unique (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (c₁ c₂ : Conditioning joint evidence) : c₁.condCred = c₂.condCred := by
  ext
  have h1 := congrArg (·.val) c₁.chainRule
  have h2 := congrArg (·.val) c₂.chainRule
  simp only [conj_val] at h1 h2
  have heq : c₁.condCred.val * evidence.val = c₂.condCred.val * evidence.val := by
    rw [h1, h2]
  have hne : evidence.val ≠ 0 := ne_of_gt h_pos
  calc c₁.condCred.val = c₁.condCred.val * evidence.val / evidence.val := by field_simp
    _ = c₂.condCred.val * evidence.val / evidence.val := by rw [heq]
    _ = c₂.condCred.val := by field_simp

/-! ## Fixed Points -/

/-- The fixed point credence for self-referential negation: L = ~L implies L = 0.5 -/
def half : Credence where
  val := 0.5
  nonneg := by norm_num
  le_one := by norm_num

@[simp] theorem half_val : half.val = 0.5 := rfl

/-- Conjunction is NOT idempotent: c ⊗ c ≠ c in general (fails at 0.5) -/
theorem conj_not_idempotent : ∃ c : Credence, c ⊗ c ≠ c := by
  use half
  intro h
  have : half.val * half.val = half.val := congrArg (·.val) h
  simp only [half_val] at this
  norm_num at this

/-- The liar sentence has credence 0.5 -/
theorem liar_fixed_point : ~half = half := by
  ext
  simp only [neg_val, half_val]
  ring

/-- 0.5 is the unique fixed point of negation -/
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
  have hlhs : (half ⊗ (half ⊔ half)).val = 0.5 * (0.5 + 0.5 - 0.5 * 0.5) := by
    simp only [conj_val, disj_val, half_val]
  have hrhs : ((half ⊗ half) ⊔ (half ⊗ half)).val =
      0.5 * 0.5 + 0.5 * 0.5 - (0.5 * 0.5) * (0.5 * 0.5) := by
    simp only [conj_val, disj_val, half_val]
  have heq : (half ⊗ (half ⊔ half)).val = ((half ⊗ half) ⊔ (half ⊗ half)).val :=
    congrArg (·.val) h
  simp only [hlhs, hrhs] at heq
  norm_num at heq

/-! ## Spread (Bernoulli Variance)

The expression c * (1-c) is the variance of a Bernoulli random variable with
parameter c. This is a well-known quantity in probability theory.

Algebraically, c ⊗ ~c applies the independence conjunction to a credence and
its complement. This does NOT compute cred(A ∧ ~A), which is always 0 (a
contradiction is impossible). Rather, it is a derived algebraic quantity
measuring how far a credence is from certainty.

Properties:
- Maximum value 0.25 at c = 0.5 (maximum uncertainty)
- Zero at c = 0 or c = 1 (certainty)
- The De Morgan dual c ⊔ ~c = 1 - c*(1-c) is the certainty (min 0.75 at c=0.5)
-/

/-- Spread (Bernoulli variance): c ⊗ ~c = c * (1-c). Measures distance from certainty. -/
def spread (c : Credence) : Credence := c ⊗ ~c

theorem spread_val (c : Credence) : (spread c).val = c.val * (1 - c.val) := by
  simp only [spread, conj_val, neg_val]

/-- Maximum spread at c = 0.5 gives 0.25 (maximum uncertainty) -/
theorem spread_half : (spread half).val = 0.25 := by
  simp only [spread_val, half_val]
  norm_num

/-- Spread is always ≤ 0.25 -/
theorem spread_le_quarter (c : Credence) :
    (spread c).val ≤ 0.25 := by
  simp only [spread_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - 0.5)]

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

/-- Minimum certainty at half gives 0.75 (maximum uncertainty) -/
theorem certainty_half : (certainty half).val = 0.75 := by
  simp only [certainty_val, half_val]
  norm_num

/-- Certainty is always at least 0.75 -/
theorem certainty_ge_three_quarters (c : Credence) :
    (certainty c).val ≥ 0.75 := by
  simp only [certainty_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - 0.5)]

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

end Credence

/-! ## Three-Valued Collapse

The three-valued collapse maps [0,1] to {0, 0.5, 1}:
- 0 maps to 0
- (0,1) maps to 0.5
- 1 maps to 1

This collapsed algebra matches RM3 for {negation, conjunction, disjunction},
but differs on implication: RM3 has 0 → b = 1 (ex falso), while Cred
conditioning on 0 is unconstrained.
-/

/-- Three-valued credence type -/
inductive ThreeVal where
  | zero : ThreeVal
  | half : ThreeVal
  | one : ThreeVal
deriving DecidableEq, Repr

namespace ThreeVal

/-- Negation on three values (matches Cred and RM3) -/
def neg : ThreeVal → ThreeVal
  | zero => one
  | half => half
  | one => zero

/-- Conjunction on three values (matches RM3 min) -/
def conj : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => zero
  | _, zero => zero
  | one, b => b
  | a, one => a
  | half, half => half

/-- Disjunction on three values (matches RM3 max) -/
def disj : ThreeVal → ThreeVal → ThreeVal
  | one, _ => one
  | _, one => one
  | zero, b => b
  | a, zero => a
  | half, half => half

/-- Negation is involutive -/
theorem neg_neg (v : ThreeVal) : neg (neg v) = v := by
  cases v <;> rfl

/-- 0 is absorbing for conjunction -/
theorem conj_zero (v : ThreeVal) : conj zero v = zero := by
  cases v <;> rfl

theorem zero_conj (v : ThreeVal) : conj v zero = zero := by
  cases v <;> rfl

/-- 1 is identity for conjunction -/
theorem conj_one (v : ThreeVal) : conj one v = v := by
  cases v <;> rfl

theorem one_conj (v : ThreeVal) : conj v one = v := by
  cases v <;> rfl

/-- half ∧ half = half (key RM3 property) -/
theorem conj_half_half : conj half half = half := by rfl

/-- 1 is absorbing for disjunction -/
theorem disj_one (v : ThreeVal) : disj one v = one := by
  cases v <;> rfl

theorem one_disj (v : ThreeVal) : disj v one = one := by
  cases v <;> rfl

/-- 0 is identity for disjunction -/
theorem disj_zero (v : ThreeVal) : disj zero v = v := by
  cases v <;> rfl

theorem zero_disj (v : ThreeVal) : disj v zero = v := by
  cases v <;> rfl

/-- half ∨ half = half (key RM3 property) -/
theorem disj_half_half : disj half half = half := by rfl

/-- De Morgan law -/
theorem de_morgan_conj (a b : ThreeVal) : neg (conj a b) = disj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem de_morgan_disj (a b : ThreeVal) : neg (disj a b) = conj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- RM3 implication (for comparison - NOT used in Cred) -/
def rm3_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one  -- Ex falso!
  | half, zero => half
  | half, half => half
  | half, one => one
  | one, zero => zero
  | one, half => half
  | one, one => one

/-- RM3 has ex falso: 0 → b = 1 for all b -/
theorem rm3_ex_falso (b : ThreeVal) : rm3_impl zero b = one := by
  cases b <;> rfl

/-! ### Complete RM3 Implication Table (Theorem 6.2)

The following 9 theorems verify every entry in the RM3 implication table:
       | 0 | 1/2 | 1
   ----+---+-----+---
   0   | 1 |  1  | 1    (ex falso row)
   1/2 |1/2| 1/2 | 1
   1   | 0 | 1/2 | 1
-/

theorem rm3_impl_zero_zero : rm3_impl zero zero = one := rfl
theorem rm3_impl_zero_half : rm3_impl zero half = one := rfl
theorem rm3_impl_zero_one : rm3_impl zero one = one := rfl
theorem rm3_impl_half_zero : rm3_impl half zero = half := rfl
theorem rm3_impl_half_half : rm3_impl half half = half := rfl
theorem rm3_impl_half_one : rm3_impl half one = one := rfl
theorem rm3_impl_one_zero : rm3_impl one zero = zero := rfl
theorem rm3_impl_one_half : rm3_impl one half = half := rfl
theorem rm3_impl_one_one : rm3_impl one one = one := rfl

/-- Cred conditioning on 0 is NOT forced to 1 (blocks ex falso).
    Any credence value can serve as the conditional when evidence = 0. -/
theorem cred_no_ex_falso (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

end ThreeVal

/-! ### Cred Conditioning at Special Values (Theorem 6.2)

Cred conditioning differs from RM3 implication in two key ways:
1. When evidence = 0: conditioning is unconstrained (any value works)
2. When evidence > 0: conditioning is uniquely determined

The table from the paper (with * = unconstrained):
       | 0 | 1/2 | 1
   ----+---+-----+---
   0   | * |  *  | *     (any value satisfies chain rule)
   1/2 | 0 |1/2,1| 1     (determined: joint/evidence)
   1   | 0 | 1/2 | 1     (determined: joint/evidence)

Note: The 1/2,1 entry means cred(A|B) depends on cred(A and B):
- If joint = 1/4, then 1/4 / 1/2 = 1/2
- If joint = 1/2, then 1/2 / 1/2 = 1
-/

namespace Credence

/-! #### Row 1: Evidence = 0 (unconstrained) -/

/-- When evidence = 0, conditioning to 0 is unconstrained -/
theorem cond_zero_zero_any (c : Credence) :
    ∃ cond : Conditioning 0 0, cond.condCred = c :=
  conditioning_zero_any c

/-- When evidence = 0, conditioning to half is unconstrained -/
theorem cond_zero_half_any (c : Credence) :
    ∃ cond : Conditioning 0 0, cond.condCred = c :=
  conditioning_zero_any c

/-- When evidence = 0, conditioning to one is unconstrained -/
theorem cond_zero_one_any (c : Credence) :
    ∃ cond : Conditioning 0 0, cond.condCred = c :=
  conditioning_zero_any c

/-! #### Row 2 and 3: Evidence > 0 (determined)

When evidence > 0, the conditional credence is uniquely determined
by the chain rule: cred(A|B) = cred(A and B) / cred(B).
-/

/-- When evidence > 0, conditioning is uniquely determined -/
theorem cond_pos_unique (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (c₁ c₂ : Conditioning joint evidence) : c₁.condCred = c₂.condCred :=
  conditioning_unique joint evidence h_pos c₁ c₂

/-- When evidence = 1, cred(A|1) = cred(A and 1) = joint -/
theorem cond_evidence_one (joint : Credence) :
    ∃ cond : Conditioning joint 1, cond.condCred = joint :=
  conditioning_one joint

/-- Specific case: cred(1|1) = 1 -/
theorem cond_one_one : ∃ cond : Conditioning 1 1, cond.condCred = (1 : Credence) := by
  exact conditioning_one 1

/-- Specific case: cred(0|1) = 0 -/
theorem cond_zero_evidence_one : ∃ cond : Conditioning 0 1, cond.condCred = (0 : Credence) := by
  exact conditioning_one 0

/-- Specific case: cred(half|1) = half -/
theorem cond_half_evidence_one : ∃ cond : Conditioning half 1, cond.condCred = half := by
  exact conditioning_one half

/-- When evidence = half and joint = 0, cred(A|half) = 0 -/
theorem cond_zero_half : ∃ cond : Conditioning 0 half, cond.condCred = (0 : Credence) := by
  refine ⟨⟨0, ?_⟩, rfl⟩
  ext
  simp only [conj_val, zero_val, zero_mul]

/-- When evidence = half and joint = half, cred(A|half) = 1 -/
theorem cond_half_half : ∃ cond : Conditioning half half, cond.condCred = (1 : Credence) := by
  refine ⟨⟨1, ?_⟩, rfl⟩
  ext
  simp only [conj_val, one_val, one_mul, half_val]

/-- Alternative: When joint = 1/4 and evidence = half, cred(A|half) = 1/2.
    This shows the conditioning value depends on the joint credence. -/
def quarter : Credence where
  val := 0.25
  nonneg := by norm_num
  le_one := by norm_num

@[simp] theorem quarter_val : quarter.val = 0.25 := rfl

theorem cond_quarter_half : ∃ cond : Conditioning quarter half, cond.condCred = half := by
  refine ⟨⟨half, ?_⟩, rfl⟩
  ext
  simp only [conj_val, half_val, quarter_val]
  norm_num

/-- When evidence = 1 and joint = 0, cred(A|1) = 0 -/
theorem cond_joint_zero_evidence_one :
    ∃ cond : Conditioning 0 1, cond.condCred = (0 : Credence) :=
  conditioning_one 0

/-- When evidence = 1 and joint = half, cred(A|1) = half -/
theorem cond_joint_half_evidence_one :
    ∃ cond : Conditioning half 1, cond.condCred = half :=
  conditioning_one half

/-- When evidence = 1 and joint = 1, cred(A|1) = 1 -/
theorem cond_joint_one_evidence_one :
    ∃ cond : Conditioning 1 1, cond.condCred = (1 : Credence) :=
  conditioning_one 1

/-! #### Summary: RM3 vs Cred Comparison

Key differences verified:
1. RM3: 0 → b = 1 for all b (ex falso quodlibet)
   Lean: rm3_impl_zero_zero, rm3_impl_zero_half, rm3_impl_zero_one
2. Cred: cred(b|0) is unconstrained (any value satisfies chain rule)
   Lean: cond_zero_zero_any, cond_zero_half_any, cond_zero_one_any
3. When evidence > 0, Cred conditioning is uniquely determined
   Lean: cond_pos_unique

This proves the comparison table in Theorem 6.2 of the paper.
-/

end Credence

/-! ## Three-Valued Collapse Homomorphism

The collapse function maps the continuous [0,1] credence algebra to the discrete
three-valued algebra. This section proves that collapse is a homomorphism for
negation, conjunction, and disjunction (Theorem 6.1 in the paper).

Key insight: The operations on ThreeVal are defined as min/max on {0, 0.5, 1},
which exactly matches what happens when Cred operations are applied to these
boundary values and then collapsed.
-/

/-- Collapse maps Credence to ThreeVal: 0 → zero, 1 → one, else → half -/
noncomputable def collapse (c : Credence) : ThreeVal :=
  if c.val = 0 then ThreeVal.zero
  else if c.val = 1 then ThreeVal.one
  else ThreeVal.half

/-- Collapse of 0 is zero -/
@[simp] theorem collapse_zero : collapse (0 : Credence) = ThreeVal.zero := by
  unfold collapse
  simp only [Credence.zero_val, ↓reduceIte]

/-- Collapse of 1 is one -/
@[simp] theorem collapse_one : collapse (1 : Credence) = ThreeVal.one := by
  unfold collapse
  simp only [Credence.one_val, one_ne_zero, ↓reduceIte]

/-- Collapse of half is half -/
@[simp] theorem collapse_half : collapse Credence.half = ThreeVal.half := by
  unfold collapse
  simp only [Credence.half_val, ↓reduceIte]
  norm_num

/-- Helper: c.val in open interval (0,1) implies collapse c = half -/
theorem collapse_interior (c : Credence) (h0 : c.val ≠ 0) (h1 : c.val ≠ 1) :
    collapse c = ThreeVal.half := by
  unfold collapse
  simp only [h0, h1, ↓reduceIte]

/-! ### Negation Homomorphism -/

/-- Collapse respects negation: collapse(~c) = ThreeVal.neg(collapse c) -/
theorem collapse_neg (c : Credence) : collapse (~c) = ThreeVal.neg (collapse c) := by
  by_cases h0 : c.val = 0
  · have hc : c = 0 := by ext; exact h0
    subst hc
    simp only [Credence.neg_zero, collapse_one, collapse_zero, ThreeVal.neg]
  · by_cases h1 : c.val = 1
    · have hc : c = 1 := by ext; exact h1
      subst hc
      simp only [Credence.neg_one, collapse_zero, collapse_one, ThreeVal.neg]
    · have hcoll : collapse c = ThreeVal.half := collapse_interior c h0 h1
      have hneg_ne_zero : (~c).val ≠ 0 := by
        simp only [Credence.neg_val]
        intro heq
        have : c.val = 1 := by linarith
        exact h1 this
      have hneg_ne_one : (~c).val ≠ 1 := by
        simp only [Credence.neg_val]
        intro heq
        have : c.val = 0 := by linarith
        exact h0 this
      have hcoll_neg : collapse (~c) = ThreeVal.half :=
        collapse_interior (~c) hneg_ne_zero hneg_ne_one
      simp only [hcoll, hcoll_neg, ThreeVal.neg]

/-! ### Conjunction Homomorphism -/

/-- Collapse respects conjunction: collapse(c1 ⊗ c2) = ThreeVal.conj(collapse c1)(collapse c2) -/
theorem collapse_conj (c₁ c₂ : Credence) :
    collapse (c₁ ⊗ c₂) = ThreeVal.conj (collapse c₁) (collapse c₂) := by
  by_cases h1_zero : c₁.val = 0
  · have hc1 : c₁ = 0 := by ext; exact h1_zero
    subst hc1
    simp only [Credence.zero_conj, collapse_zero, ThreeVal.conj_zero]
  · by_cases h2_zero : c₂.val = 0
    · have hc2 : c₂ = 0 := by ext; exact h2_zero
      subst hc2
      simp only [Credence.conj_zero, collapse_zero, ThreeVal.zero_conj]
    · by_cases h1_one : c₁.val = 1
      · have hc1 : c₁ = 1 := by ext; exact h1_one
        subst hc1
        simp only [Credence.one_conj, collapse_one, ThreeVal.conj_one]
      · by_cases h2_one : c₂.val = 1
        · have hc2 : c₂ = 1 := by ext; exact h2_one
          subst hc2
          simp only [Credence.conj_one, collapse_one, ThreeVal.one_conj]
        · have hcoll1 : collapse c₁ = ThreeVal.half := collapse_interior c₁ h1_zero h1_one
          have hcoll2 : collapse c₂ = ThreeVal.half := collapse_interior c₂ h2_zero h2_one
          have hprod_pos : 0 < c₁.val * c₂.val := by
            apply mul_pos
            · exact lt_of_le_of_ne c₁.nonneg (Ne.symm h1_zero)
            · exact lt_of_le_of_ne c₂.nonneg (Ne.symm h2_zero)
          have hprod_lt_one : c₁.val * c₂.val < 1 := by
            have h1_lt : c₁.val < 1 := lt_of_le_of_ne c₁.le_one h1_one
            have h2_lt : c₂.val < 1 := lt_of_le_of_ne c₂.le_one h2_one
            calc c₁.val * c₂.val < c₁.val * 1 := by
                   apply mul_lt_mul_of_pos_left h2_lt
                   exact lt_of_le_of_ne c₁.nonneg (Ne.symm h1_zero)
              _ = c₁.val := mul_one _
              _ < 1 := h1_lt
          have hconj_ne_zero : (c₁ ⊗ c₂).val ≠ 0 := ne_of_gt hprod_pos
          have hconj_ne_one : (c₁ ⊗ c₂).val ≠ 1 := ne_of_lt hprod_lt_one
          have hcoll_conj : collapse (c₁ ⊗ c₂) = ThreeVal.half :=
            collapse_interior (c₁ ⊗ c₂) hconj_ne_zero hconj_ne_one
          simp only [hcoll1, hcoll2, hcoll_conj, ThreeVal.conj_half_half]

/-! ### Disjunction Homomorphism -/

/-- Collapse respects disjunction: collapse(c1 ⊔ c2) = ThreeVal.disj(collapse c1)(collapse c2) -/
theorem collapse_disj (c₁ c₂ : Credence) :
    collapse (c₁ ⊔ c₂) = ThreeVal.disj (collapse c₁) (collapse c₂) := by
  by_cases h1_one : c₁.val = 1
  · have hc1 : c₁ = 1 := by ext; exact h1_one
    subst hc1
    simp only [Credence.one_disj, collapse_one, ThreeVal.disj_one]
  · by_cases h2_one : c₂.val = 1
    · have hc2 : c₂ = 1 := by ext; exact h2_one
      subst hc2
      simp only [Credence.disj_one, collapse_one, ThreeVal.one_disj]
    · by_cases h1_zero : c₁.val = 0
      · have hc1 : c₁ = 0 := by ext; exact h1_zero
        subst hc1
        simp only [Credence.zero_disj, collapse_zero, ThreeVal.disj_zero]
      · by_cases h2_zero : c₂.val = 0
        · have hc2 : c₂ = 0 := by ext; exact h2_zero
          subst hc2
          simp only [Credence.disj_zero, collapse_zero, ThreeVal.zero_disj]
        · have hcoll1 : collapse c₁ = ThreeVal.half := collapse_interior c₁ h1_zero h1_one
          have hcoll2 : collapse c₂ = ThreeVal.half := collapse_interior c₂ h2_zero h2_one
          have h1_pos : 0 < c₁.val := lt_of_le_of_ne c₁.nonneg (Ne.symm h1_zero)
          have h2_pos : 0 < c₂.val := lt_of_le_of_ne c₂.nonneg (Ne.symm h2_zero)
          have h1_lt : c₁.val < 1 := lt_of_le_of_ne c₁.le_one h1_one
          have h2_lt : c₂.val < 1 := lt_of_le_of_ne c₂.le_one h2_one
          have hdisj_pos : 0 < (c₁ ⊔ c₂).val := by
            simp only [Credence.disj_val]
            have hprod_lt : c₁.val * c₂.val < c₁.val + c₂.val := by
              have hp1 : c₁.val * c₂.val < c₁.val := by
                calc c₁.val * c₂.val < c₁.val * 1 := mul_lt_mul_of_pos_left h2_lt h1_pos
                  _ = c₁.val := mul_one _
              linarith
            linarith
          have hdisj_lt_one : (c₁ ⊔ c₂).val < 1 := by
            simp only [Credence.disj_val]
            have hprod_pos : 0 < c₁.val * c₂.val := mul_pos h1_pos h2_pos
            nlinarith
          have hdisj_ne_zero : (c₁ ⊔ c₂).val ≠ 0 := ne_of_gt hdisj_pos
          have hdisj_ne_one : (c₁ ⊔ c₂).val ≠ 1 := ne_of_lt hdisj_lt_one
          have hcoll_disj : collapse (c₁ ⊔ c₂) = ThreeVal.half :=
            collapse_interior (c₁ ⊔ c₂) hdisj_ne_zero hdisj_ne_one
          simp only [hcoll1, hcoll2, hcoll_disj, ThreeVal.disj_half_half]

end Cred
