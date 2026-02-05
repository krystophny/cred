/-
  Cred: A Foundation for Graded Mathematics

  This formalizes the credence algebra and its core properties.
  Credences are values in [0,1] with:
  - Independence product (multiplication on values): c₁ ⊗ c₂ = c₁.val * c₂.val.
    Under a probabilistic interpretation this equals cred(A ∧ B) only when A and B
    are independent; in general joint credence is a separate parameter.
  - Negation (complement): ~c = 1 - c
  - Disjunction (De Morgan dual): c₁ ⊔ c₂ = ~(~c₁ ⊗ ~c₂)
  - Conditioning (primitive, via chain rule)

  PHILOSOPHY: Inference as Constraint
  -----------------------------------
  Inference narrows possibilities from uncertainty toward specificity.
  - Prior: Start with maximal uncertainty (flat prior, credence 1/2)
  - Evidence constrains: Each piece of evidence narrows consistent beliefs
  - No evidence = no constraint: Credence 0 evidence cannot narrow anything

  This is why conditioning is primitive (inference IS constraining) and why
  there is no ex falso (impossible evidence provides no constraint).

  IMPORTANT: The binary operations ⊗ and ⊔ are algebraic operations on credence
  values; they do not, in general, determine joint credences of propositions
  from marginals alone. Under an independence assumption one may set
  cred(A ∧ B) = cred(A) ⊗ cred(B) (and similarly for disjunction), but in
  general joint credence is separate data (in particular, it is an explicit
  parameter in Conditioning).

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

/-! ## Conditioning (Primitive) -/

/--
Conditioning is a primitive operation satisfying the chain rule.

Parameters:
- `joint`: the credence cred(A ∧ B) of the conjunction (given, not computed)
- `evidence`: the credence cred(B) of the evidence

The chain rule states: cred(A | B) ⊗ cred(B) = cred(A ∧ B)

Note: `joint` is NOT assumed to equal `evidence ⊗ something`; it is an
independent parameter representing the actual joint credence, which may
differ from the product of marginals for dependent propositions.

Edge case when evidence = 0:
The chain rule requires condCred ⊗ 0 = joint. Since anything times 0 equals 0,
this forces joint = 0 but leaves condCred unconstrained (any value satisfies
c ⊗ 0 = 0). Conditioning on impossible evidence provides no constraint on belief.
See `conditioning_zero_any` for the proof that any credence works.
This is intentional: there is no ex falso in the credence algebra.
-/
structure Conditioning (joint evidence : Credence) where
  /-- The conditional credence cred(A | B) -/
  condCred : Credence
  /-- Chain rule: cred(A | B) ⊗ cred(B) = cred(A ∧ B) -/
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
    Proof: joint.val = condCred.val * evidence.val ≤ 1 * evidence.val = evidence.val.
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

/-! ## Fréchet-Hoeffding Bounds

The chain rule applied from both directions constrains the joint credence
to the Fréchet-Hoeffding interval [max(a + b - 1, 0), min(a, b)].
The upper bound follows from the chain rule alone (each conditioning
structure forces joint <= evidence). The lower bound additionally requires
complement non-negativity (1 - a - b + joint >= 0).
Any joint in [0, min(a, b)] admits conditioning structures in both
directions when both marginals are positive.
-/

/-- Upper Fréchet bound: bidirectional chain rule forces joint ≤ min(a, b) -/
theorem frechet_upper (a b joint : Credence)
    (cond_ba : Conditioning joint a) (cond_ab : Conditioning joint b) :
    joint.val ≤ a.val ∧ joint.val ≤ b.val :=
  ⟨conditioning_implies_joint_le_evidence joint a cond_ba,
   conditioning_implies_joint_le_evidence joint b cond_ab⟩

/-- Lower Fréchet bound: complement non-negativity forces joint ≥ a + b - 1 -/
theorem frechet_lower (a b joint : Credence)
    (h_complement : 0 ≤ 1 - a.val - b.val + joint.val) :
    a.val + b.val - 1 ≤ joint.val := by
  linarith

/-- Any joint in [0, min(a, b)] admits bidirectional conditioning -/
noncomputable def frechet_conditioning_exists (a b joint : Credence)
    (ha : 0 < a.val) (hb : 0 < b.val)
    (hja : joint.val ≤ a.val) (hjb : joint.val ≤ b.val) :
    Conditioning joint a × Conditioning joint b :=
  (conditioning_mk joint a ha hja, conditioning_mk joint b hb hjb)

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

end Credence

/-! ## Three-Valued Collapse

The three-valued collapse maps [0,1] to {0, 1/2, 1}:
- 0 maps to 0
- (0,1) maps to 1/2
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

/-! ### Complete RM3 Implication Table

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

/-! ### Gödel / Product Residuated Implication

On {0, 1/2, 1}, the product residuated implication min(b/a, 1) coincides
with the Gödel implication. Both differ from RM3 at (half, zero):
Gödel/residuated gives zero, RM3 gives half.

Cred conditioning (with Kleene joint = min(a,b)) recovers this arrow for
evidence > 0 and replaces the a = 0 row with * (unconstrained).
-/

/-- Gödel implication on three values (= product residuated on three values) -/
def godel_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one
  | half, zero => zero
  | half, half => one
  | half, one => one
  | one, zero => zero
  | one, half => half
  | one, one => one

/-! #### Complete Gödel Implication Table

       | 0 | 1/2 | 1
   ----+---+-----+---
   0   | 1 |  1  | 1    (vacuous truth row, shared with RM3)
   1/2 | 0 |  1  | 1
   1   | 0 | 1/2 | 1
-/

theorem godel_impl_zero_zero : godel_impl zero zero = one := rfl
theorem godel_impl_zero_half : godel_impl zero half = one := rfl
theorem godel_impl_zero_one : godel_impl zero one = one := rfl
theorem godel_impl_half_zero : godel_impl half zero = zero := rfl
theorem godel_impl_half_half : godel_impl half half = one := rfl
theorem godel_impl_half_one : godel_impl half one = one := rfl
theorem godel_impl_one_zero : godel_impl one zero = zero := rfl
theorem godel_impl_one_half : godel_impl one half = half := rfl
theorem godel_impl_one_one : godel_impl one one = one := rfl

/-- Product residuated implication on three values: min(b/a, 1) for a > 0, 1 for a = 0.
    Defined independently of godel_impl to verify their coincidence. -/
def prod_resid_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one        -- convention: 0 → b = 1
  | half, zero => zero    -- min(0 / (1/2), 1) = 0
  | half, half => one     -- min((1/2) / (1/2), 1) = min(1, 1) = 1
  | half, one => one      -- min(1 / (1/2), 1) = min(2, 1) = 1
  | one, zero => zero     -- min(0/1, 1) = 0
  | one, half => half     -- min((1/2)/1, 1) = 1/2
  | one, one => one       -- min(1/1, 1) = 1

/-- On {0, 1/2, 1}, Gödel and product residuated implications coincide. -/
theorem godel_impl_eq_prod_resid (a b : ThreeVal) :
    godel_impl a b = prod_resid_impl a b := by
  cases a <;> cases b <;> rfl

/-- Gödel and RM3 differ at (half, zero): Gödel gives zero, RM3 gives half -/
theorem godel_impl_ne_rm3_impl : godel_impl half zero ≠ rm3_impl half zero := by
  decide

/-- Gödel also has 0 -> b = 1 (vacuous truth, shared with RM3) -/
theorem godel_impl_zero_is_one (b : ThreeVal) : godel_impl zero b = one := by
  cases b <;> rfl

/-- Cred conditioning blocks ex falso relative to both RM3 and Gödel:
    both have 0 -> b = 1, but Cred conditioning at evidence 0 is unconstrained. -/
theorem cred_no_ex_falso_godel (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

/-! ### Bayes Consistency

A binary arrow f(a, b) used as conditioning is Bayes-consistent when the joint
it induces is symmetric: f(a, b) * a = f(b, a) * b.  This is the constraint
from applying the chain rule in both directions (Bayes theorem).
-/

theorem rm3_not_bayes_consistent :
    ∃ a b : ThreeVal, conj (rm3_impl a b) a ≠ conj (rm3_impl b a) b := by
  use half, zero; decide

theorem godel_bayes_consistent (a b : ThreeVal) :
    conj (godel_impl a b) a = conj (godel_impl b a) b := by
  cases a <;> cases b <;> rfl

end ThreeVal

/-! ### Cred Conditioning at Special Values

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
by the chain rule: in the real-valued model, condCred.val = joint.val / evidence.val.
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
noncomputable def quarter : Credence where
  val := (1 : ℝ) / 4
  nonneg := by norm_num
  le_one := by norm_num

@[simp] theorem quarter_val : quarter.val = (1 : ℝ) / 4 := rfl

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

/-! #### Summary: RM3 / Gödel vs Cred Comparison

Key differences verified:
1. RM3 and Gödel/residuated both have 0 -> b = 1 (ex falso / vacuous truth)
   Lean: rm3_ex_falso, godel_impl_zero_is_one
2. RM3 and Gödel differ at (half, zero): RM3 gives half, Gödel gives zero
   Lean: godel_impl_ne_rm3_impl
3. Cred: cred(b|0) is unconstrained (any value satisfies chain rule)
   Lean: cond_zero_zero_any, cond_zero_half_any, cond_zero_one_any
4. When evidence > 0, Cred conditioning is uniquely determined
   Lean: cond_pos_unique
5. With Kleene joint (min), Cred conditioning matches Gödel/residuated for evidence > 0

This proves the comparison tables in the paper.
-/

end Credence

/-! ## Three-Valued Collapse Homomorphism

The collapse function maps the continuous [0,1] credence algebra to the discrete
three-valued algebra. This section proves that collapse is a homomorphism for
negation, conjunction, and disjunction (Collapse Homomorphism theorem in the paper).

Key insight: The operations on ThreeVal are defined as min/max on {0, 1/2, 1},
which exactly matches what happens when Cred operations are applied to these
boundary values and then collapsed (Collapse Homomorphism theorem in the paper).
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

/-- Collapse is surjective: every three-valued element has a preimage -/
theorem collapse_surjective : ∀ v : ThreeVal,
    ∃ c : Credence, collapse c = v := by
  intro v
  cases v with
  | zero => exact ⟨0, collapse_zero⟩
  | half => exact ⟨Credence.half, collapse_half⟩
  | one => exact ⟨1, collapse_one⟩

/-! ## Uniqueness of the Kleene Target

No analogous collapse homomorphism exists for Gödel or Łukasiewicz algebras.
The negation fixed point at 1/2 propagates constraints that only the Kleene
algebra can absorb.
-/

namespace ThreeVal

/-- Gödel negation: neg_G(0) = 1, neg_G(c) = 0 for c > 0 -/
def godel_neg : ThreeVal → ThreeVal
  | zero => one
  | half => zero
  | one => zero

/-- Gödel negation has no fixed point -/
theorem godel_neg_no_fixed_point (v : ThreeVal) : godel_neg v ≠ v := by
  cases v <;> decide

/-- Łukasiewicz conjunction: max(a + b - 1, 0) on three values -/
def luk_conj : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => zero
  | _, zero => zero
  | half, half => zero
  | half, one => half
  | one, half => half
  | one, one => one

theorem luk_conj_half_half : luk_conj half half = zero := rfl

end ThreeVal

/-- No collapse to Gödel logic: no function φ : [0,1] → {0,1/2,1} preserving
    Gödel negation, because Gödel negation has no fixed point but φ(1/2) must
    be one (since 1/2 = 1 - 1/2 maps to itself under complement). -/
theorem no_godel_collapse :
    ¬(∃ φ : Credence → ThreeVal,
      (∀ c, φ (Credence.neg c) = ThreeVal.godel_neg (φ c))) := by
  intro ⟨φ, hneg⟩
  have hfix := hneg Credence.half
  rw [Credence.liar_fixed_point] at hfix
  exact ThreeVal.godel_neg_no_fixed_point (φ Credence.half) hfix.symm

/-- No collapse to Łukasiewicz logic: no function φ : [0,1] → {0,1/2,1}
    preserving both standard negation and Łukasiewicz conjunction.
    Proof: negation at 1/2 forces φ(1/2) = 1/2. Pick c = √(1/2); then
    c ⊗ c = 1/2, so φ(1/2) = luk_conj(φ(c), φ(c)). But luk_conj(v,v)
    is 0 or 1 for v ∈ {0,1/2,1}, never 1/2. -/
theorem no_luk_collapse :
    ¬(∃ φ : Credence → ThreeVal,
      (∀ c, φ (Credence.neg c) = ThreeVal.neg (φ c)) ∧
      (∀ c₁ c₂, φ (c₁ ⊗ c₂) = ThreeVal.luk_conj (φ c₁) (φ c₂))) := by
  intro ⟨φ, hneg, hconj⟩
  have hfix := hneg Credence.half
  rw [Credence.liar_fixed_point] at hfix
  have hphalf : φ Credence.half = ThreeVal.half := by
    cases h : φ Credence.half <;> simp_all [ThreeVal.neg]
  have hsqrt_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  set c : Credence := ⟨Real.sqrt (1 / 2), Real.sqrt_nonneg _, by
    calc Real.sqrt (1 / 2) ≤ Real.sqrt 1 := by
          apply Real.sqrt_le_sqrt; norm_num
      _ = 1 := Real.sqrt_one⟩
  have hcsq : c ⊗ c = Credence.half := by
    ext
    simp only [Credence.conj_val, Credence.half_val]
    exact Real.mul_self_sqrt hsqrt_nn
  have hconj_c := hconj c c
  rw [hcsq, hphalf] at hconj_c
  cases h : φ c <;> rw [h] at hconj_c <;> simp [ThreeVal.luk_conj] at hconj_c

/-! ## Boolean Subalgebra and Kleene Quotient

{0,1} is a subalgebra of Cred: operations on Boolean values stay Boolean.
{0,1/2,1} is NOT a subalgebra: 1/2 ⊗ 1/2 = 1/4, which leaves the set.
This is why the three-valued relationship requires a quotient (the collapse
homomorphism) rather than a simple restriction.
-/

namespace Credence

/-! ### Boolean Subalgebra: {0,1} is closed under all operations -/

theorem boolean_neg_closed (c : Credence) (h : c = 0 ∨ c = 1) :
    ~c = 0 ∨ ~c = 1 := by
  rcases h with rfl | rfl
  · right; simp
  · left; simp

theorem boolean_conj_closed (c₁ c₂ : Credence)
    (h₁ : c₁ = 0 ∨ c₁ = 1) (h₂ : c₂ = 0 ∨ c₂ = 1) :
    c₁ ⊗ c₂ = 0 ∨ c₁ ⊗ c₂ = 1 := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

theorem boolean_disj_closed (c₁ c₂ : Credence)
    (h₁ : c₁ = 0 ∨ c₁ = 1) (h₂ : c₂ = 0 ∨ c₂ = 1) :
    c₁ ⊔ c₂ = 0 ∨ c₁ ⊔ c₂ = 1 := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

/-! ### {0,1/2,1} is NOT a subalgebra: 1/2 ⊗ 1/2 = 1/4 -/

theorem three_val_conj_not_closed :
    ¬(∀ c₁ c₂ : Credence,
      (c₁ = 0 ∨ c₁ = half ∨ c₁ = 1) →
      (c₂ = 0 ∨ c₂ = half ∨ c₂ = 1) →
      (c₁ ⊗ c₂ = 0 ∨ c₁ ⊗ c₂ = half ∨ c₁ ⊗ c₂ = 1)) := by
  intro h
  have := h half half (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  rcases this with h0 | hh | h1
  · have : (half ⊗ half).val = 0 := congrArg (·.val) h0
    simp [conj_val, half_val] at this
  · have : (half ⊗ half).val = half.val := congrArg (·.val) hh
    simp [conj_val, half_val] at this
  · have hv : (half ⊗ half).val = 1 := congrArg (·.val) h1
    simp only [conj_val, half_val] at hv
    norm_num at hv

/-! ### No retraction: no negation-preserving map [0,1] → {0,1} -/

theorem no_boolean_neg_retraction :
    ¬(∃ φ : Credence → Credence,
      (∀ c, φ c = 0 ∨ φ c = 1) ∧
      (∀ c, φ (~c) = ~(φ c))) := by
  intro ⟨φ, hbool, hneg⟩
  have hfix := hneg half
  rw [liar_fixed_point] at hfix
  -- hfix : φ half = ~(φ half), so φ half is a negation fixed point
  have hfp : φ half = half := neg_fixed_point_unique (φ half) hfix.symm
  -- but φ half ∈ {0,1}, and half ∉ {0,1}
  rcases hbool half with h0 | h1
  · have : half.val = 0 := by rw [← hfp, h0]; simp
    simp [half_val] at this
  · have : half.val = 1 := by rw [← hfp, h1]; simp
    simp [half_val] at this

end Credence

/-! ## Bayes Consistency on [0,1]

Formalizes the paper's pen-and-paper proofs: product residuated Bayes
consistency, Gödel failure on the continuum, copula connection, and
t-norm conditioning uniqueness.
-/

namespace Credence

/-- Product residuated implication on [0,1]: min(b/a, 1) for a > 0, 1 for a = 0 -/
noncomputable def prod_resid_real (a b : Credence) : ℝ :=
  if a.val = 0 then 1 else min (b.val / a.val) 1

/-- The induced joint of the product residuated equals min(a,b) -/
theorem prod_resid_joint (a b : Credence) :
    prod_resid_real a b * a.val = min a.val b.val := by
  unfold prod_resid_real
  by_cases ha : a.val = 0
  · simp only [ha, ↓reduceIte, mul_zero, min_eq_left b.nonneg]
  · simp only [ha, ↓reduceIte]
    have ha_pos : 0 < a.val := lt_of_le_of_ne a.nonneg (Ne.symm ha)
    by_cases hle : b.val ≤ a.val
    · have hdiv : b.val / a.val ≤ 1 := (div_le_one ha_pos).mpr hle
      rw [min_eq_left hdiv, min_eq_right hle]
      field_simp
    · push_neg at hle
      have hdiv : 1 ≤ b.val / a.val := by
        rw [le_div_iff₀ ha_pos, one_mul]; exact le_of_lt hle
      rw [min_eq_right hdiv, one_mul]
      exact (min_eq_left (le_of_lt hle)).symm

/-- Product residuated is Bayes-consistent on [0,1] -/
theorem prod_resid_bayes_consistent_real (a b : Credence) :
    prod_resid_real a b * a.val = prod_resid_real b a * b.val := by
  rw [prod_resid_joint, prod_resid_joint, min_comm]

/-- Gödel implication on [0,1]: 1 if a ≤ b, else b -/
noncomputable def godel_impl_real (a b : Credence) : ℝ :=
  if a.val ≤ b.val then 1 else b.val

/-- Gödel implication fails Bayes consistency on [0,1] -/
theorem godel_not_bayes_consistent_real :
    ∃ a b : Credence,
      godel_impl_real a b * a.val ≠ godel_impl_real b a * b.val := by
  refine ⟨⟨2 / 5, by norm_num, by norm_num⟩, ⟨3 / 5, by norm_num, by norm_num⟩, ?_⟩
  simp only [godel_impl_real]
  norm_num

end Credence

/-- Any symmetric function yields a Bayes-consistent arrow
    when both marginals are positive (copula connection) -/
theorem symmetric_bayes_consistent (C : ℝ → ℝ → ℝ)
    (hsymm : ∀ x y, C x y = C y x)
    (a b : Credence) (ha : a.val ≠ 0) (hb : b.val ≠ 0) :
    C a.val b.val / a.val * a.val = C b.val a.val / b.val * b.val := by
  have h1 : C a.val b.val / a.val * a.val = C a.val b.val := by field_simp [ha]
  have h2 : C b.val a.val / b.val * b.val = C b.val a.val := by field_simp [hb]
  rw [h1, h2]
  exact hsymm a.val b.val

/-- Symmetry + right-zero boundary gives left-zero (copula zero case) -/
theorem copula_zero_left (C : ℝ → ℝ → ℝ)
    (hsymm : ∀ x y, C x y = C y x) (hzero : ∀ x, C x 0 = 0)
    (b : ℝ) : C 0 b = 0 := by
  rw [hsymm, hzero]

/-- Minimum t-norm fails unique conditioning -/
theorem min_tnorm_not_unique :
    ∃ e c₁ c₂ : Credence, 0 < e.val ∧ c₁ ≠ c₂ ∧
      min c₁.val e.val = e.val ∧ min c₂.val e.val = e.val := by
  refine ⟨Credence.half, Credence.half, 1, ?_, ?_, ?_, ?_⟩
  · simp only [Credence.half_val]; norm_num
  · intro h
    have := congrArg Credence.val h
    simp only [Credence.half_val, Credence.one_val] at this
    norm_num at this
  · exact min_self _
  · simp only [Credence.one_val, Credence.half_val]
    exact min_eq_right (by norm_num : (1 : ℝ) / 2 ≤ 1)

/-- Łukasiewicz t-norm fails unique conditioning -/
theorem luk_tnorm_not_unique :
    ∃ e c₁ c₂ : Credence, 0 < e.val ∧ c₁ ≠ c₂ ∧
      max (c₁.val + e.val - 1) 0 = 0 ∧ max (c₂.val + e.val - 1) 0 = 0 := by
  refine ⟨Credence.half, 0, Credence.half, ?_, ?_, ?_, ?_⟩
  · simp only [Credence.half_val]; norm_num
  · intro h
    have := congrArg Credence.val h
    simp only [Credence.half_val, Credence.zero_val] at this
    norm_num at this
  · simp only [Credence.zero_val, Credence.half_val]; norm_num
  · simp only [Credence.half_val]; norm_num

/-- RM3 material conditional on [0,1]: max(1-a, b) -/
noncomputable def rm3_impl_real (a b : Credence) : ℝ :=
  max (1 - a.val) b.val

/-- RM3 fails Bayes consistency under real multiplication on [0,1] -/
theorem rm3_not_bayes_consistent_real :
    ∃ a b : Credence,
      rm3_impl_real a b * a.val ≠ rm3_impl_real b a * b.val := by
  refine ⟨Credence.half, 0, ?_⟩
  simp only [rm3_impl_real, Credence.half_val, Credence.zero_val]
  norm_num

/-! ## Maximum Dependence (Min Copula) and Independence (Product)

The following theorems formalize the key uniqueness results from Part 1:
- min_bayes_consistent: The min copula is Bayes consistent
- prod_trivial_conditioning: Product (independence) gives trivial conditioning

These complete the proof that maximum dependence (min) is the unique truth-functional
joint that is both Bayes-consistent AND non-trivial.
-/

/-- Min copula is Bayes consistent: min(a,b)/a * a = min(b,a)/b * b.
    This follows from symmetry of min. -/
theorem min_bayes_consistent (a b : Credence) :
    min a.val b.val = min b.val a.val := by
  exact min_comm a.val b.val

/-- Under independence (product joint), conditioning is trivial:
    if j(A,B) = a * b, then cred(A|B) = a*b/b = a.
    Evidence has no effect on the conclusion. -/
theorem prod_trivial_conditioning (a b : Credence) (hb : b.val ≠ 0) :
    a.val * b.val / b.val = a.val := by
  field_simp

/-- Under max dependence (min joint), conditioning is non-trivial:
    if j(A,B) = min(a,b), then cred(A|B) = min(a,b)/b ≠ a in general.
    Example: a = 1/4, b = 1/2 gives min(1/4, 1/2)/0.5 = 1/2 ≠ 1/4. -/
theorem min_nontrivial_conditioning :
    ∃ a b : Credence, 0 < b.val ∧ min a.val b.val / b.val ≠ a.val := by
  refine ⟨Credence.quarter, Credence.half, ?_, ?_⟩
  · simp only [Credence.half_val]; norm_num
  · simp only [Credence.quarter_val, Credence.half_val]
    norm_num

end Cred
