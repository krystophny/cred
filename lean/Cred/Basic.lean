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
The chain rule becomes condCred * 0 = joint, forcing joint = 0.
But condCred itself is unconstrained (any value satisfies c * 0 = 0).
This means conditioning on impossible evidence gives no information.
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

/-- When evidence = 1, cred(A | B) = cred(A ∧ B) -/
theorem conditioning_one (joint : Credence) :
    ∃ cond : Conditioning joint 1, cond.condCred = joint := by
  use ⟨joint, by simp⟩

/-- Existence of conditioning when evidence > 0 and joint ≤ evidence -/
theorem conditioning_exists (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) :
    ∃ _ : Conditioning joint evidence, True := by
  refine ⟨⟨⟨joint.val / evidence.val, ?_, ?_⟩, ?_⟩, trivial⟩
  · exact div_nonneg joint.nonneg (le_of_lt h_pos)
  · rw [div_le_one h_pos]; exact h_le
  · ext; simp only [conj_val]; field_simp

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

/-! ## Contradiction and Tautology (Under Independence)

These operations compute c ⊗ ~c and c ⊔ ~c using the independence formulas.

IMPORTANT: In classical probability, P(A ∧ ~A) = 0 and P(A ∨ ~A) = 1 always,
because A and ~A are mutually exclusive. However, in this graded algebra:

1. We use the INDEPENDENCE formula: c ⊗ ~c = c * (1-c)
2. This gives nonzero "contradiction" (max 0.25 at c=0.5)
3. And non-unity "tautology" (min 0.75 at c=0.5)

This is INTENTIONAL and meaningful for the graded logic:
- It measures the "uncertainty" or "spread" in a credence
- c = 0.5 maximizes uncertainty (highest contradiction, lowest tautology)
- c = 0 or 1 minimizes uncertainty (zero contradiction, full tautology)

For dependent propositions (like A and ~A which are maximally anti-correlated),
use the Conditioning structure with proper joint credences instead.
-/

/-- Pseudo-contradiction under independence: c ⊗ ~c = c * (1-c) -/
def contradiction (c : Credence) : Credence := c ⊗ ~c

theorem contradiction_val (c : Credence) : (contradiction c).val = c.val * (1 - c.val) := by
  simp only [contradiction, conj_val, neg_val]

/-- Maximum contradiction at c = 0.5 gives 0.25 (measures uncertainty) -/
theorem contradiction_half : (contradiction half).val = 0.25 := by
  simp only [contradiction_val, half_val]
  norm_num

/-- Contradiction is always ≤ 0.25 -/
theorem contradiction_le_quarter (c : Credence) :
    (contradiction c).val ≤ 0.25 := by
  simp only [contradiction_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - 0.5)]

/-- Contradiction is 0 only at extremes (certainty) -/
theorem contradiction_eq_zero_iff (c : Credence) :
    contradiction c = 0 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have hv : c.val * (1 - c.val) = 0 := by
      have := congrArg (·.val) h
      simp only [contradiction_val, zero_val] at this
      exact this
    rcases mul_eq_zero.mp hv with hz | h1
    · left; ext; exact hz
    · right; ext; simp only [one_val]; linarith
  · intro h
    rcases h with rfl | rfl
    · ext; simp [contradiction_val]
    · ext; simp [contradiction_val]

/-- Pseudo-tautology under independence: c ⊔ ~c = 1 - c*(1-c) -/
def tautology (c : Credence) : Credence := c ⊔ ~c

theorem tautology_val (c : Credence) : (tautology c).val = 1 - c.val * (1 - c.val) := by
  simp only [tautology, disj_val, neg_val]
  ring

/-- Tautology equals 1 at extremes (certainty) -/
theorem tautology_zero : tautology (0 : Credence) = 1 := by
  ext
  simp only [tautology_val, zero_val, one_val]
  norm_num

theorem tautology_one : tautology (1 : Credence) = 1 := by
  ext
  simp only [tautology_val, one_val, sub_self, mul_zero, sub_zero]

/-- Minimum tautology at half gives 0.75 (maximum uncertainty) -/
theorem tautology_half : (tautology half).val = 0.75 := by
  simp only [tautology_val, half_val]
  norm_num

/-- Tautology is always at least 0.75 -/
theorem tautology_ge_three_quarters (c : Credence) :
    (tautology c).val ≥ 0.75 := by
  simp only [tautology_val]
  have h1 := c.nonneg
  have h2 := c.le_one
  nlinarith [sq_nonneg (c.val - 0.5)]

/-- Tautology equals 1 only at extremes -/
theorem tautology_eq_one_iff (c : Credence) :
    tautology c = 1 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have hv : 1 - c.val * (1 - c.val) = 1 := by
      have := congrArg (·.val) h
      simp only [tautology_val, one_val] at this
      exact this
    have hzero : c.val * (1 - c.val) = 0 := by linarith
    rcases mul_eq_zero.mp hzero with hz | h1
    · left; ext; exact hz
    · right; ext; simp only [one_val]; linarith
  · intro h
    rcases h with rfl | rfl
    · exact tautology_zero
    · exact tautology_one

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

/-- Cred conditioning on 0 is NOT forced to 1 (blocks ex falso) -/
theorem cred_no_ex_falso :
    ∃ c : Credence, ∃ cond : Credence.Conditioning 0 0, cond.condCred = c := by
  use 0
  exact Credence.conditioning_zero_any 0

end ThreeVal

end Cred
