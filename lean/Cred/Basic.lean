/-
  Cred: A Foundation for Graded Mathematics

  This formalizes the credence algebra and its core properties.
  Credences are values in [0,1] with:
  - Conjunction (multiplication)
  - Negation (complement)
  - Conditioning (primitive, via chain rule)
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

/-! ## Conditioning (Primitive) -/

/--
Conditioning is a primitive operation satisfying the chain rule.
We represent it as a structure containing a credence value and
the chain rule constraint.
-/
structure Conditioning (A B : Credence) where
  /-- The conditional credence cred(A | B) -/
  condCred : Credence
  /-- Chain rule: cred(A | B) * cred(B) = cred(A ∧ B) -/
  chainRule : condCred ⊗ B = A ⊗ B

/-- When B = 0, conditioning is unconstrained (no ex falso!) -/
theorem conditioning_zero_unconstrained (A : Credence) (c : Credence) :
    c ⊗ (0 : Credence) = A ⊗ 0 := by simp

/-- When B = 1, cred(A | B) = cred(A) -/
theorem conditioning_one (A : Credence) :
    ∃ cond : Conditioning A 1, cond.condCred = A := by
  use ⟨A, by simp⟩

/-! ## Fixed Points -/

/-- The fixed point credence for self-referential negation: L = ~L implies L = 0.5 -/
def half : Credence where
  val := 0.5
  nonneg := by norm_num
  le_one := by norm_num

@[simp] theorem half_val : half.val = 0.5 := rfl

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

/-- 0 is identity for disjunction -/
@[simp] theorem disj_zero (c : Credence) : c ⊔ 0 = c := by
  ext
  simp only [disj_val, zero_val, mul_zero, add_zero, sub_zero]

/-- 1 is absorbing for disjunction -/
@[simp] theorem disj_one (c : Credence) : c ⊔ 1 = 1 := by
  ext
  simp only [disj_val, one_val, mul_one]
  linarith [c.le_one]

/-- De Morgan: ~(A ⊗ B) = ~A ⊔ ~B -/
theorem de_morgan_conj (c₁ c₂ : Credence) : ~(c₁ ⊗ c₂) = ~c₁ ⊔ ~c₂ := by
  ext
  simp only [neg_val, conj_val, disj_val]
  ring

/-- De Morgan: ~(A ⊔ B) = ~A ⊗ ~B -/
theorem de_morgan_disj (c₁ c₂ : Credence) : ~(c₁ ⊔ c₂) = ~c₁ ⊗ ~c₂ := by
  simp only [disj]
  exact neg_neg _

/-! ## Contradiction -/

/-- A contradiction is A ⊗ ~A -/
def contradiction (c : Credence) : Credence := c ⊗ ~c

theorem contradiction_val (c : Credence) : (contradiction c).val = c.val * (1 - c.val) := by
  simp only [contradiction, conj_val, neg_val]

/-- Maximum contradiction at c = 0.5 gives 0.25, not 0 -/
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

/-! ## Tautology -/

/-- A tautology is A ⊔ ~A -/
def tautology (c : Credence) : Credence := c ⊔ ~c

theorem tautology_val (c : Credence) : (tautology c).val = 1 - c.val * (1 - c.val) := by
  simp only [tautology, disj_val, neg_val]
  ring

/-- Under independence assumption, tautology equals 1 only at extremes -/
theorem tautology_zero : tautology (0 : Credence) = 1 := by
  ext
  simp only [tautology_val, zero_val, one_val]
  norm_num

theorem tautology_one : tautology (1 : Credence) = 1 := by
  ext
  simp only [tautology_val, one_val, sub_self, mul_zero, sub_zero]

/-- Minimum tautology at half gives 0.75 -/
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

end Credence

end Cred
