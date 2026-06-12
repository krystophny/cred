/-
  Cred Rational Value Algebra: the value algebra constructed off the reals.

  Issue #549. The product De Morgan operations are closed on the rational unit
  interval, and the rationals are built from the integers and naturals with no
  reals at all. So `RatUnit` is a real-free carrier of the full `CredAlgebra`
  signature (the actual product, negation, and De Morgan dual, not a finite
  collapse), with a homomorphism bridge to the hosted `Credence` instance.

  This is the constructive core of "construct the value algebra internally": the
  algebra of values needs no reals. Completeness for the inf/sup quantifiers is
  the order-completion of this rational algebra, the internal Dedekind cuts, which
  by the conservation principle of `Cred.commitment_conservation` relocates the
  reals into the cut data rather than removing them. That completion is the
  remaining step; the algebra itself is here, real-free.
-/

import Cred.Algebra

namespace Cred

/-- The rational unit interval: a real-free carrier for the value algebra. -/
def RatUnit : Type := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

namespace RatUnit

instance : PartialOrder RatUnit := Subtype.partialOrder _

theorem le_def (a b : RatUnit) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-- Zero, the bottom value. -/
def zero : RatUnit := ⟨0, by norm_num⟩
/-- One, the top value. -/
def one : RatUnit := ⟨1, by norm_num⟩

/-- Negation `1 - q`, closed on the unit interval. -/
def neg (a : RatUnit) : RatUnit :=
  ⟨1 - a.val, by obtain ⟨h0, h1⟩ := a.2; exact ⟨by linarith, by linarith⟩⟩

/-- Product conjunction `q * r`, closed on the unit interval. -/
def conj (a b : RatUnit) : RatUnit :=
  ⟨a.val * b.val, by
    obtain ⟨ha0, ha1⟩ := a.2; obtain ⟨hb0, hb1⟩ := b.2
    refine ⟨mul_nonneg ha0 hb0, ?_⟩
    calc a.val * b.val ≤ 1 * 1 := by
          apply mul_le_mul ha1 hb1 hb0 (by norm_num)
      _ = 1 := by norm_num⟩

/-- Disjunction as the De Morgan dual, so `disj_eq` holds by `rfl`. -/
def disj (a b : RatUnit) : RatUnit := neg (conj (neg a) (neg b))

@[simp] theorem neg_val (a : RatUnit) : (neg a).val = 1 - a.val := rfl
@[simp] theorem conj_val (a b : RatUnit) : (conj a b).val = a.val * b.val := rfl
@[simp] theorem zero_val : (zero).val = 0 := rfl
@[simp] theorem one_val : (one).val = 1 := rfl

/-- The rational unit interval is a real-free `CredAlgebra`. -/
instance : CredAlgebra RatUnit where
  bot := zero
  top := one
  cneg := neg
  cconj := conj
  cdisj := disj
  bot_le a := by rw [le_def]; exact a.2.1
  le_top a := by rw [le_def]; exact a.2.2
  cneg_cneg a := by apply Subtype.ext; simp only [neg_val]; ring
  cneg_le_cneg a b h := by rw [le_def] at h ⊢; simp only [neg_val]; linarith
  cneg_bot := by apply Subtype.ext; simp only [neg_val, zero_val, one_val]; norm_num
  cconj_comm a b := by apply Subtype.ext; simp only [conj_val]; ring
  cconj_assoc a b c := by apply Subtype.ext; simp only [conj_val]; ring
  cconj_top a := by apply Subtype.ext; simp only [conj_val, one_val]; ring
  cconj_bot a := by apply Subtype.ext; simp only [conj_val, zero_val]; ring
  cconj_le_cconj_left a {b c} h := by
    rw [le_def] at h ⊢; simp only [conj_val]
    exact mul_le_mul_of_nonneg_left h a.2.1
  disj_eq _ _ := rfl

/-! ## Bridge to the hosted `Credence` instance -/

/-- The embedding of a rational value into the hosted credence algebra. -/
noncomputable def toCredence (a : RatUnit) : Credence :=
  ⟨(a.val : ℝ), by exact_mod_cast a.2.1, by exact_mod_cast a.2.2⟩

@[simp] theorem toCredence_val (a : RatUnit) : (toCredence a).val = (a.val : ℝ) := rfl

/-- The embedding preserves negation. -/
theorem toCredence_neg (a : RatUnit) :
    toCredence (neg a) = Credence.neg (toCredence a) := by
  apply Credence.ext
  rw [toCredence_val, Credence.neg_val, toCredence_val, neg_val]
  push_cast; ring

/-- The embedding preserves the product conjunction. -/
theorem toCredence_conj (a b : RatUnit) :
    toCredence (conj a b) = Credence.conj (toCredence a) (toCredence b) := by
  apply Credence.ext
  rw [toCredence_val, Credence.conj_val, toCredence_val, toCredence_val, conj_val]
  push_cast; ring

/-- The embedding preserves disjunction, hence is a `CredAlgebra` homomorphism. -/
theorem toCredence_disj (a b : RatUnit) :
    toCredence (disj a b) = Credence.disj (toCredence a) (toCredence b) := by
  rw [disj, Credence.disj]
  rw [toCredence_neg, toCredence_conj, toCredence_neg, toCredence_neg]

end RatUnit

end Cred
