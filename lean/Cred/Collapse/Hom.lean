/-
  Cred Collapse: The Collapse Homomorphism

  PAPER CROSS-REFERENCES (part1/paper.tex):
  -----------------------------------------
  thm:collapse         → collapse_neg, collapse_conj, collapse_disj, collapse_surjective
  prop:no-classical    → no_boolean_neg_retraction
  prop:no-godel        → no_godel_collapse, godel_neg_no_fixed_point
  prop:no-luk          → no_luk_collapse, luk_conj_half_half
-/

import Cred.Collapse.ThreeVal

namespace Cred

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

end Cred
