/-
  Cred Bridge: Curry Block

  Curry needs a total internal conditional with modus ponens, conditional proof,
  and contraction. Cred keeps conditioning external. This module proves the
  algebraic reason: product conjunction on [0,1] has a residuated arrow, but
  the arrow restores the ex-falso row and violates contraction.
-/

import Cred.Cond.Copula

namespace Cred

namespace Credence

/-! ## Product Residuum as a Credence -/

/-- Product residuated implication as a credence value. -/
noncomputable def prodResid (a b : Credence) : Credence where
  val := prod_resid_real a b
  nonneg := by
    unfold prod_resid_real
    by_cases ha : a.val = 0
    · simp [ha]
    · simp [ha]
      exact div_nonneg b.nonneg (le_of_lt (lt_of_le_of_ne a.nonneg (Ne.symm ha)))
  le_one := by
    unfold prod_resid_real
    by_cases ha : a.val = 0
    · simp [ha]
    · simp [ha]

@[simp] theorem prodResid_val (a b : Credence) :
    (prodResid a b).val = prod_resid_real a b := rfl

@[simp] theorem prodResid_zero_left (b : Credence) :
    prodResid 0 b = 1 := by
  ext
  simp [prodResid, prod_resid_real]

theorem prodResid_pos_val (a b : Credence) (ha : 0 < a.val) :
    (prodResid a b).val = min (b.val / a.val) 1 := by
  simp [prodResid, prod_resid_real, ne_of_gt ha]

theorem prodResid_joint (a b : Credence) :
    (prodResid a b ⊗ a).val = min a.val b.val := by
  simp [prodResid_val, prod_resid_joint]

/-! ## Residuation -/

def MP (f : Credence → Credence → Credence) : Prop :=
  ∀ a b, f a b ⊗ a ≤ b

def CP (f : Credence → Credence → Credence) : Prop :=
  ∀ a b c, c ⊗ a ≤ b → c ≤ f a b

def Contraction (f : Credence → Credence → Credence) : Prop :=
  ∀ a b, f a (f a b) ≤ f a b

def Residuation (f : Credence → Credence → Credence) : Prop :=
  ∀ a b c, c ⊗ a ≤ b ↔ c ≤ f a b

theorem mp_cp_residuation (f : Credence → Credence → Credence)
    (hmp : MP f) (hcp : CP f) : Residuation f := by
  intro a b c
  constructor
  · exact hcp a b c
  · intro hle
    have hmul : (c ⊗ a).val ≤ (f a b ⊗ a).val := by
      simp only [conj_val]
      exact mul_le_mul_of_nonneg_right hle a.nonneg
    exact le_trans hmul (hmp a b)

private theorem min_div_mul_le (a b : Credence) (ha : 0 < a.val) :
    min (b.val / a.val) 1 * a.val ≤ b.val := by
  by_cases hle : b.val ≤ a.val
  · have hdiv : b.val / a.val ≤ 1 := (div_le_one ha).mpr hle
    rw [min_eq_left hdiv]
    field_simp
  · push_neg at hle
    have hdiv : 1 ≤ b.val / a.val := by
      rw [le_div_iff₀ ha, one_mul]
      exact le_of_lt hle
    rw [min_eq_right hdiv, one_mul]
    exact le_of_lt hle

theorem residuation_unique (f : Credence → Credence → Credence)
    (h : Residuation f) :
    ∀ a b, 0 < a.val → (f a b).val = min 1 (b.val / a.val) := by
  intro a b ha
  apply le_antisymm
  · apply le_min
    · exact (f a b).le_one
    · rw [le_div_iff₀ ha]
      exact (h a b (f a b)).mpr (le_refl _)
  · let r : Credence := ⟨min 1 (b.val / a.val), by
        exact le_min zero_le_one (div_nonneg b.nonneg (le_of_lt ha)), min_le_left _ _⟩
    have hr : r ⊗ a ≤ b := by
      change (min 1 (b.val / a.val)) * a.val ≤ b.val
      rw [min_comm]
      exact min_div_mul_le a b ha
    exact (h a b r).mp hr

theorem prodResid_residuation : Residuation prodResid := by
  intro a b c
  constructor
  · intro hle
    by_cases ha0 : a.val = 0
    · simp [prodResid, prod_resid_real, ha0]
      exact c.le_one
    · have ha : 0 < a.val := lt_of_le_of_ne a.nonneg (Ne.symm ha0)
      have hc_le : c.val ≤ b.val / a.val := (le_div_iff₀ ha).mpr hle
      have hc_le_min : c.val ≤ min (b.val / a.val) 1 := le_min hc_le c.le_one
      change c.val ≤ (prodResid a b).val
      simpa [prodResid, prod_resid_real, ha0] using hc_le_min
  · intro hle
    by_cases ha0 : a.val = 0
    · change c.val * a.val ≤ b.val
      rw [ha0, mul_zero]
      exact b.nonneg
    · have ha : 0 < a.val := lt_of_le_of_ne a.nonneg (Ne.symm ha0)
      change c.val * a.val ≤ b.val
      have hprod : c.val * a.val ≤ (prodResid a b).val * a.val :=
        mul_le_mul_of_nonneg_right hle a.nonneg
      rw [prodResid_pos_val a b ha] at hprod
      have hmin := min_div_mul_le a b ha
      exact le_trans hprod hmin

theorem prodResid_unique_positive (f : Credence → Credence → Credence)
    (hmp : MP f) (hcp : CP f) :
    ∀ a b, 0 < a.val → f a b = prodResid a b := by
  intro a b ha
  ext
  rw [residuation_unique f (mp_cp_residuation f hmp hcp) a b ha,
      prodResid_pos_val a b ha, min_comm]

/-! ## Contraction Failure -/

@[simp] theorem prodResid_half_quarter :
    prodResid half quarter = half := by
  ext
  norm_num [prodResid, prod_resid_real, half_val, quarter_val]

@[simp] theorem prodResid_half_half :
    prodResid half half = 1 := by
  ext
  norm_num [prodResid, prod_resid_real, half_val]

theorem prod_resid_no_contraction :
    ∃ a b, ¬ ((prodResid a (prodResid a b)) ≤ prodResid a b) := by
  refine ⟨half, quarter, ?_⟩
  norm_num [Credence.le_def, half_val]

theorem curry_block :
    ¬ ∃ f : Credence → Credence → Credence, MP f ∧ CP f ∧ Contraction f := by
  rintro ⟨f, hmp, hcp, hcontr⟩
  have hf₁ : f half quarter = half := by
    simpa using prodResid_unique_positive f hmp hcp half quarter (by norm_num [half_val])
  have hf₂ : f half half = 1 := by
    simpa using prodResid_unique_positive f hmp hcp half half (by norm_num [half_val])
  have hc := hcontr half quarter
  rw [hf₁, hf₂] at hc
  norm_num [Credence.le_def, half_val] at hc

/-! ## Curry Fixed Points for the Residuum -/

theorem curry_fixed_point_positive (b : Credence) (hb : 0 < b.val) :
    ∃ c : Credence, c = prodResid c b := by
  let c : Credence :=
    ⟨Real.sqrt b.val, Real.sqrt_nonneg b.val,
      by
        calc Real.sqrt b.val ≤ Real.sqrt 1 := Real.sqrt_le_sqrt b.le_one
          _ = 1 := Real.sqrt_one⟩
  refine ⟨c, ?_⟩
  ext
  have hcpos : 0 < c.val := by
    change 0 < Real.sqrt b.val
    exact Real.sqrt_pos.2 hb
  rw [prodResid_pos_val c b hcpos]
  have hsqrtnz : Real.sqrt b.val ≠ 0 := ne_of_gt hcpos
  have hdiv : b.val / Real.sqrt b.val = Real.sqrt b.val := by
    rw [div_eq_iff hsqrtnz]
    nth_rewrite 1 [← Real.sq_sqrt b.nonneg]
    ring
  have hsqrt_le_one : Real.sqrt b.val ≤ 1 := by
    calc Real.sqrt b.val ≤ Real.sqrt 1 := Real.sqrt_le_sqrt b.le_one
      _ = 1 := Real.sqrt_one
  simp only [c]
  rw [hdiv, min_eq_left hsqrt_le_one]

theorem curry_no_fixed_point_zero :
    ¬ ∃ c : Credence, c = prodResid c 0 := by
  rintro ⟨c, hc⟩
  by_cases hcz : c.val = 0
  · have hzero : c = 0 := by
      ext
      exact hcz
    have hprod : prodResid c 0 = 1 := by
      ext
      simp [prodResid, prod_resid_real, hcz]
    have h01 : (0 : Credence) = 1 := by
      rw [← hzero, hc, hprod]
    have hval := congrArg Credence.val h01
    norm_num at hval
  · have hcpos : 0 < c.val := lt_of_le_of_ne c.nonneg (Ne.symm hcz)
    have hval := congrArg Credence.val hc
    rw [prodResid_pos_val c 0 hcpos] at hval
    simp [Credence.zero_val] at hval
    linarith [hcpos]

end Credence

end Cred
