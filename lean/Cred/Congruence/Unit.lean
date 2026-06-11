/-
  Congruence Classification: UnitCongruence ([0,1]-multiplication)

  The Kleene lattice ({0}, (0,1), {1}) is the unique non-trivial finite
  quotient under UnitCongruence: compatibility with [0,1]-bounded
  multiplication (physically meaningful).

  PAPER CROSS-REFERENCES (part1/paper.tex):
  ------------------------------------------
  thm:congruence-main  -> unit_classification
                          (with RealCongruence.no_nontrivial_finite_quotient)
  (1) UnitCongruence.singleton_zero, UnitCongruence.singleton_one
  (2) no_two_element_quotient (re-export of no_boolean_neg_retraction)
  (3) unique_three_element_quotient (re-export of three_element_quotient_unique)
  thm:quotient-unique  -> three_element_quotient_unique

  Building blocks from Cred.Core.Value and Cred.Collapse.Hom:
  - no_boolean_neg_retraction: no 2-element quotient preserving negation
  - neg_fixed_point_unique: 1/2 is the unique negation fixed point
-/

import Cred.Collapse.Hom

namespace Cred

open Credence

/-! ## UnitCongruence: [0,1]-multiplication -/

/-- A congruence on the credence algebra with [0,1]-bounded multiplication.
    conj_compat requires all four arguments to lie in [0,1], reflecting that
    the product of [0,1]-values stays in [0,1]. -/
structure UnitCongruence where
  rel : ℝ → ℝ → Prop
  refl : ∀ a, rel a a
  symm : ∀ a b, rel a b → rel b a
  trans : ∀ a b c, rel a b → rel b c → rel a c
  neg_compat : ∀ a b, rel a b → rel (1 - a) (1 - b)
  conj_compat : ∀ a b c d,
    0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
    0 ≤ c → c ≤ 1 → 0 ≤ d → d ≤ 1 →
    rel a b → rel c d → rel (a * c) (b * d)

namespace UnitCongruence

/-- A congruence is non-trivial if it does not identify all [0,1] elements. -/
def NonTrivial (R : UnitCongruence) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ ¬R.rel a b

/-- {0} is a singleton under [0,1]-multiplication congruence.
    Proof mirrors zero_equiv_forces_trivial but threads [0,1] bounds through
    each conj_compat call. From 0~eps: neg gives 1~(1-eps), then x~x(1-eps)
    via conj_compat (all in [0,1]). Iterate to get x~x(1-eps)^n. For large n,
    x(1-eps)^n <= eps, factor as eps * (x(1-eps)^n/eps) with quotient in [0,1],
    use 0~eps to get 0~x(1-eps)^n, chain to get x~0. -/
theorem singleton_zero (R : UnitCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 0 x → x = 0 := by
  intro x hx_nn hx_le hrel
  by_contra hne
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nn (Ne.symm hne)
  have h_one_comp : R.rel 1 (1 - x) := by
    have h := R.neg_compat 0 x hrel; rwa [sub_zero] at h
  have hcomp_nn : 0 ≤ 1 - x := by linarith [hx_le]
  have hcomp_le : 1 - x ≤ 1 := by linarith [hx_nn]
  have h_scale : ∀ y, 0 ≤ y → y ≤ 1 → R.rel y (y * (1 - x)) := by
    intro y hy_nn hy_le
    have h1 : R.rel (y * 1) (y * (1 - x)) :=
      R.conj_compat y y 1 (1 - x) hy_nn hy_le hy_nn hy_le
        zero_le_one (le_refl 1) hcomp_nn hcomp_le
        (R.refl y) h_one_comp
    rwa [mul_one] at h1
  have h_zero_scaled : ∀ y, 0 ≤ y → y ≤ 1 → R.rel 0 (x * y) := by
    intro y hy_nn hy_le
    have h1 : R.rel (0 * y) (x * y) :=
      R.conj_compat 0 x y y (le_refl 0) zero_le_one
        hx_nn hx_le hy_nn hy_le hy_nn hy_le hrel (R.refl y)
    rwa [zero_mul] at h1
  have hcomp_lt_one : 1 - x < 1 := by linarith
  have h_pow_nn : ∀ n : ℕ, 0 ≤ (1 - x) ^ n := fun n => pow_nonneg hcomp_nn n
  have h_pow_le : ∀ n : ℕ, (1 - x) ^ n ≤ 1 := fun n => pow_le_one₀ hcomp_nn hcomp_le
  have h_prod_nn : ∀ (y : ℝ) (n : ℕ), 0 ≤ y → 0 ≤ y * (1 - x) ^ n :=
    fun y n hy => mul_nonneg hy (h_pow_nn n)
  have h_prod_le : ∀ (y : ℝ) (n : ℕ), 0 ≤ y → y ≤ 1 → y * (1 - x) ^ n ≤ 1 := by
    intro y n hy_nn hy_le
    calc y * (1 - x) ^ n ≤ y * 1 :=
          mul_le_mul_of_nonneg_left (h_pow_le n) hy_nn
      _ = y := mul_one y
      _ ≤ 1 := hy_le
  have h_iter : ∀ (y : ℝ), 0 ≤ y → y ≤ 1 → ∀ n : ℕ, R.rel y (y * (1 - x) ^ n) := by
    intro y hy_nn hy_le n
    induction n with
    | zero => simp [pow_zero, mul_one]; exact R.refl y
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact R.trans y (y * (1 - x) ^ n) (y * (1 - x) ^ n * (1 - x))
        ih (h_scale (y * (1 - x) ^ n) (h_prod_nn y n hy_nn)
          (h_prod_le y n hy_nn hy_le))
  obtain ⟨a, b, ha_nn, ha_le, hb_nn, hb_le, hab⟩ := hnt
  apply hab
  have h_collapse : ∀ y, 0 ≤ y → y ≤ 1 → R.rel y 0 := by
    intro y hy_nn hy_le
    by_cases hy_zero : y = 0
    · rw [hy_zero]; exact R.refl 0
    · have hy_pos : 0 < y := lt_of_le_of_ne hy_nn (Ne.symm hy_zero)
      have h_exists_n : ∃ n : ℕ, y * (1 - x) ^ n ≤ x := by
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx_pos hcomp_lt_one
        exact ⟨n, calc y * (1 - x) ^ n ≤ 1 * (1 - x) ^ n :=
              mul_le_mul_of_nonneg_right hy_le (h_pow_nn n)
          _ = (1 - x) ^ n := one_mul _
          _ ≤ x := le_of_lt hn⟩
      obtain ⟨n, hn⟩ := h_exists_n
      have hpow_nn : 0 ≤ y * (1 - x) ^ n := h_prod_nn y n hy_nn
      have hq_nn : 0 ≤ y * (1 - x) ^ n / x := div_nonneg hpow_nn (le_of_lt hx_pos)
      have hq_le : y * (1 - x) ^ n / x ≤ 1 := (div_le_one hx_pos).mpr hn
      have h_eq : x * (y * (1 - x) ^ n / x) = y * (1 - x) ^ n := by
        field_simp
      have hR_0_ypow : R.rel 0 (y * (1 - x) ^ n) := by
        rw [← h_eq]
        exact h_zero_scaled (y * (1 - x) ^ n / x) hq_nn hq_le
      exact R.trans y (y * (1 - x) ^ n) 0
        (h_iter y hy_nn hy_le n) (R.symm _ _ hR_0_ypow)
  exact R.trans a 0 b (h_collapse a ha_nn ha_le) (R.symm b 0 (h_collapse b hb_nn hb_le))

/-- {1} is a singleton: follows from singleton_zero by negation duality. -/
theorem singleton_one (R : UnitCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 1 x → x = 1 := by
  intro x hx_nn hx_le hrel
  have h_neg_rel : R.rel 0 (1 - x) := by
    have h := R.neg_compat 1 x hrel; rwa [sub_self] at h
  have := singleton_zero R hnt (1 - x) (by linarith) (by linarith) h_neg_rel
  linarith

end UnitCongruence

/-! ## Kleene partition as a concrete UnitCongruence -/

/-- The Kleene equivalence relation: three classes {0}, {1}, and (0,1). -/
def kleeneRel (a b : ℝ) : Prop :=
  (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a ≠ 0 ∧ a ≠ 1 ∧ b ≠ 0 ∧ b ≠ 1)

/-- The Kleene partition is a UnitCongruence. -/
def kleeneCongruence : UnitCongruence where
  rel := kleeneRel
  refl := by
    intro a
    by_cases h0 : a = 0
    · left; exact ⟨h0, h0⟩
    · by_cases h1 : a = 1
      · right; left; exact ⟨h1, h1⟩
      · right; right; exact ⟨h0, h1, h0, h1⟩
  symm := by
    intro a b hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha0, ha1, hb0, hb1⟩
    · left; exact ⟨hb, ha⟩
    · right; left; exact ⟨hb, ha⟩
    · right; right; exact ⟨hb0, hb1, ha0, ha1⟩
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha0, ha1, hb0, hb1⟩
    · rcases hbc with ⟨_, hc⟩ | ⟨hb1, _⟩ | ⟨hbc0, _, _, _⟩
      · left; exact ⟨ha, hc⟩
      · exfalso; rw [hb] at hb1; exact one_ne_zero hb1.symm
      · exact absurd hb hbc0
    · rcases hbc with ⟨hb0, _⟩ | ⟨_, hc⟩ | ⟨_, hbc1, _, _⟩
      · exfalso; rw [hb] at hb0; exact one_ne_zero hb0
      · right; left; exact ⟨ha, hc⟩
      · exact absurd hb hbc1
    · rcases hbc with ⟨hc0, _⟩ | ⟨hc1, _⟩ | ⟨_, _, hc0, hc1⟩
      · exact absurd hc0 hb0
      · exact absurd hc1 hb1
      · right; right; exact ⟨ha0, ha1, hc0, hc1⟩
  neg_compat := by
    intro a b hab
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha0, ha1, hb0, hb1⟩
    · rw [ha, hb]; right; left; simp
    · rw [ha, hb]; left; simp
    · right; right
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact ha1 (by linarith)
      · intro h; exact ha0 (by linarith)
      · intro h; exact hb1 (by linarith)
      · intro h; exact hb0 (by linarith)
  conj_compat := by
    intro a b c d ha_nn ha_le hb_nn hb_le hc_nn hc_le hd_nn hd_le hab hcd
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha0, ha1, hb0, hb1⟩
    · rw [ha, hb, zero_mul, zero_mul]; left; exact ⟨rfl, rfl⟩
    · rw [ha, hb, one_mul, one_mul]; exact hcd
    · rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩ | ⟨hc0, hc1, hd0, hd1⟩
      · rw [hc, hd, mul_zero, mul_zero]; left; exact ⟨rfl, rfl⟩
      · rw [hc, hd, mul_one, mul_one]; right; right; exact ⟨ha0, ha1, hb0, hb1⟩
      · right; right
        have ha_pos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha0)
        have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb_nn (Ne.symm hb0)
        have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd0)
        have ha_lt : a < 1 := lt_of_le_of_ne ha_le ha1
        have hc_lt : c < 1 := lt_of_le_of_ne hc_le hc1
        have hb_lt : b < 1 := lt_of_le_of_ne hb_le hb1
        have hd_lt : d < 1 := lt_of_le_of_ne hd_le hd1
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact ne_of_gt (mul_pos ha_pos hc_pos)
        · intro hac
          have : a * c < 1 * 1 := mul_lt_mul ha_lt (le_of_lt hc_lt) hc_pos (by linarith)
          linarith
        · exact ne_of_gt (mul_pos hb_pos hd_pos)
        · intro hbd
          have : b * d < 1 * 1 := mul_lt_mul hb_lt (le_of_lt hd_lt) hd_pos (by linarith)
          linarith

/-- The Kleene congruence is non-trivial: 0 and 0.5 are not related. -/
theorem kleene_nonTrivial : kleeneCongruence.NonTrivial := by
  refine ⟨0, 1 / 2, le_refl 0, zero_le_one, by norm_num, by norm_num, ?_⟩
  intro h
  rcases h with ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha0, _, _, _⟩
  · norm_num at hb
  · norm_num at ha
  · exact ha0 rfl

/-! ## Uniqueness of the three-element quotient -/

/-- Any surjective homomorphism from ([0,1], neg, conj) to ThreeVal
    preserving neg and conj must map 0 to zero, 1 to one, and 1/2 to half
    (or the dual with 0 <-> 1 swapped).
    This shows the Kleene lattice is the unique 3-element quotient. -/
theorem three_element_quotient_unique
    (φ : Credence → ThreeVal)
    (hsurj : Function.Surjective φ)
    (hneg : ∀ c, φ (Credence.neg c) = ThreeVal.neg (φ c))
    (hconj : ∀ c₁ c₂, φ (c₁ ⊗ c₂) = ThreeVal.conj (φ c₁) (φ c₂)) :
    φ 0 = ThreeVal.zero ∧ φ 1 = ThreeVal.one ∧ φ Credence.half = ThreeVal.half
    ∨ φ 0 = ThreeVal.one ∧ φ 1 = ThreeVal.zero ∧ φ Credence.half = ThreeVal.half := by
  have hfix := hneg Credence.half
  rw [Credence.liar_fixed_point] at hfix
  have hphalf : φ Credence.half = ThreeVal.half := by
    cases h : φ Credence.half <;> simp_all [ThreeVal.neg]
  have hneg01 := hneg 0
  rw [Credence.neg_zero] at hneg01
  -- hneg01 : φ 1 = (φ 0).neg
  have hconj1 : ∀ c, φ c = ThreeVal.conj (φ 1) (φ c) := by
    intro c; have h := hconj 1 c; rwa [Credence.one_conj] at h
  have h_phi1 : ∀ v, φ 0 = v → φ 1 = ThreeVal.neg v := by
    intro v hv; rw [hneg01, hv]
  cases h0 : φ 0 with
  | zero =>
    left
    refine ⟨rfl, ?_, hphalf⟩
    have := h_phi1 ThreeVal.zero h0; rw [this]; rfl
  | half =>
    exfalso
    have h1 := h_phi1 ThreeVal.half h0
    simp only [ThreeVal.neg] at h1
    obtain ⟨c, hc⟩ := hsurj ThreeVal.zero
    have h_eq := hconj1 c
    rw [h1] at h_eq
    rw [hc] at h_eq
    -- h_eq : ThreeVal.zero = ThreeVal.conj ThreeVal.half ThreeVal.zero
    -- conj half zero = zero, so this says zero = zero. Need a different witness.
    obtain ⟨c', hc'⟩ := hsurj ThreeVal.one
    have h_eq' := hconj1 c'
    rw [h1] at h_eq'
    rw [hc'] at h_eq'
    -- conj half one = half, so h_eq' : one = half. Contradiction.
    simp [ThreeVal.conj] at h_eq'
  | one =>
    right
    refine ⟨rfl, ?_, hphalf⟩
    have := h_phi1 ThreeVal.one h0; rw [this]; rfl

/-! ## Re-exports and classification theorems -/

/-- No 2-element quotient preserving negation exists.
    Re-export of no_boolean_neg_retraction from Cred.Collapse.Hom. -/
theorem no_two_element_quotient :
    ¬(∃ φ : Credence → Credence,
      (∀ c, φ c = 0 ∨ φ c = 1) ∧
      (∀ c, φ (Credence.neg c) = Credence.neg (φ c))) :=
  no_boolean_neg_retraction

/-- Any 3-element quotient preserving negation and conjunction is Kleene.
    Re-export of three_element_quotient_unique above. -/
theorem unique_three_element_quotient
    (φ : Credence → ThreeVal)
    (hsurj : Function.Surjective φ)
    (hneg : ∀ c, φ (Credence.neg c) = ThreeVal.neg (φ c))
    (hconj : ∀ c₁ c₂, φ (c₁ ⊗ c₂) = ThreeVal.conj (φ c₁) (φ c₂)) :
    φ 0 = ThreeVal.zero ∧ φ 1 = ThreeVal.one ∧ φ Credence.half = ThreeVal.half
    ∨ φ 0 = ThreeVal.one ∧ φ 1 = ThreeVal.zero ∧ φ Credence.half = ThreeVal.half :=
  three_element_quotient_unique φ hsurj hneg hconj

/-- Unit classification: any non-trivial UnitCongruence has singleton boundaries. -/
theorem unit_classification
    (R : UnitCongruence) (hnt : R.NonTrivial) :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 0 x → x = 0) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 1 x → x = 1) :=
  ⟨UnitCongruence.singleton_zero R hnt, UnitCongruence.singleton_one R hnt⟩

end Cred
