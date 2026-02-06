/-
  Congruence Classification of Finite Quotients

  Two congruence notions:
  - UnitCongruence: compatibility with [0,1]-multiplication (physically meaningful)
  - RealCongruence: compatibility with full R-multiplication (strictly stronger)

  The Kleene lattice ({0}, (0,1), {1}) is the unique non-trivial finite quotient
  under UnitCongruence. Under RealCongruence, no non-trivial finite quotient exists
  at all (the scaling trick produces values outside [0,1]).

  PAPER CROSS-REFERENCES (part1/paper.tex):
  ------------------------------------------
  thm:congruence-main  -> unit_classification, no_nontrivial_finite_quotient
  (1) UnitCongruence.singleton_zero, UnitCongruence.singleton_one
  (2) no_two_element_quotient (from Basic.lean: no_boolean_neg_retraction)
  (3) unique_three_element_quotient (from Basic.lean: three_element_quotient_unique)
  (4) RealCongruence.no_nontrivial_finite_quotient

  Building blocks from Basic.lean:
  - zero_equiv_forces_trivial: if 0 ~ eps > 0 then everything collapses (R-mult)
  - no_boolean_neg_retraction: no 2-element quotient preserving negation
  - three_element_quotient_unique: any 3-element quotient is Kleene
  - neg_fixed_point_unique: 1/2 is the unique negation fixed point
-/

import Cred.Basic

namespace Cred

open Credence

/-! ## Part 1: UnitCongruence — [0,1]-multiplication -/

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

/-! ## Part 2: RealCongruence — full R-multiplication -/

/-- A congruence on the credence algebra with unrestricted real multiplication.
    conj_compat has no bound requirements, enabling the scaling trick that
    rules out all non-trivial finite quotients. -/
structure RealCongruence where
  rel : ℝ → ℝ → Prop
  refl : ∀ a, rel a a
  symm : ∀ a b, rel a b → rel b a
  trans : ∀ a b c, rel a b → rel b c → rel a c
  neg_compat : ∀ a b, rel a b → rel (1 - a) (1 - b)
  conj_compat : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)

namespace RealCongruence

/-- A congruence is non-trivial if it does not identify all [0,1] elements. -/
def NonTrivial (R : RealCongruence) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ ¬R.rel a b

/-- Every RealCongruence restricts to a UnitCongruence by ignoring the
    bound hypotheses (they are unused in conj_compat). -/
def toUnit (R : RealCongruence) : UnitCongruence where
  rel := R.rel
  refl := R.refl
  symm := R.symm
  trans := R.trans
  neg_compat := R.neg_compat
  conj_compat := fun a b c d _ _ _ _ _ _ _ _ hab hcd => R.conj_compat a b c d hab hcd

theorem toUnit_nonTrivial (R : RealCongruence) (hnt : R.NonTrivial) :
    R.toUnit.NonTrivial := hnt

/-- {0} is a singleton for RealCongruence (via UnitCongruence). -/
theorem singleton_zero (R : RealCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 0 x → x = 0 :=
  UnitCongruence.singleton_zero R.toUnit (toUnit_nonTrivial R hnt)

/-- {1} is a singleton for RealCongruence (via UnitCongruence). -/
theorem singleton_one (R : RealCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 1 x → x = 1 :=
  UnitCongruence.singleton_one R.toUnit (toUnit_nonTrivial R hnt)

/-! ### Scaling trick helpers -/

/-- Powers of related elements stay related: if a ~ b then a^n ~ b^n. -/
theorem rel_pow (R : RealCongruence) {a b : ℝ} (hab : R.rel a b) :
    ∀ n : ℕ, R.rel (a ^ n) (b ^ n) := by
  intro n
  induction n with
  | zero => simp [pow_zero]; exact R.refl 1
  | succ n ih => rw [pow_succ, pow_succ]; exact R.conj_compat _ _ _ _ ih hab

/-- In a finite quotient, power iteration cycles: exists i < j with
    classify(a^i) = classify(a^j). Pure pigeonhole on Fin nclasses. -/
theorem finite_class_cycle (nclasses : ℕ)
    (classify : ℝ → Fin nclasses)
    (a : ℝ) :
    ∃ i j : ℕ, i < j ∧ j ≤ nclasses ∧ classify (a ^ i) = classify (a ^ j) := by
  by_contra h
  push_neg at h
  have hinj : ∀ i j, i ≤ nclasses → j ≤ nclasses → i ≠ j →
      classify (a ^ i) ≠ classify (a ^ j) := by
    intro i j hi hj hne heq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (h i j hlt hj).elim heq
    · exact (h j i hgt hi).elim heq.symm
  let f : Fin (nclasses + 1) → Fin nclasses := fun i => classify (a ^ i.val)
  have hf : Function.Injective f := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [f, Fin.mk.injEq] at heq ⊢
    by_contra hne
    exact hinj i j (Nat.lt_succ_iff.mp hi) (Nat.lt_succ_iff.mp hj) hne heq
  exact absurd (Fintype.card_le_of_injective f hf) (by simp [Fintype.card_fin])

/-- All iterates along a period are in the same class as the base. -/
theorem rel_along_period (R : RealCongruence) (a : ℝ) (i p : ℕ)
    (hcycle : R.rel (a ^ i) (a ^ (i + p))) :
    ∀ k : ℕ, R.rel (a ^ i) (a ^ (i + k * p)) := by
  intro k
  induction k with
  | zero => simp; exact R.refl _
  | succ k ih =>
    have h_mul : R.rel (a ^ i * a ^ p) (a ^ (i + k * p) * a ^ p) :=
      R.conj_compat _ _ _ _ ih (R.refl (a ^ p))
    have heq1 : a ^ i * a ^ p = a ^ (i + p) := by rw [pow_add]
    have heq2 : a ^ (i + k * p) * a ^ p = a ^ (i + (k + 1) * p) := by
      rw [pow_add]; ring_nf
    rw [heq1, heq2] at h_mul
    exact R.trans _ _ _ hcycle h_mul

/-- No non-trivial RealCongruence admits a finite quotient.

    Scaling-trick proof: Pick a = 1/2. Pigeonhole gives i < j with
    classify(a^i) = classify(a^j). The converse hypothesis hquot yields
    R.rel (a^i) (a^j). Write a^j = a^i * a^p where p = j - i > 0.
    Multiply both sides by (a^i)^{-1} using conj_compat (which operates
    on all of R, not just [0,1]) to get R.rel 1 (a^p).
    Apply neg_compat to get R.rel 0 (1 - a^p).
    Since 0 < a^p < 1 we have 0 < 1 - a^p, so singleton_zero forces
    1 - a^p = 0, i.e. a^p = 1 -- contradicting 0 < a < 1. -/
theorem no_nontrivial_finite_quotient (R : RealCongruence) (hnt : R.NonTrivial)
    (nclasses : ℕ)
    (classify : ℝ → Fin nclasses)
    (hquot : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      classify a = classify b → R.rel a b) :
    False := by
  set a : ℝ := 1 / 2
  have ha_pos : (0 : ℝ) < a := by norm_num
  have ha_lt : a < 1 := by norm_num
  have ha_nn : (0 : ℝ) ≤ a := le_of_lt ha_pos
  have ha_le : a ≤ 1 := le_of_lt ha_lt
  obtain ⟨i, j, hij, _, hclass⟩ := finite_class_cycle nclasses classify a
  have hp_pos : 0 < j - i := Nat.sub_pos_of_lt hij
  set p := j - i
  have hj_eq : j = i + p := (Nat.add_sub_cancel' (le_of_lt hij)).symm
  rw [hj_eq] at hclass
  have hai_pos : (0 : ℝ) < a ^ i := pow_pos ha_pos i
  have hai_nn : (0 : ℝ) ≤ a ^ i := le_of_lt hai_pos
  have hai_le : a ^ i ≤ 1 := pow_le_one₀ ha_nn ha_le
  have haj_nn : (0 : ℝ) ≤ a ^ (i + p) := pow_nonneg ha_nn (i + p)
  have haj_le : a ^ (i + p) ≤ 1 := pow_le_one₀ ha_nn ha_le
  have hrel : R.rel (a ^ i) (a ^ (i + p)) :=
    hquot _ _ hai_nn hai_le haj_nn haj_le hclass
  have hrewrite : a ^ (i + p) = a ^ i * a ^ p := by rw [pow_add]
  rw [hrewrite] at hrel
  have hai_inv_pos : (0 : ℝ) < (a ^ i)⁻¹ := inv_pos.mpr hai_pos
  have hscale_raw : R.rel ((a ^ i)⁻¹ * (a ^ i)) ((a ^ i)⁻¹ * (a ^ i * a ^ p)) :=
    R.conj_compat _ _ _ _ (R.refl (a ^ i)⁻¹) hrel
  have hleft : (a ^ i)⁻¹ * a ^ i = 1 := inv_mul_cancel₀ (ne_of_gt hai_pos)
  have hright : (a ^ i)⁻¹ * (a ^ i * a ^ p) = a ^ p := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hai_pos), one_mul]
  rw [hleft, hright] at hscale_raw
  have hrel_neg : R.rel 0 (1 - a ^ p) := by
    have h := R.neg_compat 1 (a ^ p) hscale_raw; rwa [sub_self] at h
  have hap_pos : (0 : ℝ) < a ^ p := pow_pos ha_pos p
  have hp_ne : p ≠ 0 := Nat.not_eq_zero_of_lt hp_pos
  have hap_lt : a ^ p < 1 := pow_lt_one₀ ha_pos.le ha_lt hp_ne
  have hap_comp_pos : (0 : ℝ) < 1 - a ^ p := by linarith
  have hap_comp_le : 1 - a ^ p ≤ 1 := by linarith [hap_pos]
  have := singleton_zero R hnt (1 - a ^ p) (le_of_lt hap_comp_pos) hap_comp_le hrel_neg
  linarith

end RealCongruence

/-! ## Part 3: Kleene partition as a concrete UnitCongruence -/

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

/-! ## Part 4: Re-exports and classification theorems -/

/-- No 2-element quotient preserving negation exists.
    Re-export of no_boolean_neg_retraction from Basic.lean. -/
theorem no_two_element_quotient :
    ¬(∃ φ : Credence → Credence,
      (∀ c, φ c = 0 ∨ φ c = 1) ∧
      (∀ c, φ (Credence.neg c) = Credence.neg (φ c))) :=
  no_boolean_neg_retraction

/-- Any 3-element quotient preserving negation and conjunction is Kleene.
    Re-export of three_element_quotient_unique from Basic.lean. -/
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
