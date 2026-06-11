/-
  Congruence Classification: RealCongruence (full R-multiplication)

  Under RealCongruence no non-trivial finite quotient exists at all:
  the scaling trick produces values outside [0,1].

  PAPER CROSS-REFERENCES (part1/paper.tex):
  ------------------------------------------
  thm:congruence-main (4) -> RealCongruence.no_nontrivial_finite_quotient
  thm:zero-collapse    -> zero_equiv_forces_trivial
-/

import Cred.Congruence.Unit

namespace Cred

/-! ## Building block: identifying 0 with a positive value is fatal

Under unbounded multiplication, identifying 0 with any positive value
forces the trivial (1-element) quotient. -/

/-- If a congruence on ([0,1], neg, conj) identifies 0 with some eps > 0,
    then it identifies everything with 0 (the quotient is trivial).

    Proof: 0 ~ eps implies 0 ~ eps*y for all y (conj-compat with refl).
    So [0, eps] is contained in the equivalence class of 0.
    Separately, 1 ~ 1-eps (neg), so x ~ x*(1-eps) for all x.
    By induction x ~ x*(1-eps)^n. For large n, x*(1-eps)^n < eps,
    and we can write x*(1-eps)^n = eps * (x*(1-eps)^n / eps) with
    the second factor in [0,1], so 0 ~ x*(1-eps)^n, hence x ~ 0. -/
theorem zero_equiv_forces_trivial
    (R : ℝ → ℝ → Prop)
    (hrefl : ∀ a, R a a)
    (hsymm : ∀ a b, R a b → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hneg : ∀ a b, R a b → R (1 - a) (1 - b))
    (hconj : ∀ a b c d, R a b → R c d → R (a * c) (b * d))
    (eps : ℝ) (heps_pos : 0 < eps) (heps_le : eps ≤ 1)
    (hzero_eps : R 0 eps) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R x 0 := by
  have h_one_comp : R 1 (1 - eps) := by
    have h := hneg 0 eps hzero_eps; rwa [sub_zero] at h
  have h_scale : ∀ x, R x (x * (1 - eps)) := by
    intro x
    have h1 : R (x * 1) (x * (1 - eps)) := hconj x x 1 (1 - eps) (hrefl x) h_one_comp
    rwa [mul_one] at h1
  have h_zero_scaled : ∀ y, R 0 (eps * y) := by
    intro y
    have h1 : R (0 * y) (eps * y) := hconj 0 eps y y hzero_eps (hrefl y)
    rwa [zero_mul] at h1
  have h_iter : ∀ x, ∀ n : ℕ, R x (x * (1 - eps) ^ n) := by
    intro x n
    induction n with
    | zero => simp [pow_zero, mul_one]; exact hrefl x
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact htrans x (x * (1 - eps) ^ n) (x * (1 - eps) ^ n * (1 - eps))
        ih (h_scale (x * (1 - eps) ^ n))
  have h_base_nn : 0 ≤ 1 - eps := by linarith
  intro x hx_nn hx_le
  by_cases hx_zero : x = 0
  · rw [hx_zero]; exact hrefl 0
  · have hx_pos : 0 < x := lt_of_le_of_ne hx_nn (Ne.symm hx_zero)
    have h_exists_n : ∃ n : ℕ, x * (1 - eps) ^ n ≤ eps := by
      have h_lt_one : 1 - eps < 1 := by linarith
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps_pos h_lt_one
      refine ⟨n, ?_⟩
      calc x * (1 - eps) ^ n ≤ 1 * (1 - eps) ^ n :=
            mul_le_mul_of_nonneg_right hx_le (pow_nonneg h_base_nn n)
        _ = (1 - eps) ^ n := one_mul _
        _ ≤ eps := le_of_lt hn
    obtain ⟨n, hn⟩ := h_exists_n
    have hpow_nn : 0 ≤ x * (1 - eps) ^ n :=
      mul_nonneg hx_nn (pow_nonneg h_base_nn n)
    have hR_0_xpow : R 0 (x * (1 - eps) ^ n) := by
      have hq_nn : 0 ≤ x * (1 - eps) ^ n / eps := div_nonneg hpow_nn (le_of_lt heps_pos)
      have hq_le : x * (1 - eps) ^ n / eps ≤ 1 := (div_le_one heps_pos).mpr hn
      have h_eq : eps * (x * (1 - eps) ^ n / eps) = x * (1 - eps) ^ n := by
        field_simp
      rw [← h_eq]
      exact h_zero_scaled (x * (1 - eps) ^ n / eps)
    exact htrans x (x * (1 - eps) ^ n) 0
      (h_iter x n) (hsymm _ _ hR_0_xpow)

/-! ## RealCongruence: full R-multiplication -/

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

end Cred
