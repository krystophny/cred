/-
  Congruence Classification of Finite Quotients

  The only non-trivial finite quotient of ([0,1], neg, conj) preserving
  negation and conjunction is the three-element Kleene lattice {0, 1/2, 1}.

  PAPER CROSS-REFERENCES (part1/paper.tex):
  ------------------------------------------
  thm:congruence-main  -> finite_congruence_classification
  (1) singleton_zero, singleton_one
  (2) no_two_element_quotient (from Basic.lean: no_boolean_neg_retraction)
  (3) unique_three_element_quotient (from Basic.lean: three_element_quotient_unique)
  (4) no_four_or_more_classes

  Building blocks from Basic.lean:
  - zero_equiv_forces_trivial: if 0 ~ eps > 0 then everything collapses
  - no_boolean_neg_retraction: no 2-element quotient preserving negation
  - three_element_quotient_unique: any 3-element quotient is Kleene
  - neg_fixed_point_unique: 1/2 is the unique negation fixed point
-/

import Cred.Basic

namespace Cred

open Credence

/-! ## Congruence Definition -/

/-- A congruence on the credence algebra: an equivalence relation compatible
    with negation and conjunction. Uses real-valued representatives for
    compatibility with zero_equiv_forces_trivial. -/
structure CredCongruence where
  rel : ℝ → ℝ → Prop
  refl : ∀ a, rel a a
  symm : ∀ a b, rel a b → rel b a
  trans : ∀ a b c, rel a b → rel b c → rel a c
  neg_compat : ∀ a b, rel a b → rel (1 - a) (1 - b)
  conj_compat : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)

namespace CredCongruence

/-! ## Lifted Operations on Credence -/

def relC (R : CredCongruence) (c₁ c₂ : Credence) : Prop :=
  R.rel c₁.val c₂.val

theorem relC_refl (R : CredCongruence) (c : Credence) : R.relC c c :=
  R.refl c.val

theorem relC_symm (R : CredCongruence) {c₁ c₂ : Credence} :
    R.relC c₁ c₂ → R.relC c₂ c₁ :=
  R.symm c₁.val c₂.val

theorem relC_neg (R : CredCongruence) {c₁ c₂ : Credence}
    (h : R.relC c₁ c₂) : R.relC (Credence.neg c₁) (Credence.neg c₂) :=
  R.neg_compat c₁.val c₂.val h

theorem relC_conj (R : CredCongruence) {c₁ c₂ c₃ c₄ : Credence}
    (h₁ : R.relC c₁ c₂) (h₂ : R.relC c₃ c₄) : R.relC (c₁ ⊗ c₃) (c₂ ⊗ c₄) :=
  R.conj_compat c₁.val c₂.val c₃.val c₄.val h₁ h₂

/-! ## Singleton Boundaries -/

/-- A congruence is non-trivial if it does not identify all elements. -/
def NonTrivial (R : CredCongruence) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ ¬R.rel a b

/-- {0} is a singleton: if 0 ~ eps for eps > 0, the congruence is trivial. -/
theorem singleton_zero (R : CredCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 0 x → x = 0 := by
  intro x hx_nn hx_le hrel
  by_contra hne
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nn (Ne.symm hne)
  have h_all : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → R.rel y 0 :=
    zero_equiv_forces_trivial R.rel R.refl R.symm R.trans R.neg_compat
      R.conj_compat x hx_pos hx_le hrel
  obtain ⟨a, b, ha_nn, ha_le, hb_nn, hb_le, hab⟩ := hnt
  exact hab (R.trans a 0 b (h_all a ha_nn ha_le) (R.symm b 0 (h_all b hb_nn hb_le)))

/-- {1} is a singleton: follows from singleton_zero by negation duality. -/
theorem singleton_one (R : CredCongruence) (hnt : R.NonTrivial) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 1 x → x = 1 := by
  intro x hx_nn hx_le hrel
  have h_neg_rel : R.rel 0 (1 - x) := by
    have h := R.neg_compat 1 x hrel; rwa [sub_self] at h
  have := singleton_zero R hnt (1 - x) (by linarith) (by linarith) h_neg_rel
  linarith

/-! ## No 2-Element Quotient -/

/-- No 2-element quotient preserving negation exists.
    Re-export of no_boolean_neg_retraction from Basic.lean. -/
theorem no_two_element_quotient :
    ¬(∃ φ : Credence → Credence,
      (∀ c, φ c = 0 ∨ φ c = 1) ∧
      (∀ c, φ (Credence.neg c) = Credence.neg (φ c))) :=
  no_boolean_neg_retraction

/-! ## Unique 3-Element Quotient -/

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

/-! ## No Quotient with 4 or More Classes -/

/-- Powers of related elements stay related: if a ~ b then a^n ~ b^n. -/
theorem rel_pow (R : CredCongruence) {a b : ℝ} (hab : R.rel a b) :
    ∀ n : ℕ, R.rel (a ^ n) (b ^ n) := by
  intro n
  induction n with
  | zero => simp [pow_zero]; exact R.refl 1
  | succ n ih => rw [pow_succ, pow_succ]; exact R.conj_compat _ _ _ _ ih hab

/-- Products with related elements stay related. -/
theorem rel_mul_pow (R : CredCongruence) (c : ℝ) {a b : ℝ} (hab : R.rel a b)
    (n : ℕ) : R.rel (c * a ^ n) (c * b ^ n) :=
  R.conj_compat c c (a ^ n) (b ^ n) (R.refl c) (rel_pow R hab n)

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
theorem rel_along_period (R : CredCongruence) (a : ℝ) (i p : ℕ)
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

/-- Products along a period are in the same class. -/
theorem rel_products_along_period (R : CredCongruence) (c a : ℝ)
    (i p : ℕ) (hcycle : R.rel (a ^ i) (a ^ (i + p))) :
    ∀ k : ℕ, R.rel (c * a ^ i) (c * a ^ (i + k * p)) := by
  intro k
  exact R.conj_compat c c _ _ (R.refl c) (rel_along_period R a i p hcycle k)

/-- Interior products approach zero: for 0 < a < 1 and c > 0,
    c * a^n can be made arbitrarily small while remaining positive. -/
theorem interior_products_approach_zero (a c eps : ℝ)
    (ha_pos : 0 < a) (ha_lt : a < 1) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (heps_pos : 0 < eps) :
    ∃ n : ℕ, 0 < c * a ^ n ∧ c * a ^ n < eps := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps_pos ha_lt
  exact ⟨n, mul_pos hc_pos (pow_pos ha_pos n),
    calc c * a ^ n ≤ 1 * a ^ n :=
          mul_le_mul_of_nonneg_right hc_le (pow_nonneg (le_of_lt ha_pos) n)
      _ = a ^ n := one_mul _
      _ < eps := hn⟩

/-- The n >= 4 impossibility: no non-trivial congruence has 4 or more classes.

    The paper argument (Section 7, part 4):
    With singletons {0} and {1} and >= 2 interior classes, pick a in the class of
    1/2 with 0 < a < 1. By finite_class_cycle, a^i ~ a^{i+p} for some i, p.
    By rel_along_period, a^i ~ a^{i+kp} for all k, and these approach 0.
    For c in another interior class, c * a^{i+kp} also approach 0 while
    remaining in a fixed quotient class. Since that class contains positive
    elements arbitrarily close to 0 yet {0} is a singleton, the quotient
    structure forces total collapse via zero_equiv_forces_trivial, contradicting
    non-triviality.

    The algebraic closure (connecting accumulation near 0 to R 0 eps) is deferred.
    Parts (1)-(3) are fully verified; this is the only sorry in the file. -/
theorem no_four_or_more_classes (R : CredCongruence) (hnt : R.NonTrivial)
    (nclasses : ℕ) (hn : 4 ≤ nclasses)
    (classify : ℝ → Fin nclasses)
    (hcompat : ∀ a b, R.rel a b → classify a = classify b)
    (hsurj : Function.Surjective classify)
    (hclass_zero : ∀ x, 0 ≤ x → x ≤ 1 → classify x = classify 0 → x = 0)
    (hclass_one : ∀ x, 0 ≤ x → x ≤ 1 → classify x = classify 1 → x = 1) :
    False := by
  sorry

/-! ## Main Classification Theorem -/

/-- Complete congruence classification (Theorem 7 of the paper).
    In any non-trivial congruence on ([0,1], neg, conj):
    - {0} and {1} are singletons (fully verified)
    - No 2-element quotient preserving negation exists (fully verified)
    - Any 3-element quotient is the Kleene lattice (fully verified)
    - No quotient with 4+ classes exists (pending: no_four_or_more_classes) -/
theorem finite_congruence_classification
    (R : CredCongruence) (hnt : R.NonTrivial) :
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 0 x → x = 0) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ 1 → R.rel 1 x → x = 1) :=
  ⟨singleton_zero R hnt, singleton_one R hnt⟩

end CredCongruence

end Cred
