/-
  Cred Cond: Bayes Consistency and Dependence Policies on [0,1]

  PAPER CROSS-REFERENCES (part1/paper.tex):
  -----------------------------------------
  thm:uniqueness-main  → min_bayes_consistent, prod_trivial_conditioning,
                         min_nontrivial_conditioning, truth_functional_forces_min, luk_not_idempotent
  thm:min-copula-unique → min_copula_unique, symmetric_idempotent_2incr_ge_min
  thm:max-dependence   → min_bayes_consistent, prod_trivial_conditioning,
                         min_nontrivial_conditioning, truth_functional_forces_min
  thm:copula-unique    → copula_idempotent_unique, no_intermediate_idempotent_copula
  prop:resid-bayes     → prod_resid_bayes_consistent_real
  prop:godel-not-bayes → godel_not_bayes_consistent_real
  prop:rm3-not-bayes   → rm3_not_bayes_consistent_real
  prop:indep-classical → independence_within_forces_classical, product_idempotent_iff_classical
  prop:cross-trivial   → cross_world_independence_trivial
-/

import Cred.Cond.Admissible

namespace Cred

/-! ## Bayes Consistency on [0,1]

Formalizes the paper's pen-and-paper proofs: product-residuated Bayes
consistency, Gödel failure on the continuum, the copula/dependence boundary,
and t-norm conditioning uniqueness.

Terminology discipline: a t-norm or truth-functional joint is a fixed coupling
policy on scalar values.  General probability does not fix the joint from the
marginals; it supplies event/proposition-specific dependence data.
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

/-- Any symmetric scalar coupling gives a Bayes-consistent arrow when both
    marginals are positive.  This is a value-level coupling statement, not a
    claim that probability joints are truth-functional in general. -/
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

/-! ## Fixed scalar couplings: max dependence (min) and independence (product)

The following theorems formalize the boundary between truth-functional fuzzy
connectives and probability-style dependence:
- min_bayes_consistent: the min coupling is Bayes-consistent;
- prod_trivial_conditioning: the product coupling is independence and gives
  trivial conditioning;
- the uniqueness results below say that if one insists on one idempotent,
  symmetric, copula-like scalar joint function for all proposition pairs, then
  the coupling is forced to be min.

This is not a statement that general copulas collapse to min.  It is a warning
that probability-style reasoning requires abandoning truth-functionality: the
joint must be allowed to depend on the events/propositions, not only on their
marginal scalar values.
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

/-! ## Uniqueness of the idempotent scalar copula-like joint

The following theorems prove that min is the unique scalar function satisfying
symmetry, idempotence, boundary conditions, and the 2-increasing copula
condition.  This is a truth-functionality boundary, not a denial of the rich
family of probabilistic copulas.

Correct reading: no intermediate scalar truth-function for conjunction can be
both idempotent and copula-like under these assumptions.  To represent general
probabilistic dependence, do not use a single function ℝ × ℝ → ℝ for every pair;
supply the joint on propositions/events.
-/

/-- The 2-increasing property for a joint function.
    For any rectangle [a₁,a₂] × [b₁,b₂], the "volume" is non-negative:
    j(a₂,b₂) - j(a₂,b₁) - j(a₁,b₂) + j(a₁,b₁) ≥ 0 -/
def TwoIncreasing (j : ℝ → ℝ → ℝ) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : ℝ, a₁ ≤ a₂ → b₁ ≤ b₂ →
    j a₂ b₂ - j a₂ b₁ - j a₁ b₂ + j a₁ b₁ ≥ 0

/-- Key lemma: If j is symmetric, idempotent, has zero boundary, and is 2-increasing,
    then j(a,b) ≥ min(a,b) for all a,b ∈ [0,1]. -/
theorem symmetric_idempotent_2incr_ge_min (j : ℝ → ℝ → ℝ)
    (hsymm : ∀ a b, j a b = j b a)
    (hidemp : ∀ a, j a a = a)
    (hzero : ∀ b, j 0 b = 0)
    (h2incr : TwoIncreasing j)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ j a b := by
  wlog hab : a ≤ b generalizing a b
  · push_neg at hab
    rw [hsymm, min_comm]
    exact this b a hb ha (le_of_lt hab)
  -- Now a ≤ b, so min a b = a
  rw [min_eq_left hab]
  -- Apply 2-increasing to rectangle [0,a] × [a,b]
  have h := h2incr 0 a a b (by linarith) hab
  -- j(a,b) - j(a,a) - j(0,b) + j(0,a) ≥ 0
  simp only [hidemp, hzero] at h
  -- j(a,b) - a - 0 + 0 ≥ 0
  linarith

/-- Main uniqueness theorem: If j is symmetric, idempotent, has zero boundary,
    is bounded above by min, and is 2-increasing, then j = min.
    This proves min is the unique scalar copula-like function with these properties. -/
theorem min_copula_unique (j : ℝ → ℝ → ℝ)
    (hsymm : ∀ a b, j a b = j b a)
    (hidemp : ∀ a, j a a = a)
    (hzero : ∀ b, j 0 b = 0)
    (hupper : ∀ a b, j a b ≤ min a b)
    (h2incr : TwoIncreasing j)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    j a b = min a b := by
  apply le_antisymm
  · exact hupper a b
  · exact symmetric_idempotent_2incr_ge_min j hsymm hidemp hzero h2incr a b ha hb

/-- Helper: The Fréchet upper bound follows from copula axioms -/
theorem copula_frechet_upper (j : ℝ → ℝ → ℝ)
    (hzero_left : ∀ b, j 0 b = 0)
    (hzero_right : ∀ a, j a 0 = 0)
    (hone_left : ∀ b, 0 ≤ b → b ≤ 1 → j 1 b = b)
    (hone_right : ∀ a, 0 ≤ a → a ≤ 1 → j a 1 = a)
    (h2incr : TwoIncreasing j)
    (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    j a b ≤ min a b := by
  apply le_min
  · -- j(a,b) ≤ a: use 2-increasing on [0,a] × [b,1]
    have h := h2incr 0 a b 1 ha hb'
    simp only [hone_right a ha ha', hzero_left, hzero_right] at h
    linarith
  · -- j(a,b) ≤ b: use 2-increasing on [a,1] × [0,b]
    have h := h2incr a 1 0 b ha' hb
    simp only [hone_left b hb hb', hzero_right] at h
    linarith

/-- Corollary: No intermediate scalar copula-like truth function between
    independence and max-dependence can satisfy both idempotence and the copula axioms.
    Specifically, if j(a,a) = a and j is a scalar copula-like function, then j = min.
    Independence (product) fails idempotence except at Boolean values. -/
theorem no_intermediate_idempotent_copula (j : ℝ → ℝ → ℝ)
    (hsymm : ∀ a b, j a b = j b a)
    (hidemp : ∀ a, j a a = a)
    (hzero_left : ∀ b, j 0 b = 0)
    (hzero_right : ∀ a, j a 0 = 0)
    (hone_left : ∀ b, 0 ≤ b → b ≤ 1 → j 1 b = b)
    (hone_right : ∀ a, 0 ≤ a → a ≤ 1 → j a 1 = a)
    (h2incr : TwoIncreasing j)
    (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    j a b = min a b := by
  have hupper := copula_frechet_upper j hzero_left hzero_right hone_left hone_right h2incr a b ha ha' hb hb'
  apply le_antisymm hupper
  exact symmetric_idempotent_2incr_ge_min j hsymm hidemp hzero_left h2incr a b ha hb

/-! ## Mixed Dependence Structures

Can we mix dependence structures -- e.g. use independence for some pairs and
max-dependence for others?  Yes, but then the joint depends not just on the
marginal VALUES but also on WHICH propositions are involved.

This is the probability-style approach: P(A∧B) depends on the specific events
A and B, not just P(A) and P(B).  It is exactly what truth-functionality forbids.

The following theorem shows that if we want the SAME scalar j for all pairs
(truth-functionality), then Bayes consistency + idempotence forces j = min.
-/

/-- If we require the same joint function for all proposition pairs
    (truth-functionality), and require Bayes consistency and idempotence,
    then the joint must be min (max positive dependence).

    Relaxing to different joints for different pairs gives probability-style
    reasoning but loses truth-functionality. -/
theorem truth_functional_forces_min :
    ∀ j : ℝ → ℝ → ℝ,
      (∀ a b, j a b = j b a) →  -- Bayes consistency
      (∀ a, j a a = a) →        -- Idempotence
      (∀ b, j 0 b = 0) →        -- Zero boundary
      (∀ a b, j a b ≤ min a b) → -- Fréchet upper
      TwoIncreasing j →          -- Copula property
      ∀ a b, 0 ≤ a → 0 ≤ b → j a b = min a b :=
  fun j hsymm hidemp hzero hupper h2incr a b ha hb =>
    min_copula_unique j hsymm hidemp hzero hupper h2incr a b ha hb

/-! ## World Partitioning: Independence Between Worlds

We analyze value-level partitioning of proposition pairs into dependence classes.
The key results are:

1. Product/independence WITHIN a self-pair world forces credences to {0,1}, because
   idempotence j(a,a)=a conflicts with product j(a,a)=a² away from the boundary.
2. Product/independence BETWEEN worlds is consistent but trivializes cross-world inference.
3. If one insists on a single truth-functional idempotent scalar joint within a world,
   max-dependence (min) is forced by the copula-like assumptions.
-/

/-- Independence within a world forces classical credences.
    If j(a,a) = a² (product/independence), then a = a² implies a ∈ {0,1}.
    This proves: independence WITHIN a world collapses credences to boolean. -/
theorem independence_within_forces_classical (a : ℝ) (_ha : 0 ≤ a) (_ha' : a ≤ 1)
    (hidemp_prod : a * a = a) :
    a = 0 ∨ a = 1 := by
  have h : a * (a - 1) = 0 := by linarith [hidemp_prod]
  rcases mul_eq_zero.mp h with ha0 | ha1
  · left; exact ha0
  · right; linarith

/-- Corollary: Product copula idempotence only at extremes.
    The product j(a,a) = a·a equals a only when a ∈ {0,1}. -/
theorem product_idempotent_iff_classical (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    a * a = a ↔ a = 0 ∨ a = 1 := by
  constructor
  · exact independence_within_forces_classical a ha ha'
  · intro h
    rcases h with rfl | rfl <;> ring

/-- Cross-world independence trivializes conditioning.
    If j(a,b) = a·b (product), then cred(A|B) = cred(A) for b ≠ 0.
    Evidence from another world has no effect. -/
theorem cross_world_independence_trivial (a b : ℝ) (hb : b ≠ 0) :
    (a * b) / b = a := by
  field_simp

/-- Max-dependence within a truth-functional scalar world is forced by
    idempotence + copula-like assumptions. -/
theorem within_world_max_dependence_forced (j : ℝ → ℝ → ℝ)
    (hsymm : ∀ a b, j a b = j b a)
    (hidemp : ∀ a, j a a = a)
    (hzero : ∀ b, j 0 b = 0)
    (hupper : ∀ a b, j a b ≤ min a b)
    (h2incr : TwoIncreasing j) :
    ∀ a b, 0 ≤ a → 0 ≤ b → j a b = min a b :=
  min_copula_unique j hsymm hidemp hzero hupper h2incr

/-! ## Probability as dependence-enriched logic

Can probability serve as a generalization of logical reasoning?  The key issue
is how to assign joint probabilities.

1. Standard probability: P(A∧B) depends on the SPECIFIC propositions/events A, B
   (not just P(A) and P(B)).  This is exactly what truth-functionality forbids.

2. If one insists on a value-only truth-functional conjunction for mathematical
   propositions, idempotence P(A∧A)=P(A) rules out the product coupling except at
   Boolean values, because P(A)²=P(A) only for {0,1}.

3. Under the scalar copula-like assumptions above, idempotence forces the min
   coupling.  That identifies the maximally dependent truth-functional boundary,
   not the full probabilistic setting.

4. To move toward probability-as-logic, free the joint from truth-functionality:
   supply J(A,B) as dependence data, subject to Fréchet/coherence constraints.
-/

/-- Probability-style reasoning requires abandoning truth-functionality.
    If we want j to vary based on proposition pairs (not just values),
    then j is a function on Prop × Prop, not ℝ × ℝ.

    This theorem shows that any truth-functional scalar approach with idempotence
    and the stated copula-like assumptions must use min. -/
theorem truth_functional_idempotent_implies_max_dependence :
    ∀ j : ℝ → ℝ → ℝ,
      (∀ a, j a a = a) →              -- Idempotence (mathematical world requirement)
      (∀ a b, j a b ≤ min a b) →      -- Fréchet upper bound
      (∀ b, j 0 b = 0) →              -- Zero boundary
      (∀ a b, j a b = j b a) →        -- Symmetry
      TwoIncreasing j →                -- Copula property
      ∀ a b, 0 ≤ a → 0 ≤ b → j a b = min a b :=
  fun j hidemp hupper hzero hsymm h2incr a b ha hb =>
    min_copula_unique j hsymm hidemp hzero hupper h2incr a b ha hb

/-- Łukasiewicz t-norm fails idempotence: max(2a - 1, 0) ≠ a for a ∈ (1/2, 1).
    This directly verifies the claim in the paper about Łukasiewicz. -/
theorem luk_not_idempotent :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ max (2 * a - 1) 0 ≠ a := by
  use 3/4
  constructor
  · norm_num
  constructor
  · norm_num
  · simp only [max_eq_left (by norm_num : (0:ℝ) ≤ 2 * (3/4) - 1)]
    norm_num

/-- Wrapper: standard copula axioms + idempotence force min.
    This connects no_intermediate_idempotent_copula to the papers Thm 3.1:
    the Frechet upper bound is DERIVED from copula axioms, not assumed.
    The paper can cite this single theorem for the clean statement. -/
theorem copula_idempotent_unique (j : ℝ → ℝ → ℝ)
    (hsymm : ∀ a b, j a b = j b a)
    (hidemp : ∀ a, j a a = a)
    (hzero_right : ∀ a, j a 0 = 0)
    (hone_left : ∀ b, 0 ≤ b → b ≤ 1 → j 1 b = b)
    (h2incr : TwoIncreasing j)
    (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    j a b = min a b := by
  have hzero_left : ∀ b, j 0 b = 0 := fun b => by rw [hsymm]; exact hzero_right b
  have hone_right : ∀ a, 0 ≤ a → a ≤ 1 → j a 1 = a := by
    intro a' ha0 ha1; rw [hsymm]; exact hone_left a' ha0 ha1
  exact no_intermediate_idempotent_copula j hsymm hidemp hzero_left hzero_right
    hone_left hone_right h2incr a b ha ha' hb hb'

end Cred