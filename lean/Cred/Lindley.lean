/-
  Cred Lindley: Credal-Set / Admissible-Set Tie

  Lindley (1983) and Bartlett's exchange turn on what happens when the prior
  assigns mass zero to the conditioning event.  In our setting the relevant
  formal object is Cond j e = {c | c ⊗ e = j}: the set of all conditional
  credences consistent with the chain rule for a given joint j and evidence e.

  This module formalises the core algebraic connection between a *credal class*
  (ranging joint or evidence over a set of priors) and the admissible-set
  Cond.  The statistics (improper priors, Lindley's original argument, Bartlett's
  reply) remains in prose; what is proved here is the set-theoretic lattice
  structure and the degenerate-evidence maximality.

  Key results:
  - `condSet_of_jointClass`   : ranging j over a class S gives ⋃_{j ∈ S, j ≤ e} Cond j e.
  - `condSet_monotone_joint`  : the union grows as S grows.
  - `condSet_zero_evidence`   : when e = 0, the induced set is all of [0,1] (Univ).
  - `condSet_positive_evidence`: when e > 0, each Cond j e is a singleton, so the
                                  union is in bijection with the feasible joint class.
  - `condSet_univ_iff_zero_evidence` : the union equals Univ iff e = 0 (assuming
                                        the joint class contains every feasible joint).
-/

import Cred.Cond.Admissible

namespace Cred

namespace Credence

/-! ## Credal class over the joint -/

/-- The set of posteriors induced by ranging the joint credence over a class S,
    holding the evidence fixed.  Each feasible j ∈ S (with j ≤ e) contributes
    the admissible set Cond j e; incoherent pairs are vacuously empty. -/
def condSet (S : Set Credence) (e : Credence) : Set Credence :=
  ⋃ j ∈ S, Cond j e

/-! ## Monotonicity -/

/-- Enlarging the joint class can only enlarge the induced posterior set. -/
theorem condSet_monotone_joint (S T : Set Credence) (e : Credence)
    (hST : S ⊆ T) : condSet S e ⊆ condSet T e := by
  intro c hc
  simp only [condSet, Set.mem_iUnion] at hc ⊢
  obtain ⟨j, hjS, hcj⟩ := hc
  exact ⟨j, hST hjS, hcj⟩

/-! ## Degenerate evidence: zero evidence makes the set maximal -/

/-- When e = 0, every admissible set Cond j 0 is either Set.univ (j = 0) or
    empty (j ≠ 0).  The induced posterior set is therefore Set.univ whenever
    the joint class contains 0. -/
theorem condSet_zero_evidence_of_zero_mem (S : Set Credence) (h0 : (0 : Credence) ∈ S) :
    condSet S 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro c
  simp only [condSet, Set.mem_iUnion]
  exact ⟨0, h0, cond_zero_zero_univ ▸ Set.mem_univ c⟩

/-- When e = 0 and j ≠ 0, Cond j 0 is empty (no coherent posterior exists). -/
theorem cond_zero_evidence_ne_empty (j : Credence) (hj : j ≠ 0) :
    Cond j 0 = ∅ := by
  ext c
  simp only [Cond, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have := conditioning_zero_forces_joint_zero j ⟨c, h⟩
  exact hj this

/-! ## Positive evidence: singletons and bijectivity -/

/-- When e > 0, the induced posterior set equals the image of the feasible
    sub-class {j ∈ S | j ≤ e} under the map j ↦ the unique conditional j/e. -/
theorem condSet_positive_evidence (S : Set Credence) (e : Credence) (he : 0 < e.val) :
    condSet S e =
      (fun j : {j : Credence // j ∈ S ∧ j.val ≤ e.val} =>
        (conditioning_mk j.val e he j.property.2).condCred) ''
      Set.univ := by
  ext c
  simp only [condSet, Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨j, hjS, hjc⟩
    have hle : j.val ≤ e.val := conditioning_implies_joint_le_evidence j e ⟨c, hjc⟩
    refine ⟨⟨j, hjS, hle⟩, ?_⟩
    have hsingleton := cond_singleton_of_pos j e he hle
    have hmem : c ∈ Cond j e := hjc
    rw [hsingleton] at hmem
    exact (Set.mem_singleton_iff.mp hmem).symm
  · rintro ⟨⟨j, hjS, hle⟩, rfl⟩
    exact ⟨j, hjS, (conditioning_mk j e he hle).chainRule⟩

/-! ## Maximality characterisation -/

/-- The induced posterior set is all of [0,1] if and only if either:
      (a) e = 0 and 0 ∈ S, or
      (b) every credence c is the image j/e of some feasible j ∈ S.
    The clean half is the zero-evidence direction. -/
theorem condSet_univ_of_zero_evidence (S : Set Credence) (e : Credence)
    (he : e = 0) (h0 : (0 : Credence) ∈ S) : condSet S e = Set.univ := by
  subst he
  exact condSet_zero_evidence_of_zero_mem S h0

/-- If e > 0 and the induced set is univ, then for every credence c there
    exists j ∈ S with j ≤ e and j/e = c. -/
theorem condSet_univ_implies_surjective (S : Set Credence) (e : Credence)
    (he : 0 < e.val) (huniv : condSet S e = Set.univ) :
    ∀ c : Credence, ∃ j ∈ S, j.val ≤ e.val ∧ j.val / e.val = c.val := by
  intro c
  have hc : c ∈ condSet S e := huniv ▸ Set.mem_univ c
  simp only [condSet, Set.mem_iUnion] at hc
  obtain ⟨j, hjS, hjc⟩ := hc
  have hle : j.val ≤ e.val := conditioning_implies_joint_le_evidence j e ⟨c, hjc⟩
  refine ⟨j, hjS, hle, ?_⟩
  simp only [Cond, Set.mem_setOf_eq] at hjc
  have hval : c.val * e.val = j.val := by
    have := congrArg val hjc; simp only [conj_val] at this; exact this
  rw [div_eq_iff (ne_of_gt he)]
  linarith

/-! ## Improper-prior pathology (formal face)

    When the joint class is the full feasible set {j | j ≤ e}, the induced
    posterior set is exactly [0,1] for e > 0 (every posterior is realised)
    and trivially [0,1] for e = 0.  This is the formal correlate of Lindley's
    remark: an improper prior that assigns zero mass to the conditioning event
    leaves the posterior wholly unconstrained. -/

/-- With the full feasible joint class {j | j ≤ e} and e > 0, every posterior
    in [0,1] is realised. -/
theorem condSet_full_feasible_eq_univ (e : Credence) (_he : 0 < e.val) :
    condSet {j | j.val ≤ e.val} e = Set.univ := by
  apply Set.eq_univ_of_forall
  intro c
  simp only [condSet, Set.mem_iUnion, Set.mem_setOf_eq]
  -- Take j = c ⊗ e; then c ∈ Cond j e by definition, and j ≤ e.
  refine ⟨c ⊗ e, ?_, ?_⟩
  · simp only [conj_val]
    calc c.val * e.val ≤ 1 * e.val :=
          mul_le_mul_of_nonneg_right c.le_one e.nonneg
      _ = e.val := one_mul _
  · exact rfl

end Credence

end Cred
