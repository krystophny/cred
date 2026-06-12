/-
  Cred Topology: Graded Openness and Closedness

  Over a CredSet, openness and closedness are credence-valued statuses rather
  than Boolean predicates.  The openness degree of a set s is the infimum of
  its membership function: 1 means every point is a full member; 0 means some
  point has zero membership.  Closedness is the openness of the complement,
  i.e., the infimum of non-membership.

  Duality: closednessDegree ≤ ~(opennessDegree) in general (inf(1-f) ≤ 1-inf f
  because 1-inf f is an upper bound on 1-f(x)).  On the extremes (univ and
  emptyset) equality holds.  On crisp sets both degrees are 0 or 1.

  Key results:
  - `closednessDegree_le_neg` : closedness ≤ ~openness (general duality inequality).
  - `univ_openness_one`, `univ_closedness_zero` : boundary values.
  - `emptyset_openness_zero`, `emptyset_closedness_one` : boundary values.
  - `openness_monotone` : s ⊆ t → opennessDegree s ≤ opennessDegree t.
  - `closedness_antitone` : s ⊆ t → closednessDegree t ≤ closednessDegree s.
  - `inter_openness_ge_conj` : openness of intersection dominates the product.
  - `openness_compl_compl` : double complement restores the degree.
  - `crisp_openness_zero_or_one` : crisp sets have degree 0 or 1.
  - `crisp_closedness_zero_or_one` : same for closedness.
  - `crisp_openness_zero_iff` : degree 0 ↔ some element has zero membership.
  - `crisp_openness_one_iff_univ` : degree 1 ↔ s = univ.
-/

import Cred.Set.Classical
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace Cred

open Credence CredSet

variable {U : Type*}

/-! ## Bounded-range helpers -/

private theorem bddBelow_mem (s : CredSet U) :
    BddBelow (Set.range (fun x => (s.mem x).val)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact (s.mem x).nonneg⟩

/-! ## Definitions -/

/-- The openness degree of a CredSet: the infimum of membership over all points.
    1 = every point is a full member; 0 = some point has zero membership. -/
noncomputable def opennessDegree [Nonempty U] (s : CredSet U) : Credence where
  val := iInf (fun x => (s.mem x).val)
  nonneg := le_ciInf (fun x => (s.mem x).nonneg)
  le_one := ciInf_le_of_le (bddBelow_mem s) (Classical.arbitrary U)
              (s.mem (Classical.arbitrary U)).le_one

/-- The closedness degree of a CredSet: the openness degree of its complement,
    i.e., the infimum of non-membership values. -/
noncomputable def closednessDegree [Nonempty U] (s : CredSet U) : Credence :=
  opennessDegree (compl s)

/-! ## Basic lemmas -/

@[simp]
theorem opennessDegree_val [Nonempty U] (s : CredSet U) :
    (opennessDegree s).val = iInf (fun x => (s.mem x).val) := rfl

theorem closednessDegree_val [Nonempty U] (s : CredSet U) :
    (closednessDegree s).val = iInf (fun x => (1 - (s.mem x).val)) := by
  simp only [closednessDegree, opennessDegree_val, compl_mem, neg_val]

theorem closednessDegree_eq_openness_compl [Nonempty U] (s : CredSet U) :
    closednessDegree s = opennessDegree (compl s) := rfl

/-! ## Duality Inequality -/

/-- General duality: closedness degree ≤ negation of openness degree.
    Since inf(f) ≤ f(x), we have 1-f(x) ≤ 1-inf(f) for all x, so 1-inf(f)
    is an upper bound for 1-f(x), hence inf(1-f) ≤ 1-inf(f). -/
theorem closednessDegree_le_neg [Nonempty U] (s : CredSet U) :
    closednessDegree s ≤ ~(opennessDegree s) := by
  rw [le_def, closednessDegree_val, neg_val, opennessDegree_val]
  have hbdd : BddBelow (Set.range (fun x => 1 - (s.mem x).val)) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; simp only; linarith [(s.mem x).le_one]⟩
  refine ciInf_le_of_le hbdd (Classical.arbitrary U) ?_
  linarith [ciInf_le (bddBelow_mem s) (Classical.arbitrary U)]

/-- Double complement restores the openness degree. -/
theorem openness_compl_compl [Nonempty U] (s : CredSet U) :
    opennessDegree (compl (compl s)) = opennessDegree s := by
  ext
  simp only [opennessDegree_val, compl_mem, neg_neg]

/-! ## Boundary Values -/

/-- The universal set has openness degree 1. -/
theorem univ_openness_one [Nonempty U] :
    opennessDegree (univ : CredSet U) = 1 := by
  ext
  simp only [opennessDegree_val, univ_mem, one_val]
  exact le_antisymm
    (ciInf_le_of_le (bddBelow_mem univ) (Classical.arbitrary U) (le_refl _))
    (le_ciInf (fun _ => le_refl _))

/-- The empty set has openness degree 0. -/
theorem emptyset_openness_zero [Nonempty U] :
    opennessDegree (emptyset : CredSet U) = 0 := by
  ext
  simp only [opennessDegree_val, emptyset_mem, zero_val]
  exact le_antisymm
    (ciInf_le_of_le (bddBelow_mem emptyset) (Classical.arbitrary U) (le_refl _))
    (le_ciInf (fun _ => le_refl _))

private theorem compl_univ_eq_emptyset :
    compl (univ : CredSet U) = emptyset :=
  ext_mem (fun x => by simp [compl_mem, univ_mem, emptyset_mem, neg_one])

private theorem compl_emptyset_eq_univ :
    compl (emptyset : CredSet U) = univ :=
  ext_mem (fun x => by simp [compl_mem, univ_mem, emptyset_mem, neg_zero])

/-- The universal set has closedness degree 0. -/
theorem univ_closedness_zero [Nonempty U] :
    closednessDegree (univ : CredSet U) = 0 := by
  simp only [closednessDegree_eq_openness_compl, compl_univ_eq_emptyset, emptyset_openness_zero]

/-- The empty set has closedness degree 1. -/
theorem emptyset_closedness_one [Nonempty U] :
    closednessDegree (emptyset : CredSet U) = 1 := by
  simp only [closednessDegree_eq_openness_compl, compl_emptyset_eq_univ, univ_openness_one]

/-! ## Monotonicity -/

/-- Subset implies openness degree is no larger: s ⊆ t → opennessDegree s ≤ opennessDegree t. -/
theorem openness_monotone [Nonempty U] {s t : CredSet U} (h : s ⊆ t) :
    opennessDegree s ≤ opennessDegree t := by
  rw [le_def, opennessDegree_val, opennessDegree_val]
  apply le_ciInf
  intro x
  exact le_trans (ciInf_le (bddBelow_mem s) x) (h x)

/-- Closedness degree is antitone: if s ⊆ t then closednessDegree t ≤ closednessDegree s. -/
theorem closedness_antitone [Nonempty U] {s t : CredSet U} (h : s ⊆ t) :
    closednessDegree t ≤ closednessDegree s := by
  simp only [closednessDegree_eq_openness_compl]
  apply openness_monotone
  -- compl t ⊆ compl s because negation reverses the credence order
  intro x
  simp only [compl_mem, le_def, neg_val]
  have := h x
  rw [le_def] at this
  linarith [this]

/-! ## Intersection -/

/-- The openness degree of an intersection is at least the product of the degrees:
    openness s ⊗ openness t ≤ openness (s ∩ t). -/
theorem inter_openness_ge_conj [Nonempty U] (s t : CredSet U) :
    opennessDegree s ⊗ opennessDegree t ≤ opennessDegree (inter s t) := by
  rw [le_def, conj_val, opennessDegree_val, opennessDegree_val, opennessDegree_val]
  simp only [inter_mem]
  apply le_ciInf
  intro x
  simp only [conj_val]
  apply mul_le_mul
  · exact ciInf_le (bddBelow_mem s) x
  · exact ciInf_le (bddBelow_mem t) x
  · exact le_ciInf (fun y => (t.mem y).nonneg)
  · exact (s.mem x).nonneg

/-! ## Crisp Recovery -/

/-- On a crisp set, the openness degree is 0 or 1: the classical dichotomy recovers. -/
theorem crisp_openness_zero_or_one [Nonempty U] {s : CredSet U} (hs : Crisp s) :
    opennessDegree s = 0 ∨ opennessDegree s = 1 := by
  by_cases h : ∃ x : U, s.mem x = 0
  · left
    ext
    simp only [opennessDegree_val, zero_val]
    obtain ⟨x, hx⟩ := h
    exact le_antisymm
      (ciInf_le_of_le (bddBelow_mem s) x (by rw [hx]; simp))
      (le_ciInf (fun y => (s.mem y).nonneg))
  · right
    push_neg at h
    have hall : ∀ x : U, s.mem x = 1 := fun x => (hs x).resolve_left (h x)
    ext
    simp only [opennessDegree_val, one_val]
    exact le_antisymm
      (ciInf_le_of_le (bddBelow_mem s) (Classical.arbitrary U) (by rw [hall]; simp))
      (le_ciInf (fun x => by rw [hall x]; simp))

/-- On a crisp set, the closedness degree is 0 or 1. -/
theorem crisp_closedness_zero_or_one [Nonempty U] {s : CredSet U} (hs : Crisp s) :
    closednessDegree s = 0 ∨ closednessDegree s = 1 := by
  simp only [closednessDegree_eq_openness_compl]
  exact crisp_openness_zero_or_one (compl_crisp hs)

/-- On a crisp set, opennessDegree = 0 iff some element has zero membership. -/
theorem crisp_openness_zero_iff [Nonempty U] {s : CredSet U} (hs : Crisp s) :
    opennessDegree s = 0 ↔ ∃ x : U, s.mem x = 0 := by
  constructor
  · intro heq
    by_contra hall
    push_neg at hall
    -- all memberships are 1 (by crispness and no zeros)
    have hone : ∀ x : U, s.mem x = 1 := fun x => (hs x).resolve_left (hall x)
    -- the infimum of all-1 is 1, contradicting heq = 0
    have hinf : iInf (fun x => (s.mem x).val) = 1 :=
      le_antisymm (ciInf_le_of_le (bddBelow_mem s) (Classical.arbitrary U) (by rw [hone]; simp))
                  (le_ciInf (fun x => by rw [hone x]; simp))
    have h0 : (opennessDegree s).val = 0 := by
      have := congrArg Credence.val heq; simpa [opennessDegree_val, zero_val] using this
    have h1 : (opennessDegree s).val = 1 := by simpa [opennessDegree_val] using hinf
    linarith
  · intro ⟨x, hx⟩
    ext
    simp only [opennessDegree_val, zero_val]
    exact le_antisymm
      (ciInf_le_of_le (bddBelow_mem s) x (by rw [hx]; simp))
      (le_ciInf (fun _ => (s.mem _).nonneg))

/-- On a crisp set, opennessDegree = 1 iff s = univ. -/
theorem crisp_openness_one_iff_univ [Nonempty U] {s : CredSet U} (hs : Crisp s) :
    opennessDegree s = 1 ↔ s = univ := by
  constructor
  · intro heq
    have hinf : iInf (fun x => (s.mem x).val) = 1 := by
      have := congrArg Credence.val heq; simpa [opennessDegree_val] using this
    apply ext_mem; intro x
    have hge : 1 ≤ (s.mem x).val := hinf ▸ ciInf_le (bddBelow_mem s) x
    have hmem : (s.mem x).val = 1 := le_antisymm (s.mem x).le_one hge
    have hc : s.mem x = 1 := Credence.ext hmem
    simp [univ_mem, hc]
  · intro heq; subst heq; exact univ_openness_one

end Cred
