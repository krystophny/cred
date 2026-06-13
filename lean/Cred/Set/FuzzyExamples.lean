/-
  Cred Set: Paper-Facing Graded and Fuzzy-Set Examples

  Worked examples of graded membership where every numeric degree comes from a
  NAMED source, never an arbitrary fuzzy label (governing rule #680). Here the
  source is a membership function built from a crisp embedding: a finite set
  `A : Finset (Fin n)` gives the membership function `muCrisp A x = if x ∈ A
  then 1 else 0`. Its values are exactly {0,1} and it recovers `A` on the nose
  (`fuzzy_membership_crisp_recovery`).

  A threshold cut of a CredSet at a level `t` is the classical set of points
  whose membership reaches `t`. The cut of a crisp membership is the underlying
  classical set, independent of the (positive) threshold (`threshold_cut_crisp`).

  Finally we reuse `crisp_fuzzyOpen_iff` (Cred.Topology.Fuzzy) to read a crisp
  membership function as a fuzzy-open set whose support is the classical set.
-/

import Cred.Set.Basic
import Cred.Topology.Fuzzy

namespace Cred

namespace CredSet

open Credence

/-! ## Crisp Membership Functions over `Fin n`

A finite set `A : Finset (Fin n)` defines a membership function by its crisp
indicator. The degree at `x` is 1 (member) or 0 (non-member): a value sourced
entirely from the crisp embedding of the decidable predicate `x ∈ A`. -/

variable {n : ℕ}

/-- The crisp membership function of a finite set: members get 1, others get 0. -/
def muCrisp (A : Finset (Fin n)) : CredSet (Fin n) :=
  ⟨fun x => if x ∈ A then 1 else 0⟩

@[simp] theorem muCrisp_mem (A : Finset (Fin n)) (x : Fin n) :
    (muCrisp A).mem x = if x ∈ A then 1 else 0 := rfl

/-- The crisp membership function takes only the values 0 and 1. -/
theorem muCrisp_crisp (A : Finset (Fin n)) : Crisp (muCrisp A) := by
  intro x
  simp only [muCrisp_mem]
  by_cases hx : x ∈ A
  · exact Or.inr (by simp [hx])
  · exact Or.inl (by simp [hx])

/-- CRISP RECOVERY: the membership degree is 1 exactly on members, and the
    degree is always one of the two crisp values {0,1}. The classical set is
    read back off the membership function with no information loss. -/
theorem fuzzy_membership_crisp_recovery (A : Finset (Fin n)) (x : Fin n) :
    ((muCrisp A).mem x = 1 ↔ x ∈ A) ∧
      ((muCrisp A).mem x = 0 ∨ (muCrisp A).mem x = 1) := by
  refine ⟨?_, muCrisp_crisp A x⟩
  simp only [muCrisp_mem]
  by_cases hx : x ∈ A
  · simp [hx]
  · simp only [hx, if_false, iff_false]
    exact fun h => absurd h credence_zero_ne_one

/-! ## Threshold Cuts

The `t`-cut of a graded set is the classical set of points whose membership
degree reaches the level `t`. This is the standard alpha-cut of fuzzy-set
theory, here a genuine `Set (Fin n)` rather than a graded object. -/

/-- The `t`-cut: points whose membership degree is at least `t`. -/
def thresholdCut (s : CredSet (Fin n)) (t : Credence) : Set (Fin n) :=
  {x | t ≤ s.mem x}

@[simp] theorem mem_thresholdCut (s : CredSet (Fin n)) (t : Credence) (x : Fin n) :
    x ∈ thresholdCut s t ↔ t ≤ s.mem x := Iff.rfl

/-- CRISP RECOVERY for cuts: at any positive threshold `t` (with `0 < t ≤ 1`),
    the cut of a crisp membership function is exactly the underlying classical
    set. The threshold collapses to the two-valued membership question. -/
theorem threshold_cut_crisp (A : Finset (Fin n)) {t : Credence}
    (ht0 : (0 : Credence) < t) (ht1 : t ≤ 1) :
    thresholdCut (muCrisp A) t = {x | x ∈ A} := by
  ext x
  simp only [mem_thresholdCut, muCrisp_mem, Set.mem_setOf_eq, le_def]
  by_cases hx : x ∈ A
  · simp only [hx, if_true, iff_true, one_val]; exact (le_def t 1).mp ht1
  · simp only [hx, if_false, iff_false, zero_val]
    intro h
    rw [lt_def, zero_val] at ht0; linarith

/-! ## A Small Graded Example with Its Cut

Not every membership function is crisp. The next set takes the genuinely graded
value `half` at one point; its degree there is sourced from the named credence
`half` (the liar fixed point of `Cred.Core.Value`), not an arbitrary label.
Its `t`-cut still recovers a classical set, and at a high threshold the graded
point drops out. -/

/-- A graded membership over `Fin 3`: full at `0`, half at `1`, empty at `2`. -/
noncomputable def gradedExample : CredSet (Fin 3) :=
  ⟨fun i => if i = 0 then 1 else if i = 1 then half else 0⟩

@[simp] theorem gradedExample_mem (i : Fin 3) :
    gradedExample.mem i = if i = 0 then 1 else if i = 1 then half else 0 := rfl

/-- The graded example is NOT crisp: its value at `1` is `half`, which is
    neither `0` nor `1`. The witness pins the failure of crispness. -/
theorem gradedExample_not_crisp : ¬ Crisp gradedExample := by
  intro hc
  have h1 : gradedExample.mem (1 : Fin 3) = half := by simp
  rcases hc 1 with h | h
  · rw [h1] at h
    have := congrArg Credence.val h
    simp only [half_val, zero_val] at this; norm_num at this
  · rw [h1] at h
    have := congrArg Credence.val h
    simp only [half_val, one_val] at this; norm_num at this

/-- The `1`-cut (certainty cut) of the graded example is the single point `0`:
    only the full-membership point survives the highest threshold. -/
theorem gradedExample_one_cut :
    thresholdCut gradedExample 1 = {(0 : Fin 3)} := by
  ext i
  simp only [mem_thresholdCut, gradedExample_mem, Set.mem_singleton_iff, le_def]
  fin_cases i
  · simp
  · rw [if_neg (by decide), if_pos (by decide)]
    simp only [half_val, one_val]
    constructor
    · intro h; norm_num at h
    · intro h; exact absurd h (by decide)
  · rw [if_neg (by decide), if_neg (by decide)]
    simp only [zero_val, one_val]
    constructor
    · intro h; norm_num at h
    · intro h; exact absurd h (by decide)

/-! ## Topology: a Crisp Membership Function as a Fuzzy-Open Set

Reusing `crisp_fuzzyOpen_iff`: over the discrete topology on `Fin n` every crisp
membership function is fuzzy-open, since its support is automatically open. The
fuzzy-open degree question collapses to classical openness of the underlying
set. -/

/-- The support of a crisp membership function is its underlying classical set. -/
theorem muCrisp_support (A : Finset (Fin n)) :
    support (muCrisp A) = {x | x ∈ A} := by
  ext x
  simp only [mem_support, muCrisp_mem, Set.mem_setOf_eq]
  by_cases hx : x ∈ A
  · simp [hx]
  · simp only [hx, if_false, iff_false]
    exact fun h => absurd h credence_zero_ne_one

/-- A crisp membership function over the discrete topology is fuzzy-open: its
    support is open, and `crisp_fuzzyOpen_iff` transports that to fuzzy-openness. -/
theorem muCrisp_fuzzyOpen [TopologicalSpace (Fin n)] [DiscreteTopology (Fin n)]
    (A : Finset (Fin n)) : FuzzyOpen (muCrisp A) := by
  rw [crisp_fuzzyOpen_iff (muCrisp_crisp A)]
  exact isOpen_discrete _

end CredSet

end Cred
