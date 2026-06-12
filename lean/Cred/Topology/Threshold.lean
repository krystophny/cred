/-
  Cred Topology: Threshold (alpha-cut) Topology

  A graded set assigns each point a credence; fixing a threshold t turns it into
  an ordinary crisp set, the t-cut (alpha-cut) {x | t ≤ mem x}. Raising t can
  only shrink the cut, so a single graded set yields an antitone family of crisp
  sets indexed by threshold (issue #606). This is the bridge from CredSet back to
  ordinary set theory and topology.

  Threshold openness/closedness (issue #605) reads off two degree functions
  (OpenDegree, ClosedDegree) at a threshold: A is t-open when t ≤ OpenDegree A,
  t-closed when t ≤ ClosedDegree A, t-clopen when both. The new phenomenon is
  that clopen status is threshold-dependent: A can be clopen at one t and fail
  at a higher one. A concrete finite example tabulates this.

  For graded real neighborhoods we take the tent profile μ(x) = max(0, 1 - |x|),
  a graded neighborhood of 0, and show its alpha-cuts are closed intervals; for
  the sample t = 1/2 the cut is exactly Set.Icc (-(1/2)) (1/2). This reuses
  mathlib's classical topology (IsClosed, Set.Icc) rather than reinventing it.
-/

import Cred.Set.Classical
import Cred.Threshold
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

namespace Cred

namespace Topology

open Credence CredSet

variable {U : Type*}

/-! ## Alpha-Cuts of a Graded Set

The t-cut of a graded set `s` is the classical set of points whose membership
credence reaches the threshold `t`. We expose it both as a `Set U` (`cut`) and,
through `ofPred`, as a crisp `CredSet U` (`tcut`). -/

/-- The t-cut (alpha-cut) of a graded set as an ordinary set: points whose
    membership credence is at least `t`. -/
def cut (t : Credence) (s : CredSet U) : Set U := {x | t ≤ s.mem x}

@[simp] theorem mem_cut (t : Credence) (s : CredSet U) (x : U) :
    x ∈ cut t s ↔ t ≤ s.mem x := Iff.rfl

/-- The t-cut as a crisp graded set: membership 1 on the cut, 0 off it. -/
noncomputable def tcut (t : Credence) (s : CredSet U) : CredSet U :=
  ofPred (cut t s)

/-- The t-cut graded set is crisp. -/
theorem tcut_crisp (t : Credence) (s : CredSet U) : Crisp (tcut t s) :=
  ofPred_crisp _

/-- The crisp t-cut recovers exactly the set-level cut. -/
theorem toPred_tcut (t : Credence) (s : CredSet U) :
    toPred (tcut t s) = cut t s :=
  toPred_ofPred _

/-- Graded membership in the crisp t-cut is reaching the threshold. -/
theorem tcut_mem_one_iff (t : Credence) (s : CredSet U) (x : U) :
    (tcut t s).mem x = 1 ↔ t ≤ s.mem x :=
  ofPred_mem_eq_one_iff _ x

/-! ## Monotonicity in the Threshold

Raising the threshold can only shrink the cut: the family is antitone in `t`.
At the extremes the 0-cut is everything and (for membership bounded by 1) the
1-cut collects exactly the certain points. -/

/-- Antitone in the threshold: a higher threshold yields a smaller cut. -/
theorem cut_antitone (s : CredSet U) {t₁ t₂ : Credence} (h : t₁ ≤ t₂) :
    cut t₂ s ⊆ cut t₁ s :=
  fun _ hx => le_trans h hx

/-- The crisp cuts are nested by the pointwise subset order: higher threshold,
    smaller crisp set. -/
theorem tcut_subset (s : CredSet U) {t₁ t₂ : Credence} (h : t₁ ≤ t₂) :
    tcut t₂ s ⊆ tcut t₁ s := by
  rw [crisp_subset_iff (tcut_crisp _ _) (tcut_crisp _ _)]
  intro x hx
  rw [toPred_def] at hx ⊢
  rw [tcut_mem_one_iff] at hx ⊢
  exact le_trans h hx

/-- The 0-cut is the whole space: every credence reaches threshold 0. -/
@[simp] theorem cut_zero (s : CredSet U) : cut 0 s = Set.univ := by
  ext x
  simp [mem_cut, zero_le]

/-- The 1-cut collects exactly the points of certain membership. -/
theorem cut_one (s : CredSet U) : cut 1 s = {x | s.mem x = 1} := by
  ext x
  simp only [mem_cut, Set.mem_setOf_eq]
  exact ⟨fun h => le_antisymm (le_one' _) h, fun h => h ▸ le_refl _⟩

/-! ## Threshold Openness, Closedness, Clopenness (issue #605)

A graded topological status is given by two degree functions on a graded space:
how open and how closed each set is. Thresholding each degree gives crisp
open/closed/clopen predicates parameterised by `t`. -/

/-- `A` is t-open when its openness degree reaches the threshold. -/
def IsOpenAt (t openDeg : Credence) : Prop := t ≤ openDeg

/-- `A` is t-closed when its closedness degree reaches the threshold. -/
def IsClosedAt (t closedDeg : Credence) : Prop := t ≤ closedDeg

/-- `A` is t-clopen when it is both t-open and t-closed. -/
def IsClopenAt (t openDeg closedDeg : Credence) : Prop :=
  IsOpenAt t openDeg ∧ IsClosedAt t closedDeg

/-- Threshold conjunction (both degrees clear `t`) is implied by the product
    degree clearing `t`: a t-clopen verdict via the product is at least as
    strong. Threshold conjunction and product-degree conjunction differ; the
    product is the stricter test. -/
theorem clopen_of_product_threshold {t openDeg closedDeg : Credence}
    (h : t ≤ openDeg ⊗ closedDeg) : IsClopenAt t openDeg closedDeg := by
  refine ⟨le_trans h ?_, le_trans h ?_⟩
  · -- openDeg ⊗ closedDeg ≤ openDeg
    rw [le_def, conj_val]
    nlinarith [openDeg.nonneg, closedDeg.le_one]
  · rw [le_def, conj_val]
    nlinarith [closedDeg.nonneg, openDeg.le_one]

/-- Clopen status is antitone in the threshold: a clopen verdict at `t₂`
    survives lowering to any `t₁ ≤ t₂`. -/
theorem clopen_antitone {t₁ t₂ openDeg closedDeg : Credence} (h : t₁ ≤ t₂)
    (hc : IsClopenAt t₂ openDeg closedDeg) : IsClopenAt t₁ openDeg closedDeg :=
  ⟨le_trans h hc.1, le_trans h hc.2⟩

/-! ## Concrete Finite Example: Threshold-Dependent Clopenness

A single set `A` with `OpenDegree A = 0.8` and `ClosedDegree A = 0.7` (issue
#605). The status table over thresholds:

| t    | t-open | t-closed | t-clopen |
|------|--------|----------|----------|
| 0.5  | yes    | yes      | yes      |
| 0.75 | yes    | no       | no       |
| 0.9  | no     | no       | no       |

Clopenness is genuinely threshold-relative: true at 0.5, false at 0.75. -/

/-- Openness degree 0.8 of the example set. -/
noncomputable def exOpen : Credence := ⟨(4 : ℝ) / 5, by norm_num, by norm_num⟩

/-- Closedness degree 0.7 of the example set. -/
noncomputable def exClosed : Credence := ⟨(7 : ℝ) / 10, by norm_num, by norm_num⟩

/-- Threshold 0.5. -/
noncomputable def t50 : Credence := ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩
/-- Threshold 0.75. -/
noncomputable def t75 : Credence := ⟨(3 : ℝ) / 4, by norm_num, by norm_num⟩
/-- Threshold 0.9. -/
noncomputable def t90 : Credence := ⟨(9 : ℝ) / 10, by norm_num, by norm_num⟩

theorem ex_clopen_at_50 : IsClopenAt t50 exOpen exClosed := by
  refine ⟨?_, ?_⟩
  · rw [IsOpenAt, le_def]; norm_num [t50, exOpen]
  · rw [IsClosedAt, le_def]; norm_num [t50, exClosed]

theorem ex_open_at_75 : IsOpenAt t75 exOpen := by
  rw [IsOpenAt, le_def]; norm_num [t75, exOpen]

theorem ex_not_closed_at_75 : ¬ IsClosedAt t75 exClosed := by
  rw [IsClosedAt, le_def]; norm_num [t75, exClosed]

/-- At 0.75 the set is open but not clopen: clopenness has been lost by raising
    the threshold from 0.5. -/
theorem ex_not_clopen_at_75 : ¬ IsClopenAt t75 exOpen exClosed :=
  fun h => ex_not_closed_at_75 h.2

theorem ex_not_open_at_90 : ¬ IsOpenAt t90 exOpen := by
  rw [IsOpenAt, le_def]; norm_num [t90, exOpen]

theorem ex_not_clopen_at_90 : ¬ IsClopenAt t90 exOpen exClosed :=
  fun h => ex_not_open_at_90 h.1

/-! ## Connection to Threshold Consequence

The cut threshold `t` is the same designation parameter as in
`thresholdConsequence`: a formula's value clearing `t` under a valuation is
membership in the t-cut of its valuation-indexed graded set. Concretely, the
t-cut of the graded set "value of formula `φ`" is the set of valuations that
designate `φ` at threshold `t`, and threshold consequence is exactly inclusion
of cuts pulled back along the premises. -/

/-- The graded set on valuations whose membership at `v` is `evalCred v φ`. -/
noncomputable def evalSet (α : Type*) (φ : Formula α) : CredSet (α → Credence) :=
  ⟨fun v => evalCred v φ⟩

/-- A valuation lies in the t-cut of `evalSet φ` exactly when it designates `φ`
    at threshold `t`. -/
theorem mem_cut_evalSet (t : Credence) (φ : Formula α) (v : α → Credence) :
    v ∈ cut t (evalSet α φ) ↔ t ≤ evalCred v φ := Iff.rfl

/-- Threshold consequence is cut inclusion: every valuation in all premise cuts
    lies in the conclusion cut. -/
theorem thresholdConsequence_iff_cut (t : Credence)
    (premises : List (Formula α)) (conclusion : Formula α) :
    thresholdConsequence t α premises conclusion ↔
    ∀ v, (∀ φ ∈ premises, v ∈ cut t (evalSet α φ)) →
      v ∈ cut t (evalSet α conclusion) :=
  Iff.rfl

/-! ## Graded Real Neighborhoods (issue #606)

The tent profile `μ(x) = max(0, 1 - |x|)` is a graded neighborhood of `0` on the
real line: certain at `0`, fading to impossible at distance `1`. Its alpha-cuts
are closed intervals centred at `0`, shrinking as the threshold rises. We give
the cut shape for any threshold and pin the sample `t = 1/2` cut to the concrete
interval `Set.Icc (-(1/2)) (1/2)`, which mathlib certifies as closed. -/

/-- The tent membership value `max(0, 1 - |x|)` as a credence. -/
noncomputable def tentVal (x : ℝ) : Credence where
  val := max 0 (1 - |x|)
  nonneg := le_max_left _ _
  le_one := by
    rcases le_total (1 - |x|) 0 with h | h
    · rw [max_eq_left h]; exact zero_le_one
    · rw [max_eq_right h]; nlinarith [abs_nonneg x]

@[simp] theorem tentVal_val (x : ℝ) : (tentVal x).val = max 0 (1 - |x|) := rfl

/-- The tent graded neighborhood of `0` on `ℝ`. -/
noncomputable def tent : CredSet ℝ := ⟨tentVal⟩

@[simp] theorem tent_mem (x : ℝ) : tent.mem x = tentVal x := rfl

/-- For a positive threshold `t`, the tent alpha-cut is the symmetric closed
    interval of radius `1 - t`: an interval, as a graded neighborhood should
    have. -/
theorem cut_tent_eq_Icc {t : Credence} (ht : 0 < t.val) :
    cut t tent = Set.Icc (-(1 - t.val)) (1 - t.val) := by
  ext x
  simp only [mem_cut, tent_mem, le_def, tentVal_val, Set.mem_Icc]
  constructor
  · intro h
    have hpos : t.val ≤ 1 - |x| := by
      rcases le_or_lt (1 - |x|) 0 with hle | hlt
      · rw [max_eq_left hle] at h; linarith
      · rwa [max_eq_right hlt.le] at h
    have habs : |x| ≤ 1 - t.val := by linarith
    rw [abs_le] at habs
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  · intro ⟨h1, h2⟩
    have habs : |x| ≤ 1 - t.val := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have : t.val ≤ 1 - |x| := by linarith
    exact le_trans this (le_max_right _ _)

/-- Concrete sample: the `t = 1/2` tent cut is exactly `Set.Icc (-(1/2)) (1/2)`. -/
theorem cut_tent_half :
    cut half tent = Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  rw [cut_tent_eq_Icc (t := half) (by rw [half_val]; norm_num)]
  norm_num [half_val]

/-- That sample cut is closed in the usual topology on `ℝ` (mathlib). -/
theorem isClosed_cut_tent_half : IsClosed (cut half tent) := by
  rw [cut_tent_half]; exact isClosed_Icc

/-- The full-space degenerate case: the `0`-cut of the tent is all of `ℝ`. -/
theorem cut_tent_zero : cut 0 tent = Set.univ := cut_zero tent

end Topology

end Cred
