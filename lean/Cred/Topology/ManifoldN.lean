/-
  Cred Topology: Graded n-Dimensional Manifold Layer

  This layer upgrades the one-dimensional seed in `Cred/Topology/Manifold.lean`
  to a genuine n-dimensional recovery of Mathlib's smooth-manifold notion. The
  model space is `E := EuclideanSpace ℝ (Fin n)` for an arbitrary `n`, with the
  boundaryless model-with-corners `I := 𝓘(ℝ, E)`. We work over an abstract space
  `M` that already carries a `ChartedSpace E M`, so `M` has charts into the
  n-dimensional model. Nothing is fixed to one dimension here.

  WHAT IS GRADED vs THE CRISP RECOVERY.
  The graded datum is a per-transition smoothness STATUS credence: for a pair of
  charts `e e'` of `M`, the transition `e.symm ≫ₕ e'` carries status `1` exactly
  when it lies in `contDiffGroupoid ∞ I` (Mathlib's `ContDiffOn` compatibility
  condition), `0` otherwise. The atlas-level status `atlasSmoothStatus` is `1`
  exactly when EVERY ordered pair of atlas charts has transition status `1`.

  THE HEADLINE RECOVERY. `atlasSmoothStatus_eq_one_iff_isManifold` proves
      atlasSmoothStatus = 1  ↔  IsManifold I (∞ : WithTop ℕ∞) M,
  i.e. the graded atlas status reaches certainty exactly when `M` is a genuine
  Mathlib smooth (`C^∞`, the `∞ : WithTop ℕ∞` order) manifold. Both directions
  are proved from the groupoid membership API: status `1` unpacks to the
  `HasGroupoid.compatible` field and back. `IsManifold I ∞ M` is definitionally
  `HasGroupoid M (contDiffGroupoid ∞ I)`, so this is a faithful recovery, not a
  triviality.

  The smoothness order is `∞ : WithTop ℕ∞` (C^∞) throughout, matching the order
  type of `contDiffGroupoid` and `IsManifold`. In this Mathlib version the order
  scale is `WithTop ℕ∞` with `⊤ = ω` (analytic) above `∞ = C^∞`; we use `∞`, the
  standard smooth-manifold order. This layer adds the n-dimensional chart-overlap
  recovery; it still has NO tangent bundle, no differential forms, no de Rham
  theory — those are future cuts.
-/

import Cred.Core.Value
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Cred

namespace ManifoldN

open Credence
open Classical
open scoped Manifold ContDiff

/-! ## The n-dimensional model

We fix the Euclidean model space and its boundaryless model-with-corners. -/

/-- The n-dimensional Euclidean model space. -/
abbrev ModelSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The boundaryless model-with-corners on the n-dimensional Euclidean space. -/
abbrev model (n : ℕ) : ModelWithCorners ℝ (ModelSpace n) (ModelSpace n) :=
  𝓘(ℝ, ModelSpace n)

/-! ## Per-transition smoothness status

For a pair of partial homeomorphisms `e e' : M → ModelSpace n`, the transition is
`e.symm ≫ₕ e'`. Its smoothness status is the credence `1` when the transition
lies in `contDiffGroupoid ∞ (model n)`, else `0`. The order literal `∞` is the
C^∞ order, matching `contDiffGroupoid` and `IsManifold`. -/

section Transition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]

/-- Smoothness STATUS of a transition between two partial homeomorphisms of `M`
into the n-dimensional model, as a credence: `1` when `e.symm ≫ₕ e'` is in
`contDiffGroupoid ∞ (model n)`, `0` otherwise. -/
noncomputable def transitionStatus
    (e e' : PartialHomeomorph M (ModelSpace n)) : Credence :=
  if (e.symm ≫ₕ e') ∈ contDiffGroupoid (∞ : WithTop ℕ∞) (model n) then 1 else 0

omit [ChartedSpace (ModelSpace n) M] in
/-- Crisp reduction: a transition has status `1` exactly when it lies in the
contDiff groupoid (Mathlib's smooth-compatibility condition). -/
theorem transitionStatus_eq_one_iff
    (e e' : PartialHomeomorph M (ModelSpace n)) :
    transitionStatus e e' = 1 ↔
      (e.symm ≫ₕ e') ∈ contDiffGroupoid (∞ : WithTop ℕ∞) (model n) := by
  unfold transitionStatus
  by_cases h : (e.symm ≫ₕ e') ∈ contDiffGroupoid (∞ : WithTop ℕ∞) (model n)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hcontra
    have : (0 : Credence).val = (1 : Credence).val := by rw [hcontra]
    simp at this

omit [ChartedSpace (ModelSpace n) M] in
/-- A transition with status `1` returns the membership in the contDiff groupoid;
this is the crisp recovery for a single overlap. -/
theorem smooth_transition_recovery
    {e e' : PartialHomeomorph M (ModelSpace n)}
    (h : transitionStatus e e' = 1) :
    (e.symm ≫ₕ e') ∈ contDiffGroupoid (∞ : WithTop ℕ∞) (model n) :=
  (transitionStatus_eq_one_iff e e').mp h

end Transition

/-! ## The symm ∘ self transition is always smooth

`e.symm ≫ₕ e` lies in the contDiff groupoid for any chart `e` (Mathlib's
`symm_trans_mem_contDiffGroupoid`), so its status is certain. -/

section SelfTransition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]

omit [ChartedSpace (ModelSpace n) M] in
/-- The self-overlap transition `e.symm ≫ₕ e` always has smooth status. -/
theorem transitionStatus_symm_trans_self
    (e : PartialHomeomorph M (ModelSpace n)) :
    transitionStatus e e = 1 := by
  rw [transitionStatus_eq_one_iff]
  exact symm_trans_mem_contDiffGroupoid e

end SelfTransition

/-! ## Atlas-level smoothness status

The atlas status is `1` exactly when every ordered pair of atlas charts has
transition status `1`. We define it via the underlying Prop `AllTransitionsSmooth`
and set the status credence to `1` iff that Prop holds. -/

section Atlas

variable (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]

/-- The atlas-compatibility Prop: every ordered pair of charts in `M`'s atlas has
its transition inside the contDiff groupoid. This is exactly the
`HasGroupoid.compatible` condition for `contDiffGroupoid ∞ (model n)`. -/
def AllTransitionsSmooth : Prop :=
  ∀ {e e' : PartialHomeomorph M (ModelSpace n)},
    e ∈ atlas (ModelSpace n) M → e' ∈ atlas (ModelSpace n) M →
      (e.symm ≫ₕ e') ∈ contDiffGroupoid (∞ : WithTop ℕ∞) (model n)

/-- The aggregate atlas smoothness status: `1` when every atlas transition is
smooth, `0` otherwise. -/
noncomputable def atlasSmoothStatus : Credence :=
  if AllTransitionsSmooth n M then 1 else 0

variable {n M}

/-- The atlas status is `1` exactly when the atlas-compatibility Prop holds. -/
theorem atlasSmoothStatus_eq_one_iff_prop :
    atlasSmoothStatus n M = 1 ↔ AllTransitionsSmooth n M := by
  unfold atlasSmoothStatus
  by_cases h : AllTransitionsSmooth n M
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hcontra
    have : (0 : Credence).val = (1 : Credence).val := by rw [hcontra]
    simp at this

/-- The atlas-compatibility Prop is equivalent to `HasGroupoid` for the contDiff
groupoid: it is the unfolded `compatible` field. -/
theorem allTransitionsSmooth_iff_hasGroupoid :
    AllTransitionsSmooth n M ↔ HasGroupoid M (contDiffGroupoid (∞ : WithTop ℕ∞) (model n)) := by
  constructor
  · intro h
    exact ⟨fun he he' => h he he'⟩
  · intro h
    intro e e' he he'
    exact h.compatible he he'

/-! ## Headline recovery theorem

The atlas smoothness status reaches certainty exactly when `M` is a genuine
Mathlib smooth (`C^∞`) manifold for the model `I = 𝓘(ℝ, EuclideanSpace
ℝ (Fin n))`. `IsManifold I ∞ M` is definitionally `HasGroupoid M (contDiffGroupoid
∞ I)`, so this is a faithful crisp recovery of Mathlib's notion. -/

/-- HEADLINE RECOVERY. The graded atlas smoothness status equals certainty (`1`)
if and only if `M` is an `IsManifold` for the n-dimensional Euclidean model at
the `∞ : WithTop ℕ∞` (C^∞) order — Mathlib's genuine smooth-manifold notion.
Both directions go through the contDiff-groupoid membership API. -/
theorem atlasSmoothStatus_eq_one_iff_isManifold :
    atlasSmoothStatus n M = 1 ↔ IsManifold (model n) (∞ : WithTop ℕ∞) M := by
  rw [atlasSmoothStatus_eq_one_iff_prop, allTransitionsSmooth_iff_hasGroupoid]
  constructor
  · intro h; exact { compatible := h.compatible }
  · intro h; exact ⟨h.compatible⟩

/-- Forward recovery: atlas status `1` yields the Mathlib `IsManifold` instance. -/
theorem isManifold_of_atlasSmoothStatus
    (h : atlasSmoothStatus n M = 1) : IsManifold (model n) (∞ : WithTop ℕ∞) M :=
  atlasSmoothStatus_eq_one_iff_isManifold.mp h

/-- Backward recovery: a Mathlib `IsManifold` forces atlas status `1`. -/
theorem atlasSmoothStatus_eq_one_of_isManifold
    (h : IsManifold (model n) (∞ : WithTop ℕ∞) M) : atlasSmoothStatus n M = 1 :=
  atlasSmoothStatus_eq_one_iff_isManifold.mpr h

end Atlas

/-! ## The model space over itself is a smooth manifold

The n-dimensional Euclidean model space is a charted space over itself
(`chartedSpaceSelf`) and a Mathlib smooth manifold (`intIsManifoldModelSpace`),
so its atlas smoothness status is certain. -/

/-- The n-dimensional model space, charted over itself, has atlas smoothness
status `1`: it is a genuine Mathlib smooth manifold. -/
theorem atlasSmoothStatus_model_space (n : ℕ) :
    atlasSmoothStatus n (ModelSpace n) = 1 :=
  atlasSmoothStatus_eq_one_of_isManifold intIsManifoldModelSpace

end ManifoldN

end Cred
