/-
  Cred Topology: Graded Atlas Seed (one-dimensional model)

  A FIRST-CUT seed toward a graded differential-geometric layer, not a manifold
  theory. The model space is fixed to ℝ (one dimension). A `GradedChart` is just
  a coordinate map `U → ℝ`; transitions between charts are supplied externally as
  real functions `τ : ℝ → ℝ`. There is no atlas cover, no Hausdorff condition, no
  second-countability, no requirement that the charts overlap or cover anything.
  Those are exactly the data a real manifold theory adds; here they are absent on
  purpose.

  WHAT IS GRADED vs THE CRISP REDUCTION.
  The graded datum is `transitionSmoothness τ`, a STATUS credence reading whether
  the supplied transition is smooth. In this first cut the status is two-valued
  (1 when `τ` is `ContDiff ℝ ⊤`, else 0): it records the classical smoothness
  predicate as a credence rather than interpolating between smooth and non-smooth.
  The CRISP REDUCTION is `transitionSmoothness_eq_one_iff`: status 1 is logically
  equivalent to ordinary mathlib smoothness, so the classical compatibility
  condition is recovered exactly with nothing added. `smooth_atlas_recovery`
  pushes this through a `GradedAtlas`: a smooth status (built from per-transition
  status 1) returns the underlying transitions as genuine `ContDiff` functions.

  The smoothness-order literal is `⊤ : WithTop ℕ∞`, the top of mathlib's order
  scale; `contDiff_id`, `contDiff_const`, and `ContDiff.comp` are order-generic,
  so they apply at `⊤` unchanged.
-/

import Cred.Core.Value
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Cred

namespace Manifold

open Credence
open Classical

/-! ## Charts over the one-dimensional model

A chart is a bare coordinate map into the fixed model space ℝ. No invertibility,
domain, or overlap data is carried: this is a seed, and those obligations belong
to a later manifold layer. -/

/-- A graded chart on `U`: a coordinate map into the one-dimensional model ℝ. -/
structure GradedChart (U : Type*) where
  toModel : U → ℝ

/-! ## Transition smoothness as a status credence

Transitions between charts are supplied as real functions `τ : ℝ → ℝ`. The status
credence records the classical smoothness predicate: certain (1) when `τ` is
smooth, impossible (0) otherwise. It is two-valued by design; interpolation
between smooth and rough is left to a later cut. -/

/-- Smoothness STATUS of a supplied transition `τ : ℝ → ℝ`, as a credence:
`1` when `τ` is `ContDiff ℝ ⊤`, `0` otherwise. -/
noncomputable def transitionSmoothness (τ : ℝ → ℝ) : Credence :=
  if ContDiff ℝ (⊤ : WithTop ℕ∞) τ then 1 else 0

/-- Crisp reduction: status `1` is exactly ordinary mathlib smoothness. -/
theorem transitionSmoothness_eq_one_iff (τ : ℝ → ℝ) :
    transitionSmoothness τ = 1 ↔ ContDiff ℝ (⊤ : WithTop ℕ∞) τ := by
  unfold transitionSmoothness
  by_cases h : ContDiff ℝ (⊤ : WithTop ℕ∞) τ
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hcontra
    -- 0 = 1 is impossible: read off the `.val`.
    have : (0 : Credence).val = (1 : Credence).val := by rw [hcontra]
    simp at this

/-- The identity transition has smooth status. -/
theorem transitionSmoothness_id : transitionSmoothness id = 1 := by
  rw [transitionSmoothness_eq_one_iff]; exact contDiff_id

/-- A constant transition has smooth status. -/
theorem transitionSmoothness_const (c : ℝ) :
    transitionSmoothness (fun _ => c) = 1 := by
  rw [transitionSmoothness_eq_one_iff]; exact contDiff_const

/-- Composition of two smooth-status transitions has smooth status: the graded
status tracks the classical `ContDiff.comp` closure. -/
theorem transitionSmoothness_comp {σ τ : ℝ → ℝ}
    (hσ : transitionSmoothness σ = 1) (hτ : transitionSmoothness τ = 1) :
    transitionSmoothness (σ ∘ τ) = 1 := by
  rw [transitionSmoothness_eq_one_iff] at hσ hτ ⊢
  exact hσ.comp hτ

/-! ## A minimal graded atlas

A `GradedAtlas` carries a finite list of charts, the transitions supplied between
consecutive overlaps as `ℝ → ℝ`, and an aggregate `smoothStatus` credence. No
cover/Hausdorff/second-countable conditions are imposed: this is the atlas seed,
not a manifold. The aggregate status is honestly defined as the meet of the
per-transition statuses, so it is `1` exactly when every supplied transition is
smooth. -/

/-- A minimal graded atlas over the one-dimensional model: charts, supplied
transitions, and an aggregate smoothness status credence. -/
structure GradedAtlas (U : Type*) where
  charts : List (GradedChart U)
  transitions : List (ℝ → ℝ)
  smoothStatus : Credence

/-- Build the aggregate smoothness status of a transition list: the conjunction
(meet, via product) of the per-transition statuses. Empty list is vacuously
smooth (status `1`). -/
noncomputable def atlasStatus (transitions : List (ℝ → ℝ)) : Credence :=
  transitions.foldr (fun τ acc => (transitionSmoothness τ) ⊗ acc) 1

/-- `atlasStatus` on a cons: the head status conjoined with the tail status. -/
theorem atlasStatus_cons (σ : ℝ → ℝ) (rest : List (ℝ → ℝ)) :
    atlasStatus (σ :: rest) = transitionSmoothness σ ⊗ atlasStatus rest := rfl

/-- The standard graded atlas built from a chart list and transition list: its
aggregate status is `atlasStatus` of the transitions. -/
noncomputable def GradedAtlas.ofTransitions {U : Type*}
    (charts : List (GradedChart U)) (transitions : List (ℝ → ℝ)) :
    GradedAtlas U where
  charts := charts
  transitions := transitions
  smoothStatus := atlasStatus transitions

/-- A product of credences is `1` only when both factors are `1`: at the top of
`[0,1]` the product has no other way to reach the maximum. -/
theorem conj_eq_one_iff (a b : Credence) :
    a ⊗ b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hval : a.val * b.val = 1 := by
      have := congrArg Credence.val h
      simpa using this
    have ha1 : a.val ≤ 1 := a.le_one
    have hb1 : b.val ≤ 1 := b.le_one
    have ha0 : 0 ≤ a.val := a.nonneg
    have hb0 : 0 ≤ b.val := b.nonneg
    -- If either factor were below 1 the product would fall short of 1:
    -- a.val * (1 - b.val) ≥ 0 forces a.val ≥ a.val * b.val = 1, and dually.
    have haeq : a.val = 1 := by nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - b.val)]
    have hbeq : b.val = 1 := by nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - a.val)]
    refine ⟨?_, ?_⟩
    · ext; simpa using haeq
    · ext; simpa using hbeq
  · rintro ⟨ha, hb⟩
    subst ha; subst hb
    ext; simp

/-- Crisp recovery for a single transition: smooth status `1` returns the
supplied transition as a genuine `ContDiff` function. -/
theorem smooth_transition_recovery {τ : ℝ → ℝ}
    (h : transitionSmoothness τ = 1) : ContDiff ℝ (⊤ : WithTop ℕ∞) τ :=
  (transitionSmoothness_eq_one_iff τ).mp h

/-- Crisp recovery for the atlas: aggregate smooth status `1` returns every
supplied transition as a genuine `ContDiff` function. This is the bridge from the
graded status back to ordinary smooth compatibility. -/
theorem smooth_atlas_recovery {U : Type*}
    (charts : List (GradedChart U)) (transitions : List (ℝ → ℝ))
    (h : (GradedAtlas.ofTransitions charts transitions).smoothStatus = 1) :
    ∀ τ ∈ transitions, ContDiff ℝ (⊤ : WithTop ℕ∞) τ := by
  -- Unfold the aggregate status; induct over the transition list. The status
  -- hypothesis mentions `transitions`, so generalize it into the motive.
  have hstatus : atlasStatus transitions = 1 := h
  clear h charts
  induction transitions with
  | nil => intro τ hτ; simp at hτ
  | cons σ rest ih =>
      rw [atlasStatus_cons] at hstatus
      obtain ⟨hσ, hrest⟩ :=
        (conj_eq_one_iff (transitionSmoothness σ) (atlasStatus rest)).mp hstatus
      intro τ hτ
      rcases List.mem_cons.mp hτ with hhead | htail
      · subst hhead; exact smooth_transition_recovery hσ
      · exact ih hrest τ htail

end Manifold

end Cred
