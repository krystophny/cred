/-
  Cred Math: Threshold Continuity and Classical Recovery (issue #597 follow-up)

  Continuity, like the limit notion in `Cred.Math.Metric`, embeds classical
  ε-δ continuity as the crisp fragment of a graded layer. The graded datum is
  the credence-valued closeness `cClose (f x) (f y)`: a function is `t`-continuous
  at `x` when its values stay eventually `t`-close to `f x` as `y → x`. A single
  fixed threshold `t < 1` is genuinely coarser than classical continuity; it only
  forces the image tail into a band of radius `1 - t`, not to `f x`.

  CRISP REDUCTION. Taking the meet over all thresholds recovers the classical
  notion exactly: `(∀ t < 1, TContinuousAt f x t) ↔ ContinuousAt f x`
  (`tcontinuousAt_all_iff_continuousAt`), with the global version following
  pointwise (`tcontinuous_all_iff_continuous`). The recovery mirrors
  `tlimit_all_iff_tendsto`: the forward direction reads any threshold band as an
  ε-neighbourhood; the backward direction reconstructs the ε-δ condition by
  choosing a band radius `r = min (ε/2) (1/2)` and threshold `t = 1 - r`, with
  the threshold-0 edge discharged by `Credence.zero_le`.
-/

import Cred.Math.Metric
import Mathlib.Topology.MetricSpace.Basic

namespace Cred

namespace Math

open Filter Topology
open Credence

/-! ## Graded continuity

The graded primitive lifts pointwise closeness of images. `TContinuousAt f x t`
reads "as `y` approaches `x`, the value `f y` is eventually `t`-close to `f x`",
and `TContinuous f t` asks this at every point. -/

/-- Graded (threshold) continuity at a point: `f y` is eventually `t`-close to
    `f x` as `y → x`. Quantified over all thresholds `t < 1` this is classical
    continuity at `x` (`tcontinuousAt_all_iff_continuousAt`); at a single fixed
    `t` it is strictly weaker, forcing only a band of radius `1 - t`. -/
def TContinuousAt (f : ℝ → ℝ) (x : ℝ) (t : Credence) : Prop :=
  ∀ᶠ y in 𝓝 x, t ≤ cClose (f x) (f y)

/-- Graded (threshold) continuity everywhere: `t`-continuous at every point. -/
def TContinuous (f : ℝ → ℝ) (t : Credence) : Prop :=
  ∀ x, TContinuousAt f x t

/-! ## Classical recovery -/

/-- CLASSICAL RECOVERY (pointwise). Threshold continuity at `x` for every
    threshold `t < 1` is classical continuity at `x`. The backward direction
    reconstructs the ε-δ tail by choosing a band radius `r = min (ε/2) (1/2)`
    (below both `ε` and `1`, so the threshold `t = 1 - r` is positive) and
    reading the resulting threshold band as an ε-neighbourhood; the forward
    direction reads any band radius `1 - t` as an ε. Nothing graded survives
    the meet: the crisp fragment is precisely `ContinuousAt`. -/
theorem tcontinuousAt_all_iff_continuousAt (f : ℝ → ℝ) (x : ℝ) :
    (∀ t : Credence, t.val < 1 → TContinuousAt f x t) ↔ ContinuousAt f x := by
  constructor
  · intro h
    rw [Metric.continuousAt_iff]
    intro ε hε
    -- band radius r ≤ 1/2 stays below 1 (positive threshold) and below ε
    set r : ℝ := min (ε / 2) (1 / 2) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hr1 : r ≤ 1 / 2 := min_le_right _ _
    have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let t : Credence := ⟨1 - r, by linarith, by linarith⟩
    have htlt : t.val < 1 := by show (1 : ℝ) - r < 1; linarith
    have htpos : 0 < t.val := by show 0 < 1 - r; linarith
    have hev := h t htlt
    rw [TContinuousAt, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ0, hδ⟩ := hev
    refine ⟨δ, hδ0, fun {y} hy => ?_⟩
    have hmem := hδ hy
    rw [le_cClose_iff t htpos] at hmem
    have hband : |f x - f y| ≤ r := by
      have hval : (1 : ℝ) - t.val = r := by show (1 : ℝ) - (1 - r) = r; ring
      rwa [hval] at hmem
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  · intro h t htlt
    rw [TContinuousAt, Metric.eventually_nhds_iff]
    rcases eq_or_lt_of_le t.nonneg with ht0 | htpos
    · -- threshold 0: closeness ≥ 0 holds everywhere, no proximity needed
      refine ⟨1, one_pos, fun {y} _ => ?_⟩
      have ht : t = 0 := by ext; simpa using ht0.symm
      rw [ht]; exact Credence.zero_le _
    · rw [Metric.continuousAt_iff] at h
      -- band radius ρ = 1 - t.val is positive; read it as an ε-neighbourhood
      set ρ : ℝ := 1 - t.val with hρ
      have hρ0 : 0 < ρ := by show 0 < 1 - t.val; linarith
      obtain ⟨δ, hδ0, hδ⟩ := h ρ hρ0
      refine ⟨δ, hδ0, fun {y} hy => ?_⟩
      rw [le_cClose_iff t htpos]
      have hd := hδ hy
      rw [Real.dist_eq] at hd
      rw [abs_sub_comm]
      linarith [le_of_lt hd]

/-- CLASSICAL RECOVERY (global). Threshold continuity at every threshold `t < 1`
    is classical continuity. Reduces pointwise to
    `tcontinuousAt_all_iff_continuousAt` after swapping the `∀ x` / `∀ t`
    quantifiers. -/
theorem tcontinuous_all_iff_continuous (f : ℝ → ℝ) :
    (∀ t : Credence, t.val < 1 → TContinuous f t) ↔ Continuous f := by
  rw [continuous_iff_continuousAt]
  constructor
  · intro h x
    rw [← tcontinuousAt_all_iff_continuousAt]
    intro t htlt
    exact h t htlt x
  · intro h t htlt x
    exact (tcontinuousAt_all_iff_continuousAt f x).mpr (h x) t htlt

/-! ## Sanity lemmas

Constant and identity maps are threshold-continuous, matching the classical
facts through the recovery theorems. -/

/-- A constant map is `t`-continuous at every point and threshold: its image
    is fixed, so closeness is the certain `cClose c c = 1 ≥ t`. -/
theorem tcontinuousAt_const (c x : ℝ) (t : Credence) :
    TContinuousAt (fun _ => c) x t := by
  rw [TContinuousAt]
  filter_upwards with y
  simp only [cClose_self]
  exact Credence.le_one' t

/-- The identity is `t`-continuous at every point for all thresholds `t < 1`.
    Derived from the recovery theorem and mathlib's `continuousAt_id`. -/
theorem tcontinuousAt_id_all (x : ℝ) :
    ∀ t : Credence, t.val < 1 → TContinuousAt id x t :=
  (tcontinuousAt_all_iff_continuousAt id x).mpr continuousAt_id

end Math

end Cred
