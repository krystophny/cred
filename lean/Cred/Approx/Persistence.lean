/-
  Cred Approx Example: Persistent Homology as Structural Degree (issue #626)

  A topological feature in a finite filtration is a birth/death pair `(b, d)`
  with `b ≤ d`. Its persistence `d - b` is the length of the interval over which
  the feature is alive. Persistent homology reads long-lived features as robust
  signal and short-lived ones as filtration-dependent noise.

  We score that reading with the crisp structure "the feature survives at least
  one resolution `eps`": `statusScore eps b d = 1` exactly when
  `eps ≤ persistence b d`, and `0` otherwise. A feature whose persistence reaches
  the resolution scores certainty (robust); a zero-length feature scores `0`
  (underdetermined, branch-dependent).

  Status table for the single feature `b = 0`, `d = 1` (persistence `1`) across
  resolutions, with deterministic scores:

      eps      persistence   eps ≤ persistence   statusScore
      0.25     1             true                1
      0.50     1             true                1
      1.00     1             true                1
      1.50     1             false               0
      2.00     1             false               0

  The score is monotone in persistence at a fixed resolution: a longer interval
  can only raise the score (Boolean `0 ≤ 1`). Interpretation: persistent =>
  robust / certain; short-lived => branch-dependent / underdetermined.
-/

import Cred.Approx.Structure
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Cred

namespace Approx

open Credence

/-! ## Toy finite persistence intervals -/

/-- The persistence (lifetime) of a feature born at `b` and dying at `d`. -/
def persistence (b d : ℝ) : ℝ := d - b

/-- The feature is alive at filtration value `t` when it has been born but has
    not yet died. -/
def AliveAt (b d t : ℝ) : Prop := b ≤ t ∧ t < d

@[simp] theorem persistence_def (b d : ℝ) : persistence b d = d - b := rfl

/-- Persistence is nonnegative for a well-formed feature `b ≤ d`. -/
theorem persistence_nonneg {b d : ℝ} (h : b ≤ d) : 0 ≤ persistence b d := by
  simp only [persistence]; linarith

/-- A zero-length feature (`b = d`) has zero persistence. -/
theorem persistence_zero (b : ℝ) : persistence b b = 0 := by
  simp only [persistence]; ring

/-- If the feature is alive at any `t`, it has strictly positive persistence. -/
theorem persistence_pos_of_aliveAt {b d t : ℝ} (h : AliveAt b d t) :
    0 < persistence b d := by
  obtain ⟨hb, ht⟩ := h
  simp only [persistence]; linarith

/-! ## The "survives resolution `eps`" structure -/

/-- A feature is persistent at resolution `eps` when its lifetime reaches `eps`. -/
def Persistent (eps b d : ℝ) : Prop := eps ≤ persistence b d

-- `Persistent` is a real-order predicate; decide it classically.
noncomputable instance (eps b : ℝ) : DecidablePred (fun d => Persistent eps b d) :=
  fun _ => Classical.dec _

/-- The status score: certainty `1` when the feature survives resolution `eps`,
    impossibility `0` when it does not. -/
noncomputable def statusScore (eps b : ℝ) : ℝ → Credence :=
  crispScore (fun d => Persistent eps b d)

@[simp] theorem statusScore_one_iff (eps b d : ℝ) :
    statusScore eps b d = 1 ↔ eps ≤ persistence b d :=
  crispScore_one_iff (fun d => Persistent eps b d) d

@[simp] theorem statusScore_zero_iff (eps b d : ℝ) :
    statusScore eps b d = 0 ↔ ¬ eps ≤ persistence b d :=
  crispScore_zero_iff (fun d => Persistent eps b d) d

/-! ## The two extremes -/

/-- A long feature scores certainty: with resolution `eps = 1` the feature
    `(0, 2)` (persistence `2 ≥ 1`) is robust. -/
theorem long_feature_scores_one : statusScore 1 0 2 = 1 := by
  rw [statusScore_one_iff, persistence_def]; norm_num

/-- A zero-length feature scores impossibility: at any positive resolution
    `eps = 1` the feature `(b, b)` (persistence `0 < 1`) is underdetermined. -/
theorem zero_length_feature_scores_zero (b : ℝ) : statusScore 1 b b = 0 := by
  rw [statusScore_zero_iff, persistence_zero]; norm_num

/-! ## Monotonicity in persistence -/

/-- At a fixed resolution, lengthening the interval can only raise the score:
    if a feature already survives, a later death keeps it surviving. -/
theorem statusScore_mono_death {eps b d d' : ℝ} (hdd : d ≤ d')
    (h : statusScore eps b d = 1) : statusScore eps b d' = 1 := by
  rw [statusScore_one_iff, persistence_def] at h ⊢
  linarith

/-- Lowering the resolution can only raise the score: a coarser threshold is
    easier to survive. -/
theorem statusScore_mono_eps {eps eps' b d : ℝ} (he : eps' ≤ eps)
    (h : statusScore eps b d = 1) : statusScore eps' b d = 1 := by
  rw [statusScore_one_iff] at h ⊢
  linarith

/-! ## Status table, fully proved -/

/-- The deterministic status table for the feature `(0, 1)`: scores `1` up to
    resolution `1`, then `0`. -/
theorem statusTable_feature_0_1 :
    statusScore (1/4) 0 1 = 1 ∧
    statusScore (1/2) 0 1 = 1 ∧
    statusScore 1 0 1 = 1 ∧
    statusScore (3/2) 0 1 = 0 ∧
    statusScore 2 0 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [statusScore_one_iff, persistence_def]; norm_num
  · rw [statusScore_one_iff, persistence_def]; norm_num
  · rw [statusScore_one_iff, persistence_def]; norm_num
  · rw [statusScore_zero_iff, persistence_def]; norm_num
  · rw [statusScore_zero_iff, persistence_def]; norm_num

/-! ## Bridge to the structure-preservation vocabulary -/

/-- A persistent feature exactly preserves the survival structure: certainty in
    the structure-degree sense is exactly `eps ≤ persistence`. -/
theorem exactPreserves_statusScore (eps b d : ℝ) :
    ExactPreserves (statusScore eps b) d ↔ eps ≤ persistence b d := by
  rw [ExactPreserves_def]; exact statusScore_one_iff eps b d

/-- The robust feature `(0, 2)` lies in the exact-preservation class at
    resolution `1`; the noise feature `(0, 0)` does not. -/
theorem robust_vs_noise :
    ExactPreserves (statusScore 1 0) 2 ∧ ¬ ExactPreserves (statusScore 1 0) 0 := by
  refine ⟨?_, ?_⟩
  · rw [exactPreserves_statusScore, persistence_def]; norm_num
  · rw [exactPreserves_statusScore, persistence_def]; norm_num

end Approx

end Cred
