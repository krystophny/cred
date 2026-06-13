/-
  Cred Dependence: Robust Collapse of a Joint/Conditional Interval (issue #643)

  The three-valued collapse (Cred.Collapse) sends a single credence to
  {0, ½, 1}. Under imprecise dependence the input is an interval `[lo, hi]`,
  not a point, so the collapse must report whether the verdict survives the
  whole interval. `collapseIntervalToThree` returns a `RobustStatus`:

  - `incoherent`         : `hi < lo` (empty interval, malformed input).
  - `underdetermined`    : `lo = 0` and `hi = 1` (full band, no information).
  - `robustZero`         : `hi < ½` (the whole interval collapses to 0).
  - `robustOne`          : `½ < lo` (the whole interval collapses to 1).
  - `robustHalf`         : `lo = hi = ½` (a single point at ½).
  - `dependenceSensitive`: otherwise (the verdict depends on the joint).

  The definition is total and the branches are mutually exclusive by
  construction. Characterization lemmas tie each status back to the interval.
-/

import Cred.Core.Value

namespace Cred

namespace Dependence

open Cred.Credence

/-- The collapse verdict for an interval `[lo, hi]` of credences. -/
inductive RobustStatus where
  | robustZero
  | robustHalf
  | robustOne
  | dependenceSensitive
  | underdetermined
  | incoherent
deriving DecidableEq, Repr

/-- Collapse a joint/conditional interval `[lo, hi]` to a robust three-valued
    verdict. Branch order fixes the semantics: incoherence first, then the
    full-band underdetermined case, then the two robust polar cases, the robust
    half point, and finally dependence sensitivity. -/
noncomputable def collapseIntervalToThree (lo hi : Credence) : RobustStatus :=
  if hi.val < lo.val then RobustStatus.incoherent
  else if lo.val = 0 ∧ hi.val = 1 then RobustStatus.underdetermined
  else if hi.val < 1 / 2 then RobustStatus.robustZero
  else if 1 / 2 < lo.val then RobustStatus.robustOne
  else if lo.val = 1 / 2 ∧ hi.val = 1 / 2 then RobustStatus.robustHalf
  else RobustStatus.dependenceSensitive

/-! ## Characterization lemmas

Each lemma reads a status off the interval endpoints. They are derived by
unfolding the definition and discharging the guards. -/

/-- Incoherent exactly when `hi < lo`. -/
theorem collapse_incoherent_iff (lo hi : Credence) :
    collapseIntervalToThree lo hi = RobustStatus.incoherent ↔ hi.val < lo.val := by
  unfold collapseIntervalToThree
  constructor
  · intro habs
    split_ifs at habs with h0
    exact h0
  · intro hc; rw [if_pos hc]

/-- A malformed interval (`hi < lo`) collapses to `incoherent`. -/
theorem collapse_incoherent_of_lt (lo hi : Credence) (h : hi.val < lo.val) :
    collapseIntervalToThree lo hi = RobustStatus.incoherent :=
  (collapse_incoherent_iff lo hi).mpr h

/-- The full band `[0, 1]` collapses to `underdetermined`. -/
theorem collapse_underdetermined_of_full (lo hi : Credence)
    (hlo : lo.val = 0) (hhi : hi.val = 1) :
    collapseIntervalToThree lo hi = RobustStatus.underdetermined := by
  unfold collapseIntervalToThree
  have hcoh : ¬ hi.val < lo.val := by rw [hlo, hhi]; norm_num
  simp [hcoh, hlo, hhi]

/-- A coherent interval whose upper end is below ½ collapses to `robustZero`. -/
theorem collapse_robustZero_of_lt (lo hi : Credence)
    (hcoh : lo.val ≤ hi.val) (hhi : hi.val < 1 / 2) :
    collapseIntervalToThree lo hi = RobustStatus.robustZero := by
  unfold collapseIntervalToThree
  have hncoh : ¬ hi.val < lo.val := not_lt.mpr hcoh
  have hnfull : ¬ (lo.val = 0 ∧ hi.val = 1) := by
    rintro ⟨_, h1⟩; rw [h1] at hhi; norm_num at hhi
  rw [if_neg hncoh, if_neg hnfull, if_pos hhi]

/-- `robustZero` forces `hi < ½`. -/
theorem collapse_robustZero_imp (lo hi : Credence)
    (h : collapseIntervalToThree lo hi = RobustStatus.robustZero) :
    hi.val < 1 / 2 := by
  unfold collapseIntervalToThree at h
  split_ifs at h with _ _ h2
  exact h2

/-- A coherent interval whose lower end exceeds ½ collapses to `robustOne`. -/
theorem collapse_robustOne_of_gt (lo hi : Credence)
    (hcoh : lo.val ≤ hi.val) (hlo : 1 / 2 < lo.val) :
    collapseIntervalToThree lo hi = RobustStatus.robustOne := by
  unfold collapseIntervalToThree
  have hncoh : ¬ hi.val < lo.val := not_lt.mpr hcoh
  have hnfull : ¬ (lo.val = 0 ∧ hi.val = 1) := by
    rintro ⟨h0, _⟩; rw [h0] at hlo; norm_num at hlo
  have hnzero : ¬ hi.val < 1 / 2 := by linarith
  rw [if_neg hncoh, if_neg hnfull, if_neg hnzero, if_pos hlo]

/-- `robustOne` forces `½ < lo`. -/
theorem collapse_robustOne_iff (lo hi : Credence) :
    collapseIntervalToThree lo hi = RobustStatus.robustOne ↔
      (lo.val ≤ hi.val ∧ 1 / 2 < lo.val) := by
  constructor
  · intro h
    unfold collapseIntervalToThree at h
    split_ifs at h with h0 _ _ h3
    exact ⟨not_lt.mp h0, h3⟩
  · rintro ⟨hcoh, hlo⟩
    exact collapse_robustOne_of_gt lo hi hcoh hlo

/-- A point interval at ½ collapses to `robustHalf`. -/
theorem collapse_robustHalf_of_eq (lo hi : Credence)
    (hlo : lo.val = 1 / 2) (hhi : hi.val = 1 / 2) :
    collapseIntervalToThree lo hi = RobustStatus.robustHalf := by
  unfold collapseIntervalToThree
  have hncoh : ¬ hi.val < lo.val := by rw [hlo, hhi]; norm_num
  have hnfull : ¬ (lo.val = 0 ∧ hi.val = 1) := by
    rintro ⟨h0, _⟩; rw [h0] at hlo; norm_num at hlo
  have hnzero : ¬ hi.val < 1 / 2 := by rw [hhi]; norm_num
  have hnone : ¬ 1 / 2 < lo.val := by rw [hlo]; norm_num
  rw [if_neg hncoh, if_neg hnfull, if_neg hnzero, if_neg hnone, if_pos ⟨hlo, hhi⟩]

/-- `robustHalf` forces `lo = hi = ½`. -/
theorem collapse_robustHalf_imp (lo hi : Credence)
    (h : collapseIntervalToThree lo hi = RobustStatus.robustHalf) :
    lo.val = 1 / 2 ∧ hi.val = 1 / 2 := by
  unfold collapseIntervalToThree at h
  split_ifs at h with _ _ _ _ h4
  exact h4

end Dependence

end Cred
