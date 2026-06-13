/-
  Cred Examples: worked robust-collapse verdicts (issue #643)

  Four named applications of `Cred.Dependence.collapseIntervalToThree` to
  concrete credence intervals, one per non-`robustZero`/`robustOne` verdict.
  Endpoints are built with `Credence.mk'`; the verdict for each chosen interval
  is read off the characterization lemmas in `Cred.Dependence.RobustCollapse`.
-/

import Cred.Dependence.RobustCollapse
import Cred.Core.Value

namespace Cred.Examples.RobustCollapse

open Cred Cred.Dependence

/-- The point interval `[½, ½]` collapses to `robustHalf`. -/
theorem collapse_interval_interior_robust_half :
    collapseIntervalToThree
        (Credence.mk' (1 / 2) (by norm_num) (by norm_num))
        (Credence.mk' (1 / 2) (by norm_num) (by norm_num))
      = RobustStatus.robustHalf :=
  collapse_robustHalf_of_eq _ _ (by simp [Credence.mk']) (by simp [Credence.mk'])

/-- The interval `[3/7, 6/7]` strictly straddles ½ and collapses to
    `dependenceSensitive` (lo = 3/7 < ½ < 6/7 = hi). -/
theorem collapse_interval_boundary_sensitive :
    collapseIntervalToThree
        (Credence.mk' (3 / 7) (by norm_num) (by norm_num))
        (Credence.mk' (6 / 7) (by norm_num) (by norm_num))
      = RobustStatus.dependenceSensitive := by
  unfold collapseIntervalToThree
  simp only [Credence.mk']
  norm_num

/-- The full band `[0, 1]` (zero evidence) collapses to `underdetermined`. -/
theorem zero_evidence_collapse_underdetermined :
    collapseIntervalToThree
        (Credence.mk' 0 (by norm_num) (by norm_num))
        (Credence.mk' 1 (by norm_num) (by norm_num))
      = RobustStatus.underdetermined :=
  collapse_underdetermined_of_full _ _ (by simp [Credence.mk']) (by simp [Credence.mk'])

/-- The empty interval `[1, 0]` (`hi < lo`) collapses to `incoherent`. -/
theorem empty_fiber_collapse_incoherent :
    collapseIntervalToThree
        (Credence.mk' 1 (by norm_num) (by norm_num))
        (Credence.mk' 0 (by norm_num) (by norm_num))
      = RobustStatus.incoherent :=
  collapse_incoherent_of_lt _ _ (by simp [Credence.mk'])

end Cred.Examples.RobustCollapse
