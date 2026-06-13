/-
  Cred Examples: Hypothetical Branches (issues #634(4), #641)

  A concrete contradictory branch and the named no-explosion fact: the
  unrelated atom `U` is not derivable from a locally contradictory branch under
  the generative rules, which contain no explosion rule.
-/

import Cred.ProofTheory.Branches

namespace Cred.Examples.Branches

open Cred Cred.ProofTheory

/-- The unrelated atom `U` (atom `1` over `Fin 2`). -/
def U : Formula (Fin 2) := .atom 1

/-- The contradictory branch holds atom `0` and its negation, both positive. -/
noncomputable def branch : Branch (Fin 2) := contradictoryBranch

/-- The branch is locally contradictory at the positive label. -/
theorem branch_locallyContradictory :
    LocallyContradictory branch.assumptions .positive :=
  contradictoryBranch_locallyContradictory

/-- No explosion: the unrelated atom `U` is NOT derivable at the positive label
    from the contradictory branch.  The generative calculus has no explosion
    rule, so the half/zero countermodel blocks the derivation. -/
theorem local_contradiction_no_explosion_example :
    ¬ branch.Derived .positive U :=
  local_contradiction_no_explosion

end Cred.Examples.Branches
