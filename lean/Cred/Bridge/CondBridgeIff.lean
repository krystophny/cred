/-
  Cred Part 2: Conditional Bridge — Iff Characterization

  The conditional bridge
    collapse(minCopulaCond a b) = godel_impl(collapse b, collapse a)
  holds if and only if a = 0, a = 1, b = 1, or b ≤ a.

  The forward direction (bridge ↔ boundary) packages cond_bridge_boundary
  and the interior failure into one biconditional without reproving components.
-/

import Cred.Bridge.CondBridge

namespace Cred

open Credence

/-! ## Interior failure: general form

When both a and b are strictly interior and a < b, collapse of the
min-copula conditional is half while godel_impl half half is one.
This is the general instance of the single-witness interior failure. -/

/-- For interior a < b, the bridge always fails: the conditional collapses
    to half, but godel_impl(half, half) = one. -/
theorem cond_bridge_fails_all_interior (a b : Credence) (hb : 0 < b.val)
    (ha0 : a.val ≠ 0) (ha1 : a.val ≠ 1) (hb1 : b.val ≠ 1) (hab : a.val < b.val) :
    collapse (minCopulaCond a b hb) ≠
    ThreeVal.godel_impl (collapse b) (collapse a) := by
  have hb0 : b.val ≠ 0 := ne_of_gt hb
  have ⟨hcond_pos, hcond_lt⟩ := minCopulaCond_interior a b hb
    (lt_of_le_of_ne a.nonneg (Ne.symm ha0)) hab
  rw [collapse_interior _ (ne_of_gt hcond_pos) (ne_of_lt hcond_lt)]
  rw [collapse_interior b hb0 hb1]
  rw [collapse_interior a ha0 ha1]
  decide

/-! ## Biconditional characterization

The bridge holds for given a, b (with b > 0) if and only if the pair
lies on the boundary: a = 0, a = 1, b = 1, or b.val ≤ a.val. -/

/-- Conditional bridge characterization: the bridge holds iff the pair is
    a boundary case (a = 0, a = 1, b = 1, or b ≤ a). -/
theorem cond_bridge_iff (a b : Credence) (hb : 0 < b.val) :
    collapse (minCopulaCond a b hb) = ThreeVal.godel_impl (collapse b) (collapse a)
    ↔ a = 0 ∨ a = 1 ∨ b = 1 ∨ b.val ≤ a.val := by
  constructor
  · intro heq
    by_contra h
    push_neg at h
    obtain ⟨ha0, ha1, hb1, hlt⟩ := h
    have ha0' : a.val ≠ 0 := fun hv => ha0 (by ext; exact hv)
    have ha1' : a.val ≠ 1 := fun hv => ha1 (by ext; exact hv)
    have hb1' : b.val ≠ 1 := fun hv => hb1 (by ext; exact hv)
    exact cond_bridge_fails_all_interior a b hb ha0' ha1' hb1' hlt heq
  · intro h
    exact cond_bridge_boundary a b hb h

end Cred
