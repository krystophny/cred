/-
  Cred Set: The Russell Object

  Russell's set R = {x | x ∉ x} read in the graded-membership algebra. The
  self-application reading is supplied by a `selfMem : U → Credence` giving the
  degree to which each point lies in itself; the Russell set assigns each point
  the negation of its self-membership ("x is not a member of itself"). A Russell
  point is a designated `r` whose self-membership coincides with its membership
  in the Russell set. The self-membership degree then satisfies the negation
  fixed-point equation, so it equals 1/2 — the object-language counterpart of the
  scalar `GradedPredicate.russell_fixed_point`.
-/

import Cred.Set.Basic
import Cred.Predicate

namespace Cred

namespace CredSet

open Credence

variable {U : Type*}

/-- The Russell set for a self-application reading `selfMem`: each point is a
    member to the degree that it is *not* a member of itself. -/
def russell (selfMem : U → Credence) : CredSet U :=
  ⟨fun x => ~(selfMem x)⟩

@[simp] theorem russell_mem (selfMem : U → Credence) (x : U) :
    (russell selfMem).mem x = ~(selfMem x) := rfl

/-- A point `r` is Russell-self-applying when its self-membership degree equals
    its membership in the Russell set: the "x ∈ x" reading at `r` is the very
    "x ∉ x" reading the set encodes. -/
def RussellPoint (selfMem : U → Credence) (r : U) : Prop :=
  selfMem r = (russell selfMem).mem r

/-- The object-language Russell equation: at a Russell point, the self-membership
    degree is its own negation. -/
theorem russell_self_eq_neg {selfMem : U → Credence} {r : U}
    (h : RussellPoint selfMem r) : selfMem r = ~(selfMem r) :=
  h.trans (russell_mem selfMem r)

/-- Object-language Russell theorem: the self-membership degree at a Russell
    point is exactly 1/2. Algebraic core reused from `russell_fixed_point`. -/
theorem russell_self_eq_half {selfMem : U → Credence} {r : U}
    (h : RussellPoint selfMem r) : selfMem r = half :=
  GradedPredicate.russell_fixed_point _ (russell_self_eq_neg h)

/-- The Russell set's membership at a Russell point is likewise 1/2: belonging to
    "the set of non-self-members" is half true, half false. -/
theorem russell_mem_eq_half {selfMem : U → Credence} {r : U}
    (h : RussellPoint selfMem r) : (russell selfMem).mem r = half := by
  rw [← h]; exact russell_self_eq_half h

end CredSet

end Cred
