/-
  Cred Set: Quine Atoms

  A Quine atom is a non-well-founded set that is its own sole member: Q = {Q}.
  Read in the graded-membership algebra, the self-reference equation pins the
  self-membership degree q of the single node Q to the value its defining
  membership takes at the self-point.

  Two readings. The plain Quine atom Q = {Q} reads "x is a member iff x is Q";
  at the self-point this is certain, so self-membership is 1 (certain self-
  membership). The signed Quine atom reads "x is a member iff x is *not* itself",
  the Russell twist; its self-reference equation is the negation fixed point, so
  self-membership is forced to 1/2. Both are object-language instances of the
  scalar fixed-point machinery in Cred.Core.Value, mirroring Cred.Set.Russell.
-/

import Cred.Set.Basic
import Cred.Predicate

namespace Cred

namespace CredSet

open Credence

variable {U : Type*}

/-- The plain Quine atom over a node `q`: the set `{q}` whose only certain member
    is `q`. Membership elsewhere is the classical singleton indicator, lifted
    through `ofPred` (which decides via classical choice, so no `DecidableEq`). -/
noncomputable def quine (q : U) : CredSet U :=
  ofPred (fun x => x = q)

@[simp] theorem quine_mem_self (q : U) :
    (quine q).mem q = 1 :=
  (ofPred_mem_eq_one_iff _ q).mpr rfl

/-- A node `q` is a Quine point for `selfMem` when its self-membership degree
    equals its membership in the Quine atom `{q}`: the "q ∈ q" reading coincides
    with the "q ∈ {q}" the atom encodes. -/
def QuinePoint (selfMem : U → Credence) (q : U) : Prop :=
  selfMem q = (quine q).mem q

/-- The plain Quine equation: at a Quine point the self-membership degree is its
    membership in `{q}`, which is the certain value 1. -/
theorem quine_self_eq_one {selfMem : U → Credence} {q : U}
    (h : QuinePoint selfMem q) : selfMem q = 1 :=
  h.trans (quine_mem_self q)

/-- Object-language Quine theorem: a node that is its own sole member is a member
    of itself with certainty. The plain reading of Q = {Q} gives self-membership
    exactly 1; there is no fixed-point indeterminacy. -/
theorem quine_certain_self_membership {selfMem : U → Credence}
    {q : U} (h : QuinePoint selfMem q) : selfMem q = 1 :=
  quine_self_eq_one h

/-! ## Signed Quine Atom

The signed variant negates the membership reading: Q = {x | x ∉ x}, the Russell
twist of the singleton. Its self-reference equation is the negation fixed point,
so self-membership is forced to 1/2. -/

/-- The signed Quine atom: each point is a member to the degree it is *not* a
    member of itself. This is the Russell reading specialised to the Quine node. -/
def signedQuine (selfMem : U → Credence) : CredSet U :=
  ⟨fun x => ~(selfMem x)⟩

@[simp] theorem signedQuine_mem (selfMem : U → Credence) (x : U) :
    (signedQuine selfMem).mem x = ~(selfMem x) := rfl

/-- A node `q` is a signed-Quine point when its self-membership degree equals its
    membership in the signed Quine atom. -/
def SignedQuinePoint (selfMem : U → Credence) (q : U) : Prop :=
  selfMem q = (signedQuine selfMem).mem q

/-- The signed Quine equation: at a signed-Quine point self-membership is its own
    negation. -/
theorem signedQuine_self_eq_neg {selfMem : U → Credence} {q : U}
    (h : SignedQuinePoint selfMem q) : selfMem q = ~(selfMem q) :=
  h.trans (signedQuine_mem selfMem q)

/-- Object-language signed-Quine theorem: self-membership is forced to 1/2.
    Algebraic core reused from `russell_fixed_point`. -/
theorem signedQuine_self_eq_half {selfMem : U → Credence} {q : U}
    (h : SignedQuinePoint selfMem q) : selfMem q = half :=
  GradedPredicate.russell_fixed_point _ (signedQuine_self_eq_neg h)

/-! ## Existence of Admissible Solutions

The self-reference equation `selfMem q = atom.mem q` always has an admissible
credence solution: pick the self-membership degree to be the atom's membership.
For the plain atom the solution is 1; for the signed atom it is 1/2. -/

/-- Existence for the plain Quine atom: there is a self-membership reading making
    `q` a Quine point, witnessed by certain self-membership. -/
theorem quine_solution_exists (q : U) :
    ∃ selfMem : U → Credence, QuinePoint selfMem q ∧ selfMem q = 1 :=
  ⟨fun x => (quine q).mem x, rfl, quine_mem_self q⟩

/-- Existence for the signed Quine atom: there is a self-membership reading making
    `q` a signed-Quine point, with self-membership forced to 1/2. -/
theorem signedQuine_solution_exists (q : U) :
    ∃ selfMem : U → Credence, SignedQuinePoint selfMem q ∧ selfMem q = half := by
  refine ⟨fun _ => half, ?_, rfl⟩
  show half = ~half
  exact liar_fixed_point.symm

end CredSet

end Cred
