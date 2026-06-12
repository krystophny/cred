/-
  Cred Set: Graded Separation / Comprehension as a Constraint

  Separation carves a subset out of a CredSet `s` by a graded predicate
  `p : U → Credence`. Membership in the separated set is the product
  conjunction of the host membership with the predicate degree:

      (sep s p).mem x = s.mem x ⊗ p x.

  This is the defining EQUATION (a constraint), not an unrestricted
  comprehension axiom: `sep s p` exists relative to a host `s`, so there is no
  universal "set of all x with p x" that could reintroduce Russell-style
  explosion. The predicate only narrows an existing membership downward, never
  manufactures it (sep_subset).

  On the crisp fragment separation recovers classical Aussonderung: with a crisp
  host and a two-valued predicate, `sep s p` is crisp and its classical members
  are exactly the members of `s` whose predicate degree is certain — the set
  `{x ∈ s | p x = 1}`.
-/

import Cred.Set.Classical

namespace Cred

namespace CredSet

open Credence

variable {U : Type*}

/-- A graded predicate is two-valued when every degree is `0` or `1`. This is
    the predicate-level analogue of `Crisp` for sets. -/
def CrispPred (p : U → Credence) : Prop := ∀ x, p x = 0 ∨ p x = 1

/-- Graded separation: membership is the host membership conjoined with the
    predicate degree. The defining equation is a constraint on `sep s p`, not an
    unrestricted comprehension axiom. -/
def sep (s : CredSet U) (p : U → Credence) : CredSet U :=
  ⟨fun x => s.mem x ⊗ p x⟩

@[simp] theorem sep_mem (s : CredSet U) (p : U → Credence) (x : U) :
    (sep s p).mem x = s.mem x ⊗ p x := rfl

/-! ## Separation Is a Constraint, Not Free Comprehension

The defining equation only narrows the host downward: `sep s p ⊆ s` always, and
separating by the certain predicate `fun _ => 1` returns the host unchanged. -/

/-- Separation yields a subset of the host: the predicate can only shrink
    membership, never enlarge it. -/
theorem sep_subset (s : CredSet U) (p : U → Credence) : sep s p ⊆ s := by
  intro x
  rw [sep_mem, le_def, conj_val]
  calc (s.mem x).val * (p x).val ≤ (s.mem x).val * 1 :=
        mul_le_mul_of_nonneg_left (p x).le_one (s.mem x).nonneg
    _ = (s.mem x).val := mul_one _

/-- Separating by the certain predicate is the identity: the constraint is
    vacuous when every degree is `1`. -/
@[simp] theorem sep_one (s : CredSet U) : sep s (fun _ => 1) = s := by
  apply ext_mem; intro x; rw [sep_mem, conj_one]

/-- Separating by the impossible predicate empties the set. -/
@[simp] theorem sep_zero (s : CredSet U) : sep s (fun _ => 0) = emptyset := by
  apply ext_mem; intro x; rw [sep_mem, conj_zero, emptyset_mem]

/-! ## Interaction With the Crisp Fragment

Separation through an embedded predicate `ofPred P` is intersection with that
predicate's set, so it commutes with the classical embedding. -/

/-- Separating by a `Prop`-embedded predicate is intersection with its crisp
    set: the graded constraint factors through the classical embedding. -/
theorem sep_ofPred (s : CredSet U) (P : U → Prop) :
    sep s (fun x => (ofPred P).mem x) = inter s (ofPred P) := by
  apply ext_mem; intro x; rw [sep_mem, inter_mem]

/-! ## Classical Recovery

With a crisp host and a two-valued predicate, separation is crisp and recovers
ordinary Aussonderung. -/

/-- Separation by a two-valued predicate over a crisp host is crisp. -/
theorem sep_crisp {s : CredSet U} (hs : Crisp s) {p : U → Credence}
    (hp : CrispPred p) : Crisp (sep s p) := by
  intro x
  rcases hs x with hsx | hsx <;> rcases hp x with hpx | hpx <;>
    simp [sep_mem, hsx, hpx]

/-- Classical separation recovered: on a crisp host with a two-valued predicate,
    membership in `sep s p` is exactly host membership together with a certain
    predicate degree — the set `{x ∈ s | p x = 1}`. -/
theorem toPred_sep {s : CredSet U} (hs : Crisp s) {p : U → Credence}
    (hp : CrispPred p) (x : U) :
    toPred (sep s p) x ↔ toPred s x ∧ p x = 1 := by
  simp only [toPred_def, sep_mem]
  rcases hs x with hsx | hsx <;> rcases hp x with hpx | hpx <;>
    simp [hsx, hpx, credence_zero_ne_one]

/-- The same recovery stated through the embedding: separating a crisp host by
    an embedded predicate `ofPred P` has classical members `{x ∈ s | P x}`. -/
theorem toPred_sep_ofPred {s : CredSet U} (hs : Crisp s) (P : U → Prop) (x : U) :
    toPred (sep s (fun x => (ofPred P).mem x)) x ↔ toPred s x ∧ P x := by
  rw [sep_ofPred, toPred_inter hs (ofPred_crisp P), toPred_ofPred]

end CredSet

end Cred
