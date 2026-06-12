/-
  Cred Set: Classical Recovery

  Ordinary set theory sits inside the crisp fragment of CredSet. On crisp sets
  the graded operations restrict to Boolean ones: complement, intersection, and
  union of crisp sets are crisp and obey the classical membership laws, and the
  pointwise subset relation becomes implication of memberships.

  The embedding `ofPred` is a bijection between predicates `U → Prop` and crisp
  CredSets, with inverse `toPred s x := s.mem x = 1`. It is a homomorphism: it
  commutes with complement, intersection, and union (reusing ofPred_compl/
  inter/union from Basic). The coincidence theorem mem_iff_classical states that
  on crisp inputs graded membership (mem x = 1) agrees with the classical
  membership read off the recovered predicate. This is the "recover ordinary
  mathematics on crisp data" guarantee.
-/

import Cred.Set.Basic

namespace Cred

namespace CredSet

open Credence

variable {U : Type*}

/-! ## Crispness Is Closed Under the Boolean Operations -/

/-- The complement of a crisp set is crisp. -/
theorem compl_crisp {s : CredSet U} (hs : Crisp s) : Crisp (compl s) := by
  intro x
  rcases hs x with h | h <;> simp [compl_mem, h]

/-- The intersection of crisp sets is crisp. -/
theorem inter_crisp {s t : CredSet U} (hs : Crisp s) (ht : Crisp t) :
    Crisp (inter s t) := by
  intro x
  rcases hs x with hsx | hsx <;> rcases ht x with htx | htx <;>
    simp [inter_mem, hsx, htx]

/-- The union of crisp sets is crisp. -/
theorem union_crisp {s t : CredSet U} (hs : Crisp s) (ht : Crisp t) :
    Crisp (union s t) := by
  intro x
  rcases hs x with hsx | hsx <;> rcases ht x with htx | htx <;>
    simp [union_mem, hsx, htx]

/-! ## Crisp Membership Predicate

On a crisp set, `mem x = 1` is the classical "x ∈ s". The two crisp values are
mutually exclusive, so the predicate is decided by which value occurs. -/

/-- The recovered classical membership predicate of a CredSet. -/
def toPred (s : CredSet U) : U → Prop := fun x => s.mem x = 1

theorem toPred_def (s : CredSet U) (x : U) : toPred s x ↔ s.mem x = 1 := Iff.rfl

/-- On crisp sets, failing to be a member means membership value 0. -/
theorem crisp_mem_zero_of_not {s : CredSet U} (hs : Crisp s) {x : U}
    (h : ¬ toPred s x) : s.mem x = 0 := by
  rcases hs x with h0 | h1
  · exact h0
  · exact absurd h1 h

/-! ## Extensionality on the Crisp Fragment -/

/-- Crisp extensionality through the recovered predicate: two crisp sets with
    the same classical members are equal. -/
theorem crisp_ext {s t : CredSet U} (hs : Crisp s) (ht : Crisp t)
    (h : ∀ x, toPred s x ↔ toPred t x) : s = t := by
  apply ext_mem
  intro x
  by_cases hx : toPred s x
  · rw [(toPred_def s x).mp hx, (toPred_def t x).mp ((h x).mp hx)]
  · have hnt : ¬ toPred t x := fun ht' => hx ((h x).mpr ht')
    rw [crisp_mem_zero_of_not hs hx, crisp_mem_zero_of_not ht hnt]

/-! ## Subset Is Classical Implication on Crisp Sets -/

/-- On crisp sets the pointwise subset relation is implication of memberships:
    `s ⊆ t` iff every classical member of `s` is a classical member of `t`. -/
theorem crisp_subset_iff {s t : CredSet U} (hs : Crisp s) (_ht : Crisp t) :
    s ⊆ t ↔ ∀ x, toPred s x → toPred t x := by
  rw [subset_def]
  constructor
  · intro h x hsx
    have hle := h x
    rw [(toPred_def s x).mp hsx] at hle
    exact (toPred_def t x).mpr (le_antisymm (le_one' _) hle)
  · intro h x
    by_cases hsx : toPred s x
    · rw [(toPred_def s x).mp hsx, (toPred_def t x).mp (h x hsx)]
    · rw [crisp_mem_zero_of_not hs hsx]; exact zero_le _

/-! ## ofPred / toPred Is a Bijection -/

/-- Round trip predicate → set → predicate: recovers the original predicate. -/
theorem toPred_ofPred (P : U → Prop) : toPred (ofPred P) = P := by
  funext x
  exact propext (ofPred_roundtrip P x)

/-- Round trip set → predicate → set: recovers a crisp set exactly. -/
theorem ofPred_toPred {s : CredSet U} (hs : Crisp s) : ofPred (toPred s) = s := by
  apply ext_mem
  intro x
  by_cases hx : toPred s x
  · rw [(ofPred_mem_eq_one_iff (toPred s) x).mpr hx, (toPred_def s x).mp hx]
  · rw [(ofPred_mem_eq_zero_iff (toPred s) x).mpr hx,
      crisp_mem_zero_of_not hs hx]

/-- `ofPred` is injective on predicates. -/
theorem ofPred_injective {P Q : U → Prop} (h : ofPred P = ofPred Q) : P = Q := by
  rw [← toPred_ofPred P, ← toPred_ofPred Q, h]

/-- `ofPred` surjects onto crisp sets: every crisp set is `ofPred` of its
    recovered predicate. -/
theorem ofPred_surjective {s : CredSet U} (hs : Crisp s) :
    ∃ P : U → Prop, ofPred P = s :=
  ⟨toPred s, ofPred_toPred hs⟩

/-! ## Homomorphism: toPred Commutes With the Operations

`ofPred_inter`, `ofPred_union`, `ofPred_compl` already establish that the
embedding commutes with the operations. The dual statements transport the
recovered predicate through complement, intersection, and union of crisp
sets. -/

/-- `toPred` of a complement is the negated predicate. -/
theorem toPred_compl {s : CredSet U} (hs : Crisp s) (x : U) :
    toPred (compl s) x ↔ ¬ toPred s x := by
  simp only [toPred_def, compl_mem]
  rcases hs x with h | h <;> simp [h, credence_zero_ne_one]

/-- `toPred` of an intersection is the conjoined predicate. -/
theorem toPred_inter {s t : CredSet U} (hs : Crisp s) (ht : Crisp t) (x : U) :
    toPred (inter s t) x ↔ toPred s x ∧ toPred t x := by
  simp only [toPred_def, inter_mem]
  rcases hs x with hsx | hsx <;> rcases ht x with htx | htx <;>
    simp [hsx, htx, credence_zero_ne_one]

/-- `toPred` of a union is the disjoined predicate. -/
theorem toPred_union {s t : CredSet U} (hs : Crisp s) (ht : Crisp t) (x : U) :
    toPred (union s t) x ↔ toPred s x ∨ toPred t x := by
  simp only [toPred_def, union_mem]
  rcases hs x with hsx | hsx <;> rcases ht x with htx | htx <;>
    simp [hsx, htx, credence_zero_ne_one]

/-! ## Coincidence: Graded Membership Agrees With Classical Membership

On crisp inputs the graded membership relation `mem x = 1` coincides with the
classical membership of the recovered predicate. Stated through `ofPred`, the
two notions of "x is a member" are the same. -/

/-- Graded membership equals classical membership on the embedded predicate:
    `(ofPred P).mem x = 1` iff `P x`. -/
theorem mem_iff_classical (P : U → Prop) (x : U) :
    (ofPred P).mem x = 1 ↔ P x :=
  ofPred_roundtrip P x

/-- The same coincidence intrinsically: on any crisp set the graded membership
    `mem x = 1` is exactly the recovered classical membership. -/
theorem crisp_mem_iff_toPred (s : CredSet U) (x : U) :
    s.mem x = 1 ↔ toPred s x :=
  (toPred_def s x).symm

end CredSet

end Cred
