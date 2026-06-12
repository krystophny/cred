/-
  Cred Set: Graded-Membership Sets

  A CredSet over a universe U assigns each element a credence rather than a
  Boolean. The algebra on credences (negation ~, product ⊗, De Morgan dual ⊔)
  lifts pointwise to complement, intersection, and union, with emptyset and
  univ as the constant 0 and 1 sets and a pointwise subset relation.

  A CredSet is Crisp when every membership value is 0 or 1. Crisp sets are the
  classical fragment: a predicate U → Prop embeds (via the Bool indicator and
  Cred.embed) to a Crisp CredSet, the round trip recovers the predicate, and the
  graded operations restrict to Boolean and/or/not. This is the Set-level
  counterpart of the formula-level crisp embedding in Cred.Bridge.Crisp.
-/

import Cred.Bridge.Crisp

namespace Cred

open Credence

/-- A graded-membership set over `U`: each element gets a credence. -/
@[ext]
structure CredSet (U : Type*) where
  mem : U → Credence

namespace CredSet

variable {U : Type*}

/-- The empty set: membership is impossible everywhere. -/
def emptyset : CredSet U := ⟨fun _ => 0⟩

/-- The universal set: membership is certain everywhere. -/
def univ : CredSet U := ⟨fun _ => 1⟩

@[simp] theorem emptyset_mem (x : U) : (emptyset : CredSet U).mem x = 0 := rfl
@[simp] theorem univ_mem (x : U) : (univ : CredSet U).mem x = 1 := rfl

/-- Pointwise complement. -/
def compl (s : CredSet U) : CredSet U := ⟨fun x => ~(s.mem x)⟩

/-- Pointwise intersection (product conjunction). -/
def inter (s t : CredSet U) : CredSet U := ⟨fun x => s.mem x ⊗ t.mem x⟩

/-- Pointwise union (De Morgan dual). -/
def union (s t : CredSet U) : CredSet U := ⟨fun x => s.mem x ⊔ t.mem x⟩

@[simp] theorem compl_mem (s : CredSet U) (x : U) : (compl s).mem x = ~(s.mem x) := rfl
@[simp] theorem inter_mem (s t : CredSet U) (x : U) :
    (inter s t).mem x = s.mem x ⊗ t.mem x := rfl
@[simp] theorem union_mem (s t : CredSet U) (x : U) :
    (union s t).mem x = s.mem x ⊔ t.mem x := rfl

/-- Pointwise subset: membership is everywhere at most as large. -/
def Subset (s t : CredSet U) : Prop := ∀ x, s.mem x ≤ t.mem x

instance : HasSubset (CredSet U) := ⟨Subset⟩

theorem subset_def (s t : CredSet U) : s ⊆ t ↔ ∀ x, s.mem x ≤ t.mem x := Iff.rfl

/-- Extensional equality: equal membership functions give equal sets. -/
theorem ext_mem {s t : CredSet U} (h : ∀ x, s.mem x = t.mem x) : s = t :=
  CredSet.ext (funext h)

/-! ## Crisp Sets -/

/-- A CredSet is crisp when every membership value is 0 or 1. -/
def Crisp (s : CredSet U) : Prop := ∀ x, s.mem x = 0 ∨ s.mem x = 1

/-! ## Classical Embedding

A predicate `U → Prop` becomes a Crisp CredSet by embedding its Bool indicator
through `Cred.embed`. The indicator uses classical choice so the predicate may
be arbitrary. -/

open Classical

/-- Embed a predicate as a crisp graded set: members get 1, non-members get 0. -/
noncomputable def ofPred (P : U → Prop) : CredSet U :=
  ⟨fun x => embed (decide (P x))⟩

theorem ofPred_mem (P : U → Prop) (x : U) :
    (ofPred P).mem x = embed (decide (P x)) := rfl

/-- Predicate-embedded sets are crisp. -/
theorem ofPred_crisp (P : U → Prop) : Crisp (ofPred P) :=
  fun x => embed_crisp (decide (P x))

/-- The membership value is 1 exactly on members. -/
theorem ofPred_mem_eq_one_iff (P : U → Prop) (x : U) :
    (ofPred P).mem x = 1 ↔ P x := by
  rw [ofPred_mem, embed_eq_one_iff, decide_eq_true_eq]

/-- The membership value is 0 exactly off members. -/
theorem ofPred_mem_eq_zero_iff (P : U → Prop) (x : U) :
    (ofPred P).mem x = 0 ↔ ¬ P x := by
  rcases ofPred_crisp P x with h | h
  · rw [h]
    simp only [true_iff]
    intro hp
    exact credence_zero_ne_one (h ▸ (ofPred_mem_eq_one_iff P x).mpr hp)
  · rw [h]
    constructor
    · intro h0; exact absurd h0.symm credence_zero_ne_one
    · intro hnp; exact absurd ((ofPred_mem_eq_one_iff P x).mp h) hnp

/-- Round trip: recovering the predicate `mem x = 1` from `ofPred P` gives `P`. -/
theorem ofPred_roundtrip (P : U → Prop) (x : U) :
    ((ofPred P).mem x = 1) ↔ P x :=
  ofPred_mem_eq_one_iff P x

/-- Embedding respects intersection: it is the Boolean conjunction of predicates. -/
theorem ofPred_inter (P Q : U → Prop) :
    inter (ofPred P) (ofPred Q) = ofPred (fun x => P x ∧ Q x) := by
  apply ext_mem
  intro x
  rw [inter_mem, ofPred_mem, ofPred_mem, embed_conj, ofPred_mem]
  congr 1
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

/-- Embedding respects union: it is the Boolean disjunction of predicates. -/
theorem ofPred_union (P Q : U → Prop) :
    union (ofPred P) (ofPred Q) = ofPred (fun x => P x ∨ Q x) := by
  apply ext_mem
  intro x
  rw [union_mem, ofPred_mem, ofPred_mem, embed_disj, ofPred_mem]
  congr 1
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

/-- Embedding respects complement: it is the Boolean negation of the predicate. -/
theorem ofPred_compl (P : U → Prop) :
    compl (ofPred P) = ofPred (fun x => ¬ P x) := by
  apply ext_mem
  intro x
  simp only [compl_mem, ofPred_mem, embed_neg, decide_not]

end CredSet

end Cred
