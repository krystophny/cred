/-
  Cred Topology: Graded Open Sets and Classical Recovery

  A CredTopology over a carrier `U` is a family `Opens` of open CredSets closed
  under the graded set operations: `emptyset` and `univ` are open, binary
  intersection of opens is open, and arbitrary unions of opens are open. This is
  the minimal interface mirroring mathlib's `TopologicalSpace`, lifted from
  Boolean to graded membership. `Closed s := Open (compl s)`, `Clopen s :=
  Open s ∧ Closed s`, and a map is continuous when the preimage of every open
  is open.

  The crisp fragment recovers ordinary topology. A CredTopology all of whose
  opens are crisp induces a genuine mathlib `TopologicalSpace` on `U` via the
  `ofPred`/`toPred` bijection, and the recovery lemma `isOpen_iff_open` states
  that a predicate is classically open exactly when its embedded crisp CredSet
  is Cred-open. This ties the graded notion back to mathlib's `IsOpen`.
-/

import Cred.Set.Classical
import Mathlib.Topology.Basic

universe u

namespace Cred

namespace CredSet

open Credence

variable {U : Type u}

/-! ## Arbitrary Graded Union

Binary `union` from `Set.Basic` handles finite joins; mathlib topology needs
arbitrary unions. The graded union of a family `F : ι → CredSet U` takes the
supremum of memberships when it exists; on the crisp fragment the relevant
suprema are `0`/`1` and the union is just `ofPred` of the union predicate, so
the crisp bridge uses that form directly. -/

/-- The graded union of a family of predicate-embedded sets is the embedding of
    the union predicate. -/
noncomputable def iUnionPred {ι : Type*} (P : ι → U → Prop) : CredSet U :=
  ofPred (fun x => ∃ i, P i x)

theorem iUnionPred_mem_eq_one_iff {ι : Type*} (P : ι → U → Prop) (x : U) :
    (iUnionPred P).mem x = 1 ↔ ∃ i, P i x :=
  ofPred_mem_eq_one_iff _ x

theorem iUnionPred_crisp {ι : Type*} (P : ι → U → Prop) : Crisp (iUnionPred P) :=
  ofPred_crisp _

end CredSet

/-! ## CredTopology -/

open CredSet

/-- A graded topology on `U`: a family of open CredSets closed under the empty
    and universal sets, binary intersection, and arbitrary predicate unions. The
    union field is phrased on `ofPred`-style families, the form the crisp bridge
    consumes. -/
structure CredTopology (U : Type u) where
  /-- The open sets of the topology. -/
  Opens : CredSet U → Prop
  isOpen_emptyset : Opens emptyset
  isOpen_univ : Opens univ
  isOpen_inter : ∀ s t, Opens s → Opens t → Opens (inter s t)
  isOpen_iUnionPred : ∀ {ι : Type u} (P : ι → U → Prop),
    (∀ i, Opens (ofPred (P i))) → Opens (iUnionPred P)

namespace CredTopology

variable {U : Type u} (T : CredTopology U)

/-- A set is open when it lies in the topology's open family. -/
def Open (s : CredSet U) : Prop := T.Opens s

/-- A set is closed when its complement is open. -/
def Closed (s : CredSet U) : Prop := T.Open (compl s)

/-- A set is clopen when it is both open and closed. -/
def Clopen (s : CredSet U) : Prop := T.Open s ∧ T.Closed s

@[simp] theorem open_emptyset : T.Open emptyset := T.isOpen_emptyset
@[simp] theorem open_univ : T.Open univ := T.isOpen_univ

theorem open_inter {s t : CredSet U} (hs : T.Open s) (ht : T.Open t) :
    T.Open (inter s t) := T.isOpen_inter s t hs ht

/-- `univ` is closed: its complement `emptyset` is open. The complement of
    `univ` is membership `~1 = 0`, i.e. `emptyset`. -/
theorem closed_univ : T.Closed univ := by
  have h : compl (univ : CredSet U) = emptyset := by
    apply ext_mem; intro x; simp
  rw [Closed, h]; exact T.open_emptyset

/-- `emptyset` is closed: its complement `univ` is open. -/
theorem closed_emptyset : T.Closed emptyset := by
  have h : compl (emptyset : CredSet U) = univ := by
    apply ext_mem; intro x; simp
  rw [Closed, h]; exact T.open_univ

/-- `univ` is clopen. -/
theorem clopen_univ : T.Clopen univ := ⟨T.open_univ, T.closed_univ⟩

/-- `emptyset` is clopen. -/
theorem clopen_emptyset : T.Clopen emptyset := ⟨T.open_emptyset, T.closed_emptyset⟩

/-! ## Continuity

A map `f : U → V` between graded topologies is continuous when the preimage of
every open is open. The preimage of a CredSet pulls membership back along `f`. -/

/-- The preimage of a graded set along a map: membership at `x` is membership of
    `f x` in the target set. -/
def preimage {V : Type*} (f : U → V) (s : CredSet V) : CredSet U :=
  ⟨fun x => s.mem (f x)⟩

@[simp] theorem preimage_mem {V : Type*} (f : U → V) (s : CredSet V) (x : U) :
    (preimage f s).mem x = s.mem (f x) := rfl

/-- A map is continuous when the preimage of every open set is open. -/
def Continuous {V : Type*} (Tᵤ : CredTopology U) (Tᵥ : CredTopology V)
    (f : U → V) : Prop :=
  ∀ s, Tᵥ.Open s → Tᵤ.Open (preimage f s)

/-- The identity map is continuous: its preimage is the set itself. -/
theorem continuous_id : Continuous T T id := by
  intro s hs
  have h : preimage (id : U → U) s = s := by apply ext_mem; intro x; rfl
  rw [h]; exact hs

/-- Continuity is closed under composition: the preimage of an open set along
    `g ∘ f` is the preimage along `f` of its preimage along `g`. -/
theorem continuous_comp {V W : Type*} {Tᵤ : CredTopology U}
    {Tᵥ : CredTopology V} {Tw : CredTopology W} {f : U → V} {g : V → W}
    (hf : Continuous Tᵤ Tᵥ f) (hg : Continuous Tᵥ Tw g) :
    Continuous Tᵤ Tw (g ∘ f) := by
  intro s hs
  have h : preimage (g ∘ f) s = preimage f (preimage g s) := by
    apply ext_mem; intro x; rfl
  rw [h]
  exact hf _ (hg s hs)

end CredTopology

/-! ## Crisp Recovery: Bridge to Mathlib Topology

A `CredTopology` whose every open set is crisp is the graded packaging of an
ordinary topology. Through the `ofPred`/`toPred` bijection of `Set.Classical`,
its opens correspond exactly to predicates `U → Prop`, and the closure laws
become the mathlib `TopologicalSpace` axioms. The induced topology satisfies
`IsOpen P ↔ Open (ofPred P)`. -/

namespace CredTopology

variable {U : Type u} (T : CredTopology U)

/-- A topology is crisp when every open set has only 0/1 membership values. -/
def IsCrisp : Prop := ∀ s, T.Open s → CredSet.Crisp s

/-- The set of points carved out by a CredSet `s`: its classical members, i.e.
    `toPred s` viewed as a `Set U`. Topology-independent. -/
def _root_.Cred.CredSet.carrier (s : CredSet U) : Set U := {x | s.mem x = 1}

theorem _root_.Cred.CredSet.mem_carrier {s : CredSet U} {x : U} :
    x ∈ s.carrier ↔ s.mem x = 1 := Iff.rfl

/-- Mathlib topological space induced by a crisp graded topology: a set of
    points is open exactly when its embedded crisp CredSet is Cred-open. -/
noncomputable def toTopologicalSpace : TopologicalSpace U where
  IsOpen P := T.Open (CredSet.ofPred (· ∈ P))
  isOpen_univ := by
    show T.Open (CredSet.ofPred (· ∈ (Set.univ : Set U)))
    have h : CredSet.ofPred (· ∈ (Set.univ : Set U)) = CredSet.univ := by
      apply CredSet.ext_mem; intro x
      rw [(CredSet.ofPred_mem_eq_one_iff _ x).mpr (Set.mem_univ x), CredSet.univ_mem]
    rw [h]; exact T.open_univ
  isOpen_inter P Q hP hQ := by
    show T.Open (CredSet.ofPred (· ∈ P ∩ Q))
    have h : CredSet.ofPred (· ∈ P ∩ Q)
        = CredSet.inter (CredSet.ofPred (· ∈ P)) (CredSet.ofPred (· ∈ Q)) := by
      rw [CredSet.ofPred_inter]; rfl
    rw [h]; exact T.open_inter hP hQ
  isOpen_sUnion S hS := by
    show T.Open (CredSet.ofPred (· ∈ ⋃₀ S))
    -- The union of a set family is the predicate union over its members.
    have h : CredSet.ofPred (· ∈ ⋃₀ S)
        = CredSet.iUnionPred (fun P : {P // P ∈ S} => fun x => x ∈ P.1) := by
      apply CredSet.ext_mem; intro x
      by_cases hx : x ∈ ⋃₀ S
      · rw [(CredSet.ofPred_mem_eq_one_iff _ x).mpr hx]
        obtain ⟨P, hPS, hxP⟩ := hx
        rw [(CredSet.iUnionPred_mem_eq_one_iff _ x).mpr ⟨⟨P, hPS⟩, hxP⟩]
      · rw [(CredSet.ofPred_mem_eq_zero_iff _ x).mpr hx]
        rcases CredSet.iUnionPred_crisp
            (fun P : {P // P ∈ S} => fun x => x ∈ P.1) x with h0 | h1
        · exact h0.symm
        · exact absurd ((CredSet.iUnionPred_mem_eq_one_iff _ x).mp h1)
            (fun ⟨P, hxP⟩ => hx ⟨P.1, P.2, hxP⟩)
    rw [h]
    exact T.isOpen_iUnionPred _ (fun P => hS P.1 P.2)

/-- Crisp recovery. With the induced topology, a set of points `P` is mathlib-
    open exactly when its embedded crisp CredSet `ofPred (· ∈ P)` is Cred-open.
    The graded open sets are precisely the classical open sets. -/
theorem isOpen_iff_open (P : Set U) :
    @IsOpen U T.toTopologicalSpace P ↔ T.Open (CredSet.ofPred (· ∈ P)) :=
  Iff.rfl

/-- A Cred-open crisp set yields a mathlib-open set of points, and conversely:
    `Open s` (for crisp `s`) corresponds to `IsOpen (carrier s)`. This is the
    bridge from a graded open set to a classical open set. -/
theorem open_crisp_iff_isOpen {s : CredSet U} (hs : CredSet.Crisp s) :
    T.Open s ↔ @IsOpen U T.toTopologicalSpace s.carrier := by
  rw [isOpen_iff_open]
  have h : CredSet.ofPred (· ∈ s.carrier) = s := by
    have hcarrier : (fun x => x ∈ s.carrier) = CredSet.toPred s := by
      funext x; exact propext CredSet.mem_carrier
    rw [hcarrier, CredSet.ofPred_toPred hs]
  rw [h]

end CredTopology

end Cred
