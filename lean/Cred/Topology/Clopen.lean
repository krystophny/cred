/-
  Cred Topology: Clopen Sets Are Not a Contradiction

  "Clopen" (closed and open) sounds self-contradictory in naive language, the
  way an impossible-evidence conditional sounds explosive. It is not. In
  mathlib `IsClopen s` unfolds to `IsClosed s ∧ IsOpen s`, and `IsClosed s`
  means `IsOpen sᶜ`, NOT `¬ IsOpen s`. So clopen is a conjunction of two
  positive, jointly satisfiable openness facts about `s` and `sᶜ`. The two
  predicates are compatible, and which sets are clopen depends on the ambient
  topology, not on any contradiction.

  This is the topological mirror of Cred's no-explosion design. Naive language
  ("closed and open", "conditioning on the impossible") reads as paradox;
  the formal predicates are consistent. Cred sharpens the vocabulary instead
  of blurring it: `IsClosed` is `IsOpen` of the complement, just as
  `cred(A|B) ⊗ cred(B) = cred(A ∧ B)` imposes nothing — rather than ex falso —
  when `cred(B) = 0`.

  ISSUES: #601 (empty/univ clopen in ℝ), #602 (clopen depends on the ambient
  topology), #607 (clopen is a consistent conjunction, not a contradiction).
  All topology is reused from mathlib; nothing here reinvents it.
-/

import Mathlib.Topology.Clopen
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas

namespace Cred.Topology

open Set

/-! ## (#601) The trivial clopen sets of the standard real line

In the standard topology on `ℝ` the empty set and the whole line are clopen.
These reuse mathlib's `isClopen_empty` / `isClopen_univ` (which hold in every
topological space) specialized to `ℝ`. -/

theorem isClopen_empty_real : IsClopen (∅ : Set ℝ) := isClopen_empty

theorem isClopen_univ_real : IsClopen (univ : Set ℝ) := isClopen_univ

/-- On the connected real line these are the ONLY clopen sets: `IsClopen s`
    forces `s = ∅ ∨ s = univ`. Reuses `isClopen_iff` for preconnected spaces. -/
theorem real_isClopen_iff_trivial {s : Set ℝ} :
    IsClopen s ↔ s = ∅ ∨ s = univ :=
  isClopen_iff

/-! ## (#607) Clopen is a consistent conjunction, not a contradiction

The conceptual core. `IsClosed s` is definitionally `IsOpen sᶜ` (mathlib's
`isClosed_compl_iff`), NOT the negation `¬ IsOpen s`. Hence `IsClopen s`
expands to the conjunction `IsOpen s ∧ IsOpen sᶜ`: two positive openness
claims, one about `s` and one about its complement. There is no `P ∧ ¬ P`. -/

/-- The formal expansion: `IsClopen s ↔ IsOpen s ∧ IsOpen sᶜ`. The right side is
    a conjunction of two openness facts, never `IsOpen s ∧ ¬ IsOpen s`. -/
theorem isClopen_iff_isOpen_and_isOpen_compl
    {X : Type*} [TopologicalSpace X] {s : Set X} :
    IsClopen s ↔ IsOpen s ∧ IsOpen sᶜ := by
  rw [IsClopen, ← isOpen_compl_iff, and_comm]

/-- Closedness is openness of the complement, not failure of openness. The two
    sides of the clopen conjunction are about different sets, so they impose no
    mutual contradiction. -/
theorem isClosed_iff_isOpen_compl
    {X : Type*} [TopologicalSpace X] {s : Set X} :
    IsClosed s ↔ IsOpen sᶜ := isOpen_compl_iff.symm

/-- A concrete clopen witness: `univ` in `ℝ` satisfies the expanded conjunction,
    both `univ` and its complement `∅` being open. -/
theorem univ_real_isOpen_and_isOpen_compl :
    IsOpen (univ : Set ℝ) ∧ IsOpen (univ : Set ℝ)ᶜ :=
  (isClopen_iff_isOpen_and_isOpen_compl).mp isClopen_univ_real

/-! ## (#602) Clopen depends on the ambient topology

The same underlying set can be clopen under one topology and not under another.
We take the singleton `{0} ⊆ ℝ`. Under the discrete topology (`⊥`) every set is
open and closed, so `{0}` is clopen. Under the standard topology `{0}` is not
even open (a punctured neighbourhood of `0` is nonempty), so it is not clopen.
The two `TopologicalSpace ℝ` instances are supplied explicitly with `@`. -/

/-- Under the discrete topology every set is clopen; in particular `{0} ⊆ ℝ`. -/
theorem singleton_isClopen_discrete :
    @IsClopen ℝ ⊥ ({0} : Set ℝ) :=
  ⟨@isClosed_discrete ℝ ⊥ (discreteTopology_bot ℝ) _,
    @isOpen_discrete ℝ ⊥ (discreteTopology_bot ℝ) _⟩

/-- Under the standard topology `{0} ⊆ ℝ` is not open: `0` has a nonempty
    punctured neighbourhood, so the singleton fails the openness half. -/
theorem singleton_not_isOpen_real : ¬ IsOpen ({0} : Set ℝ) :=
  not_isOpen_singleton (0 : ℝ)

/-- Therefore `{0} ⊆ ℝ` is NOT clopen in the standard topology: clopen requires
    openness, which fails. Same set, opposite clopen status across topologies. -/
theorem singleton_not_isClopen_real : ¬ IsClopen ({0} : Set ℝ) :=
  fun h => singleton_not_isOpen_real h.isOpen

/-- The dependence stated as one fact: `{0} ⊆ ℝ` is clopen in the discrete
    topology yet not clopen in the standard topology. Clopen status is a
    property of the set together with its ambient topology, not of the set
    alone — and certainly not a contradiction. -/
theorem singleton_clopen_discrete_not_standard :
    @IsClopen ℝ ⊥ ({0} : Set ℝ) ∧ ¬ IsClopen ({0} : Set ℝ) :=
  ⟨singleton_isClopen_discrete, singleton_not_isClopen_real⟩

end Cred.Topology
