/-
  Cred Topology: Fuzzy Open Sets and Classical Recovery

  A fuzzy open set is a CredSet whose membership function is lower semicontinuous:
  for every point x and every α below s.mem x, a neighborhood of x stays above α.
  This generalises classical openness: on crisp sets the condition reduces to the
  classical predicate {x | s.mem x = 1} being open (Theorem crisp_fuzzyOpen_iff).

  The purely graded layer (FuzzyOpen for non-crisp CredSets) is genuinely fuzzy:
  membership can take any value in [0,1] and the condition quantifies over all sub-
  threshold witnesses α, not just {0,1}. The crisp fragment collapses this to the
  two-valued question of whether the support is classically open.

  Classical topology is reused from Mathlib (IsOpen, 𝓝, isOpen_iff_eventually);
  no topology is defined on Credence — FuzzyOpen lives over the ambient space U.
-/

import Cred.Set.Classical
import Mathlib.Topology.Basic
import Mathlib.Topology.Order

namespace Cred

namespace CredSet

open Credence Filter Topology

variable {U : Type*} [TopologicalSpace U]

/-! ## Fuzzy Open Sets -/

/-- A CredSet is fuzzy-open when its membership function is lower semicontinuous:
    every sub-threshold witness α has a neighborhood above it. -/
def FuzzyOpen (s : CredSet U) : Prop :=
  ∀ x : U, ∀ α : Credence, α < s.mem x → ∀ᶠ y in 𝓝 x, α < s.mem y

/-! ## Basic Examples -/

/-- The empty set is vacuously fuzzy-open: no α satisfies α < 0. -/
theorem fuzzyOpen_emptyset : FuzzyOpen (emptyset : CredSet U) := by
  intro x α hα
  simp only [emptyset_mem] at hα
  rw [lt_def, zero_val] at hα
  exact absurd hα (not_lt.mpr α.nonneg)

/-- The universal set is fuzzy-open: its membership is constantly 1. -/
theorem fuzzyOpen_univ : FuzzyOpen (univ : CredSet U) := by
  intro x α hα
  simp only [univ_mem] at *
  exact Eventually.of_forall (fun _ => hα)

/-! ## Support and Classical Recovery -/

/-- The classical support of a CredSet: the set of points with full membership. -/
def support (s : CredSet U) : Set U := {x | s.mem x = 1}

omit [TopologicalSpace U] in
@[simp]
theorem mem_support (s : CredSet U) (x : U) : x ∈ support s ↔ s.mem x = 1 :=
  Iff.rfl

omit [TopologicalSpace U] in
/-- On a crisp set, α < s.mem x forces s.mem x = 1. -/
theorem crisp_lt_mem_eq_one {s : CredSet U} (hs : Crisp s) {x : U} {α : Credence}
    (hα : α < s.mem x) : s.mem x = 1 := by
  rcases hs x with h | h
  · rw [h, lt_def, zero_val] at hα
    exact absurd hα (not_lt.mpr α.nonneg)
  · exact h

/-- CLASSICAL RECOVERY: a crisp CredSet is fuzzy-open iff its support is classically open. -/
theorem crisp_fuzzyOpen_iff {s : CredSet U} (hs : Crisp s) :
    FuzzyOpen s ↔ IsOpen (support s) := by
  constructor
  · intro hfo
    rw [isOpen_iff_eventually]
    intro x hx
    -- hx : s.mem x = 1; use α = 0 as the sub-threshold witness
    have hlt : (0 : Credence) < s.mem x := by
      rw [(mem_support s x).mp hx]
      rw [lt_def]
      simp [one_val, zero_val]
    have hev := hfo x 0 hlt
    -- crisp: 0 < s.mem y implies s.mem y = 1
    exact hev.mono (fun y hy => (mem_support s y).mpr (crisp_lt_mem_eq_one hs hy))
  · intro hopen x α hα
    have hx1 : s.mem x = 1 := crisp_lt_mem_eq_one hs hα
    -- α < 1 follows from α < s.mem x = 1
    have hα1 : α < 1 := hx1 ▸ hα
    -- the support is an open neighborhood of x
    have hxsupp : x ∈ support s := (mem_support s x).mpr hx1
    have hmem : support s ∈ 𝓝 x := IsOpen.mem_nhds hopen hxsupp
    -- every y in the support has s.mem y = 1 > α
    exact Filter.Eventually.mono (Filter.eventually_of_mem hmem (fun y hy => hy)) (fun y hy => by
      rw [(mem_support s y).mp hy]
      exact hα1)

/-! ## Example: Crisp Fuzzy-Open Set and Its Classical Counterpart -/

/-- A crisp CredSet over `Fin 3` that is fuzzy-open iff its support `{0, 2}` is open
    in the discrete topology (which it always is). -/
def crispExample : CredSet (Fin 3) :=
  ⟨fun i => if i = 1 then 0 else 1⟩

theorem crispExample_crisp : Crisp crispExample := by
  intro i; fin_cases i <;> simp [crispExample]

theorem crispExample_support :
    support crispExample = {i : Fin 3 | i ≠ 1} := by
  ext i
  simp only [mem_support, crispExample, Set.mem_setOf_eq]
  fin_cases i <;> simp [credence_zero_ne_one]

/-- In the discrete topology on `Fin 3` crispExample is fuzzy-open: every set is open. -/
theorem crispExample_fuzzyOpen : FuzzyOpen crispExample := by
  rw [crisp_fuzzyOpen_iff crispExample_crisp]
  exact isOpen_discrete _

end CredSet

end Cred
