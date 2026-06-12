/-
  Cred Approx: Invariant-Preserving One-Step Maps

  A scalar invariant `I : X → ℝ` partitions `X` into level sets `{x | I x = c}`.
  A self-map `Φ : X → X` is invariant-preserving when `I (Φ x) = I x` for all `x`.
  Each level set is a crisp structure (Structure.crispScore of the predicate
  `fun x => I x = c`), and the central fact is that an invariant-preserving map
  preserves every such crisp structure in the sense of `Approx.Preserves`. This
  is the general pattern behind conserved-quantity dynamics: a step that fixes a
  scalar fixes each of its level sets.

  Issue #617.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

open Credence

/-! ## Invariant-preserving maps -/

/-- `Φ` preserves the scalar invariant `I`: every step leaves `I` unchanged. -/
def InvariantPreserving {X : Type*} (I : X → ℝ) (Φ : X → X) : Prop :=
  ∀ x, I (Φ x) = I x

@[simp] theorem InvariantPreserving_def {X : Type*} (I : X → ℝ) (Φ : X → X) :
    InvariantPreserving I Φ ↔ ∀ x, I (Φ x) = I x := Iff.rfl

/-- The level set of `I` at value `c`, as a predicate on `X`. -/
def LevelSet {X : Type*} (I : X → ℝ) (c : ℝ) : X → Prop := fun x => I x = c

@[simp] theorem LevelSet_def {X : Type*} (I : X → ℝ) (c : ℝ) (x : X) :
    LevelSet I c x ↔ I x = c := Iff.rfl

/-! ## Generic facts -/

/-- An invariant-preserving map keeps each level set: if `I x = c` then
    `I (Φ x) = c`. -/
theorem invariantPreserving_levelSet {X : Type*} {I : X → ℝ} {Φ : X → X}
    (h : InvariantPreserving I Φ) (c : ℝ) (x : X) (hx : LevelSet I c x) :
    LevelSet I c (Φ x) := by
  simp only [LevelSet_def] at hx ⊢
  rw [h x, hx]

/-- Identity is invariant-preserving for every invariant. -/
theorem invariantPreserving_id {X : Type*} (I : X → ℝ) :
    InvariantPreserving I (id) := fun _ => rfl

/-- Invariant-preservation is closed under composition. -/
theorem invariantPreserving_comp {X : Type*} {I : X → ℝ} {Φ Ψ : X → X}
    (hΦ : InvariantPreserving I Φ) (hΨ : InvariantPreserving I Ψ) :
    InvariantPreserving I (Ψ ∘ Φ) := fun x => by
  simp only [Function.comp_apply]
  rw [hΨ (Φ x), hΦ x]

/-! ## Connection to crisp structure preservation

The level set is a `Prop`-valued predicate, so its `crispScore` is the 0/1
structure of "lies on the level surface". Decidability is supplied classically;
the map-preservation result does not depend on the chosen instance because it
reasons through `exactPreserves_crispScore`. -/

open scoped Classical in
/-- An invariant-preserving map preserves the crisp level-set structure at every
    level `c`, in the sense of `Approx.Preserves`. This is the general pattern:
    conserving the scalar `I` conserves each of its level sets. -/
theorem invariantPreserving_preserves_crisp {X : Type*} {I : X → ℝ} {Φ : X → X}
    (h : InvariantPreserving I Φ) (c : ℝ) :
    Preserves (crispScore (LevelSet I c)) Φ := by
  intro x hx
  rw [exactPreserves_crispScore] at hx ⊢
  exact invariantPreserving_levelSet h c x hx

/-! ## Concrete instance

On pairs `ℝ × ℝ`, the first projection is a scalar invariant. The shear
`fun p => (p.1, p.2 + p.1)` fixes the first coordinate, so it is
invariant-preserving and preserves every vertical level line `{p | p.1 = c}`. -/

/-- First-coordinate invariant on `ℝ × ℝ`. -/
def fstInvariant : ℝ × ℝ → ℝ := fun p => p.1

/-- The shear `(a, b) ↦ (a, b + a)` keeps the first coordinate. -/
def shear : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + p.1)

theorem shear_invariantPreserving : InvariantPreserving fstInvariant shear :=
  fun _ => rfl

open scoped Classical in
/-- The shear preserves every vertical level set of the first coordinate. -/
theorem shear_preserves_levelSet (c : ℝ) :
    Preserves (crispScore (LevelSet fstInvariant c)) shear :=
  invariantPreserving_preserves_crisp shear_invariantPreserving c

end Approx

end Cred
