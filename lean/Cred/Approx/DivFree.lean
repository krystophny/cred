/-
  Cred Approx: Divergence-Free / Constraint Preservation (Issue #625)

  A toy 1D periodic discrete divergence on a field `u : Fin n → ℝ` is the cyclic
  forward difference `ddiv u i = u (i+1) - u i`, with `i+1` wrapping around the
  cycle (so `n` is nonzero). The structural constraint `DivFree u` asks every
  such difference to vanish: around a cycle this forces `u` to be constant. We
  lift the constraint to a 0/1 credence score via `crispScore`, so a
  constraint-preserving update is exactly an `Approx.Preserves` self-map of the
  exact-preservation class.

  Constant shifts preserve the constraint (the difference telescopes the shift
  away), so the constant-subtracting projection keeps divergence-free fields
  divergence-free. A single-coordinate perturbation is the contrast: it pushes a
  constant field off the constraint manifold, with explicit numbers on `Fin 3`.

  Admissibility link: being off the divergence-free manifold is a structural
  defect, not a numerical one. A field that fails `DivFree` scores zero, so it is
  structurally inadmissible as a state of the constrained system, the way a
  credence assignment that violates the chain rule is inadmissible rather than
  merely an inaccurate estimate.
-/

import Cred.Approx.Structure
import Mathlib.Algebra.BigOperators.Fin

namespace Cred

namespace Approx

open Credence

/-! ## The toy periodic discrete divergence -/

/-- Cyclic forward difference of a field on `Fin n`: the toy 1D divergence.
    `NeZero n` makes the wrap-around successor `i+1` well-defined. -/
def ddiv {n : ℕ} [NeZero n] (u : Fin n → ℝ) : Fin n → ℝ := fun i => u (i + 1) - u i

@[simp] theorem ddiv_def {n : ℕ} [NeZero n] (u : Fin n → ℝ) (i : Fin n) :
    ddiv u i = u (i + 1) - u i := rfl

/-- The divergence-free constraint: every cyclic difference vanishes. -/
def DivFree {n : ℕ} [NeZero n] (u : Fin n → ℝ) : Prop := ∀ i, ddiv u i = 0

/-- The constraint is classically decidable (a finite conjunction of real
    equalities), so it lifts to a structure score. -/
noncomputable instance instDecidableDivFree {n : ℕ} [NeZero n] :
    DecidablePred (DivFree (n := n)) := fun _ => Classical.dec _

/-- The 0/1 structure score of the divergence-free constraint. -/
noncomputable def divFreeScore {n : ℕ} [NeZero n] (u : Fin n → ℝ) : Credence :=
  crispScore DivFree u

@[simp] theorem divFreeScore_one_iff {n : ℕ} [NeZero n] (u : Fin n → ℝ) :
    divFreeScore u = 1 ↔ DivFree u :=
  crispScore_one_iff DivFree u

/-- Exact preservation of the divergence-free score is the constraint itself:
    a state on the manifold scores certainty, a state off it scores zero. -/
theorem exactPreserves_divFreeScore {n : ℕ} [NeZero n] (u : Fin n → ℝ) :
    ExactPreserves (divFreeScore) u ↔ DivFree u :=
  exactPreserves_crispScore DivFree u

/-- A field off the constraint manifold scores zero: it is structurally
    inadmissible, not merely an inaccurate estimate of a divergence-free field. -/
theorem inadmissible_off_manifold {n : ℕ} [NeZero n] (u : Fin n → ℝ) (h : ¬ DivFree u) :
    divFreeScore u = 0 :=
  (crispScore_zero_iff DivFree u).mpr h

/-! ## Basic constraint facts -/

/-- The zero field is divergence-free. -/
theorem divFree_zero {n : ℕ} [NeZero n] : DivFree (fun _ : Fin n => (0 : ℝ)) := by
  intro i; simp only [ddiv_def]; ring

/-- Any constant field is divergence-free. -/
theorem divFree_const {n : ℕ} [NeZero n] (c : ℝ) : DivFree (fun _ : Fin n => c) := by
  intro i; simp only [ddiv_def]; ring

/-- The divergence is shift-invariant: adding a constant changes no difference. -/
theorem ddiv_add_const {n : ℕ} [NeZero n] (u : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    ddiv (fun j => u j + c) i = ddiv u i := by
  simp only [ddiv_def]; ring

/-- Adding any constant field preserves the divergence-free constraint. -/
theorem divFree_add_const {n : ℕ} [NeZero n] {u : Fin n → ℝ} (c : ℝ) (hu : DivFree u) :
    DivFree (fun j => u j + c) := by
  intro i; rw [ddiv_add_const]; exact hu i

/-! ## The constant-subtracting projection preserves the constraint -/

/-- Subtract a fixed constant `c` from every coordinate: the toy
    "remove the mean / gauge" projection used to keep a field on the
    divergence-free manifold. -/
def shift {n : ℕ} (c : ℝ) (u : Fin n → ℝ) : Fin n → ℝ := fun j => u j - c

@[simp] theorem shift_apply {n : ℕ} (c : ℝ) (u : Fin n → ℝ) (j : Fin n) :
    shift c u j = u j - c := rfl

/-- The projection keeps divergence-free fields divergence-free. -/
theorem shift_divFree {n : ℕ} [NeZero n] (c : ℝ) {u : Fin n → ℝ} (hu : DivFree u) :
    DivFree (shift c u) := by
  intro i; simp only [shift_apply, ddiv_def]
  have := hu i; simp only [ddiv_def] at this; linarith

/-- The constant-subtracting projection is a constraint-preserving scheme.

    It moves a divergence-free state to another divergence-free state, the
    discrete shape of a gauge/projection step that stays on the constraint
    manifold rather than leaving it. -/
theorem shift_preserves {n : ℕ} [NeZero n] (c : ℝ) :
    Preserves (divFreeScore (n := n)) (shift c) := by
  intro u hu
  rw [exactPreserves_divFreeScore] at hu ⊢
  exact shift_divFree c hu

/-! ## A coordinate perturbation breaks the constraint -/

/-- A single-coordinate "bump": add `1` to coordinate `0` only. On a constant
    field this introduces a nonzero difference across coordinate `0`, breaking
    the divergence-free constraint. -/
def bump {n : ℕ} [NeZero n] (u : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if j = 0 then u j + 1 else u j

/-- The zero field on `Fin 3` is divergence-free, but the bump update sends it
    off the manifold: at coordinate `2` the difference becomes
    `(0 + 1) - 0 = 1 ≠ 0`, since `(2 : Fin 3) + 1 = 0` wraps to the bumped
    coordinate. -/
theorem bump_breaks_divFree :
    DivFree (fun _ : Fin 3 => (0 : ℝ)) ∧ ¬ DivFree (bump (fun _ : Fin 3 => (0 : ℝ))) := by
  refine ⟨divFree_zero, ?_⟩
  intro hbump
  -- the cyclic difference at index 2 wraps to index 0, where the bump lives
  have h2 := hbump 2
  have e1 : ((2 : Fin 3) + 1) = 0 := by decide
  simp only [ddiv_def, bump, e1, if_pos rfl, if_neg (by decide : (2 : Fin 3) ≠ 0)] at h2
  norm_num at h2

/-- The bump update is not a constraint-preserving scheme: starting on the
    divergence-free manifold it produces a state with nonzero divergence, hence
    a state that is structurally inadmissible (it scores zero). -/
theorem bump_not_preserves : ¬ Preserves (divFreeScore (n := 3)) bump := by
  intro hpres
  have hin : ExactPreserves (divFreeScore (n := 3)) (fun _ : Fin 3 => (0 : ℝ)) := by
    rw [exactPreserves_divFreeScore]; exact divFree_zero
  have hout := hpres _ hin
  rw [exactPreserves_divFreeScore] at hout
  exact bump_breaks_divFree.2 hout

end Approx

end Cred
