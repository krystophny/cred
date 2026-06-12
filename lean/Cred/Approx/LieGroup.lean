/-
  Cred Approx Example: Lie-Group Integrators on SO(2) (issue #621)

  The toy group manifold is the unit circle of complex numbers, `normSq z = 1`,
  identified with the rotation group SO(2). The structure is "stay on the group",
  scored crisply by `normSq z = 1`.

  A group-based step multiplies the state by a fixed unit-modulus element `g`.
  Because `normSq` is multiplicative and `normSq g = 1`, this step stays on the
  manifold exactly, so it `Preserves` the group structure. This is the defining
  virtue of a Lie-group (geometric) integrator: the update lives in the group.

  The contrast is a coordinate/additive step `z ↦ z + w`. Even for a small
  perturbation `w` the result leaves the manifold: we give the concrete
  counterexample `1 ↦ 1 + (1/2)` at `w = 1/2`, whose squared modulus is
  `9/4 ≠ 1`. The coordinate error `|w| = 1/2` is small, yet the step is
  structurally inadmissible.
-/

import Cred.Approx.Structure
import Mathlib.Data.Complex.Basic

namespace Cred

namespace Approx

open Credence Complex

/-! ## The group manifold SO(2) as unit complex numbers -/

/-- A complex number lies on the group (unit circle / SO(2)) when its squared
    modulus is one. -/
def OnGroup (z : ℂ) : Prop := normSq z = 1

-- `OnGroup` is real equality, so its decidability is classical (noncomputable).
noncomputable instance : DecidablePred OnGroup := fun _ => Classical.dec _

/-- Membership of the group as a 0/1 credence structure. -/
noncomputable def groupScore : ℂ → Credence := crispScore OnGroup

@[simp] theorem groupScore_one_iff (z : ℂ) :
    groupScore z = 1 ↔ normSq z = 1 :=
  crispScore_one_iff OnGroup z

/-- The squared-modulus form of group membership in real coordinates. -/
theorem onGroup_iff_re_im (z : ℂ) :
    OnGroup z ↔ z.re ^ 2 + z.im ^ 2 = 1 := by
  unfold OnGroup
  rw [normSq_apply]
  constructor <;> intro h <;> nlinarith [h]

/-- The identity element `1` lies on the group. -/
theorem onGroup_one : OnGroup (1 : ℂ) := normSq_one

/-! ## A group step preserves the manifold -/

/-- One step of a group-based (geometric) integrator: left-multiply the state by
    a fixed group element `g`. -/
def groupStep (g : ℂ) (z : ℂ) : ℂ := g * z

/-- Multiplicativity of `normSq`: a group step scales the squared modulus by
    `normSq g`. -/
theorem groupStep_normSq (g z : ℂ) :
    normSq (groupStep g z) = normSq g * normSq z := by
  simp only [groupStep]
  exact normSq_mul g z

/-- A step that multiplies by a unit-modulus element stays on the group exactly,
    hence preserves the group structure. -/
theorem groupStep_preserves {g : ℂ} (hg : OnGroup g) : Preserves groupScore (groupStep g) := by
  intro z hz
  rw [ExactPreserves_def] at hz ⊢
  rw [groupScore_one_iff] at hz ⊢
  rw [groupStep_normSq, hg, hz, one_mul]

/-! ## An additive coordinate step leaves the manifold -/

/-- One step of a naive coordinate/additive scheme: add a fixed perturbation `w`. -/
def coordStep (w : ℂ) (z : ℂ) : ℂ := z + w

/-- Concrete counterexample: starting at the identity `1`, the additive step at
    the small perturbation `w = 1/2` sends `1` to `3/2`, whose squared modulus is
    `9/4 ≠ 1`. The coordinate error `|w| = 1/2` is small, yet the step leaves the
    group. -/
theorem coordStep_breaks_group :
    OnGroup (1 : ℂ) ∧ ¬ OnGroup (coordStep (1 / 2) (1 : ℂ)) := by
  refine ⟨onGroup_one, ?_⟩
  rw [onGroup_iff_re_im]
  simp only [coordStep]
  norm_num

/-- The additive coordinate step is not a group-preservation scheme: it fails the
    exact-preservation class at the identity witness. -/
theorem coordStep_not_preserves : ¬ Preserves groupScore (coordStep (1 / 2)) := by
  intro hpres
  have hstart : ExactPreserves groupScore (1 : ℂ) := by
    rw [ExactPreserves_def, groupScore_one_iff]; exact normSq_one
  have himg := hpres (1 : ℂ) hstart
  rw [ExactPreserves_def, groupScore_one_iff] at himg
  have : OnGroup (coordStep (1 / 2) (1 : ℂ)) := himg
  exact coordStep_breaks_group.2 this

end Approx

end Cred
