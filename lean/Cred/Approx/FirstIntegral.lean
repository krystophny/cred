/-
  Cred Approx: First-Integral Preserving Methods (issue #618)

  A first integral (conserved quantity) is a map `H : X → ℝ` constant along the
  orbit of a scheme `Φ : X → X`. Exact energy preservation is `H (Φ x) = H x`.
  Lifted through the shared `Approx` abstraction via `crispScore`, the
  preservation predicate becomes a 0/1 structure score, so first-integral
  preservation is exact preservation of that structure.

  Concrete instance: the quarter-turn `rot90 (x,y) = (-y, x)` conserves the
  radial energy `H₂ (x,y) = x² + y²`, hence maps every energy level set to
  itself. Contrast: the contraction `shrink (x,y) = (x/2, y/2)` strictly
  decreases `H₂` at every nonzero point, so it is not first-integral
  preserving.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

namespace FirstIntegral

open Credence
open scoped Classical

/-! ## First integrals and energy preservation -/

/-- `H` is a first integral of `Φ` at `x` when its value is conserved by one step. -/
def EnergyPreserving {X : Type*} (H : X → ℝ) (Φ : X → X) (x : X) : Prop :=
  H (Φ x) = H x

/-- A scheme conserves `H` everywhere. -/
def FirstIntegralPreserving {X : Type*} (H : X → ℝ) (Φ : X → X) : Prop :=
  ∀ x, EnergyPreserving H Φ x

/-- 0/1 structure score reading off energy preservation at a point. -/
noncomputable def energyScore {X : Type*} (H : X → ℝ) (Φ : X → X) (x : X) : Credence :=
  crispScore (fun y => EnergyPreserving H Φ y) x

/-- Exact preservation of the energy-score structure is energy preservation. -/
theorem exactPreserves_energyScore {X : Type*} (H : X → ℝ) (Φ : X → X) (x : X) :
    ExactPreserves (energyScore H Φ) x ↔ EnergyPreserving H Φ x := by
  unfold energyScore
  exact exactPreserves_crispScore _ x

/-- A first integral makes the energy structure exactly preserved everywhere. -/
theorem firstIntegralPreserving_iff_exact {X : Type*} (H : X → ℝ) (Φ : X → X) :
    FirstIntegralPreserving H Φ ↔ ∀ x, ExactPreserves (energyScore H Φ) x := by
  constructor
  · intro h x; exact (exactPreserves_energyScore H Φ x).mpr (h x)
  · intro h x; exact (exactPreserves_energyScore H Φ x).mp (h x)

/-! ## Level sets

A first integral sends each level set `{x | H x = c}` into itself; the orbit
never leaves the level it starts on. -/

/-- The `c`-level set of the integral `H`. -/
def LevelSet {X : Type*} (H : X → ℝ) (c : ℝ) : Set X := {x | H x = c}

/-- An energy-preserving step keeps a point on its level set. -/
theorem mem_levelSet_step {X : Type*} {H : X → ℝ} {Φ : X → X} {x : X} {c : ℝ}
    (hpres : EnergyPreserving H Φ x) (hx : x ∈ LevelSet H c) : Φ x ∈ LevelSet H c := by
  show H (Φ x) = c
  rw [hpres]; exact hx

/-- A first integral preserves every energy level set. -/
theorem firstIntegral_preserves_levelSets {X : Type*} {H : X → ℝ} {Φ : X → X}
    (h : FirstIntegralPreserving H Φ) (c : ℝ) :
    ∀ x ∈ LevelSet H c, Φ x ∈ LevelSet H c :=
  fun x hx => mem_levelSet_step (h x) hx

/-! ## Concrete instance: quarter-turn conserves radial energy -/

/-- Radial energy on the plane: `H₂ (x,y) = x² + y²`. -/
def radialEnergy (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- Quarter-turn (90° rotation) of the plane: `(x,y) ↦ (-y, x)`. -/
def rot90 (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, p.1)

/-- The quarter-turn conserves radial energy at every point. -/
theorem rot90_energyPreserving (p : ℝ × ℝ) : EnergyPreserving radialEnergy rot90 p := by
  show radialEnergy (rot90 p) = radialEnergy p
  unfold radialEnergy rot90
  ring

/-- The quarter-turn is first-integral preserving for radial energy. -/
theorem rot90_firstIntegralPreserving : FirstIntegralPreserving radialEnergy rot90 :=
  rot90_energyPreserving

/-- Hence the quarter-turn preserves every radial level set (every circle). -/
theorem rot90_preserves_levelSets (c : ℝ) :
    ∀ p ∈ LevelSet radialEnergy c, rot90 p ∈ LevelSet radialEnergy c :=
  firstIntegral_preserves_levelSets rot90_firstIntegralPreserving c

/-- The energy structure is exactly preserved everywhere under the quarter-turn. -/
theorem rot90_exactPreserves (p : ℝ × ℝ) :
    ExactPreserves (energyScore radialEnergy rot90) p :=
  (exactPreserves_energyScore radialEnergy rot90 p).mpr (rot90_energyPreserving p)

/-! ## Counterexample: a dissipative contraction -/

/-- Contraction of the plane toward the origin: `(x,y) ↦ (x/2, y/2)`. -/
noncomputable def shrink (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / 2, p.2 / 2)

/-- The contraction scales radial energy by `1/4`. -/
theorem shrink_energy (p : ℝ × ℝ) : radialEnergy (shrink p) = radialEnergy p / 4 := by
  unfold radialEnergy shrink
  ring

/-- The contraction strictly decreases radial energy at every nonzero point. -/
theorem shrink_strictly_dissipative (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    radialEnergy (shrink p) < radialEnergy p := by
  rw [shrink_energy]
  have hpos : 0 < radialEnergy p := by
    have hne : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hp (Prod.ext_iff.mpr ⟨hcon.1, hcon.2⟩)
    unfold radialEnergy
    rcases hne with hx | hy
    · have h1 : 0 < p.1 ^ 2 := by positivity
      nlinarith [sq_nonneg p.2]
    · have h2 : 0 < p.2 ^ 2 := by positivity
      nlinarith [sq_nonneg p.1]
  linarith

/-- The contraction fails to conserve radial energy at every nonzero point. -/
theorem shrink_not_energyPreserving (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    ¬ EnergyPreserving radialEnergy shrink p := by
  intro h
  have hlt := shrink_strictly_dissipative p hp
  unfold EnergyPreserving at h
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- The contraction is not first-integral preserving for radial energy. -/
theorem shrink_not_firstIntegralPreserving :
    ¬ FirstIntegralPreserving radialEnergy shrink := by
  intro h
  exact shrink_not_energyPreserving (1, 0) (by norm_num [Prod.ext_iff]) (h (1, 0))

/-- At a nonzero point the dissipative map's energy structure is the zero score. -/
theorem shrink_energyScore_zero (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    energyScore radialEnergy shrink p = 0 := by
  unfold energyScore
  rw [crispScore_zero_iff]
  exact shrink_not_energyPreserving p hp

/-- So the dissipative map does not exactly preserve the energy structure. -/
theorem shrink_not_exactPreserves (p : ℝ × ℝ) (hp : p ≠ (0, 0)) :
    ¬ ExactPreserves (energyScore radialEnergy shrink) p := by
  rw [exactPreserves_energyScore]
  exact shrink_not_energyPreserving p hp

end FirstIntegral

end Approx

end Cred
