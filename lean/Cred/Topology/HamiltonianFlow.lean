/-
  Cred Topology: Harmonic-Oscillator Hamiltonian Phase Flow

  This is ONE worked Hamiltonian system on the phase plane, not a general
  symplectic-manifold / Hamiltonian-mechanics theory. It unifies three layers
  the repo already carries:

    * the integral-curve layer `Cred.FlowLayer` (Mathlib `IsIntegralCurve`),
    * energy conservation along the flow (`sin^2 + cos^2 = 1`), and
    * the symplectic layer `Cred.Approx` (the rotation matrix is symplectic).

  THE SYSTEM. The harmonic-oscillator Hamiltonian on the phase plane `ℝ × ℝ`
  (coordinates `(q, p)`) is

      H(q, p) = (q^2 + p^2) / 2,

  with the symplectic gradient `X_H = J ∇H = (∂H/∂p, -∂H/∂q) = (p, -q)`. Its
  phase flow through `(q₀, p₀)` is the clockwise rotation

      γ(t) = (q₀ cos t + p₀ sin t,  -q₀ sin t + p₀ cos t).

  CARRIER. We use the lightest carrier from the manifold layer: `M = ℝ × ℝ`
  with the boundaryless model `I = 𝓘(ℝ, ℝ × ℝ)`. The tangent space
  `TangentSpace I x` is then definitionally `ℝ × ℝ`, so the vector field is a
  plain `ℝ × ℝ → ℝ × ℝ` function and the integral-curve derivative condition
  reduces, exactly as in `Cred.FlowLayer.constField_integralCurve`, through
  `hasMFDerivAt_iff_hasFDerivAt` to a `HasDerivAt` assembled by `HasDerivAt.prod`
  from the `sin`/`cos` derivatives.

  HEADLINES.
    A. `oscillator_isIntegralCurve` : `γ` is a genuine Mathlib `IsIntegralCurve`
       of `X_H`; `oscillator_flow_status` exposes this at credence status 1.
       `oscillator_hasDerivAt` is the underlying plain `HasDerivAt` form.
    B. `oscillator_energy_conserved` : `H(γ t) = H(q₀, p₀)` for all `t`; the
       energy is constant along the flow. `oscillator_energy_status` reads this
       as a conservation status 1.
    C. `oscillator_flow_symplectic` : the time-`t` flow map is the rotation
       matrix `(cos t, sin t; -sin t, cos t)`, which is `Cred.Approx.Symplectic`
       (determinant 1), so the flow preserves the canonical symplectic form.
    Init. `oscillator_flow_init` : `γ 0 = (q₀, p₀)`.

  HONEST SCOPE. This is the concrete planar harmonic oscillator. It does NOT
  build the abstract symplectic form on a manifold, Hamilton's equations for a
  general `H`, Poisson brackets, or Liouville's theorem in general — those need
  symplectic-form infrastructure Mathlib does not yet have. Here the symplectic
  form is the fixed `2x2` matrix `J` of `Cred.Approx`, and energy is the explicit
  real scalar `(q^2 + p^2)/2`, not a norm (the product carries the sup norm).
-/

import Cred.Topology.IntegralCurveLayer
import Cred.Approx.Symplectic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Cred

namespace Hamiltonian

open Credence
open Classical
open scoped Manifold ContDiff
open Real

/-! ## The Hamiltonian and its vector field -/

/-- The harmonic-oscillator Hamiltonian on the phase plane: `H(q, p) = (q² + p²)/2`.
The energy of the system. -/
noncomputable def hamiltonian (x : ℝ × ℝ) : ℝ := (x.1 ^ 2 + x.2 ^ 2) / 2

/-- The Hamiltonian vector field `X_H = J ∇H = (∂H/∂p, -∂H/∂q) = (p, -q)`, the
symplectic gradient of `H`. As a function `ℝ × ℝ → ℝ × ℝ`; the tangent space of
`𝓘(ℝ, ℝ × ℝ)` is definitionally `ℝ × ℝ`. -/
def hamVF (x : ℝ × ℝ) : ℝ × ℝ := (x.2, -x.1)

/-- The model-with-corners on the phase plane `ℝ × ℝ`. -/
abbrev model : ModelWithCorners ℝ (ℝ × ℝ) (ℝ × ℝ) := 𝓘(ℝ, ℝ × ℝ)

/-- The Hamiltonian vector field as a section of the tangent space of the model;
definitionally `hamVF`. -/
def hamField (x : ℝ × ℝ) : TangentSpace model x := hamVF x

/-! ## The phase flow -/

/-- The harmonic-oscillator phase flow through `(q₀, p₀)`: the clockwise rotation
`γ(t) = (q₀ cos t + p₀ sin t, -q₀ sin t + p₀ cos t)`. -/
noncomputable def flow (q₀ p₀ : ℝ) (t : ℝ) : ℝ × ℝ :=
  (q₀ * Real.cos t + p₀ * Real.sin t, -(q₀ * Real.sin t) + p₀ * Real.cos t)

/-- INITIAL CONDITION. The flow starts at the initial point: `γ 0 = (q₀, p₀)`. -/
theorem oscillator_flow_init (q₀ p₀ : ℝ) : flow q₀ p₀ 0 = (q₀, p₀) := by
  simp [flow]

/-! ## Headline A: the flow is an integral curve of `X_H` -/

/-- The first component `t ↦ q₀ cos t + p₀ sin t` has derivative
`-(q₀ sin t) + p₀ cos t`, the second component of `γ(t)`. -/
theorem flow_fst_hasDerivAt (q₀ p₀ t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ q₀ * Real.cos s + p₀ * Real.sin s)
      (-(q₀ * Real.sin t) + p₀ * Real.cos t) t := by
  have hc : HasDerivAt (fun s : ℝ ↦ q₀ * Real.cos s) (q₀ * -Real.sin t) t :=
    (Real.hasDerivAt_cos t).const_mul q₀
  have hs : HasDerivAt (fun s : ℝ ↦ p₀ * Real.sin s) (p₀ * Real.cos t) t :=
    (Real.hasDerivAt_sin t).const_mul p₀
  have := hc.add hs
  convert this using 1
  ring

/-- The second component `t ↦ -(q₀ sin t) + p₀ cos t` has derivative
`-(q₀ cos t + p₀ sin t)`, the negated first component of `γ(t)`. -/
theorem flow_snd_hasDerivAt (q₀ p₀ t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ -(q₀ * Real.sin s) + p₀ * Real.cos s)
      (-(q₀ * Real.cos t + p₀ * Real.sin t)) t := by
  have hs : HasDerivAt (fun s : ℝ ↦ -(q₀ * Real.sin s)) (-(q₀ * Real.cos t)) t :=
    ((Real.hasDerivAt_sin t).const_mul q₀).neg
  have hc : HasDerivAt (fun s : ℝ ↦ p₀ * Real.cos s) (p₀ * -Real.sin t) t :=
    (Real.hasDerivAt_cos t).const_mul p₀
  have := hs.add hc
  convert this using 1
  ring

/-- The flow has, at every time `t`, derivative `X_H (γ t)`: this is the plain
`HasDerivAt` (= ODE) form of the integral-curve condition,
`γ'(t) = (γ(t).2, -γ(t).1)`. -/
theorem oscillator_hasDerivAt (q₀ p₀ t : ℝ) :
    HasDerivAt (flow q₀ p₀) (hamVF (flow q₀ p₀ t)) t := by
  have h := (flow_fst_hasDerivAt q₀ p₀ t).prod (flow_snd_hasDerivAt q₀ p₀ t)
  simpa [flow, hamVF] using h

/-- HEADLINE A. The harmonic-oscillator phase flow `γ` is a genuine Mathlib
`IsIntegralCurve` of the Hamiltonian vector field `X_H = (p, -q)` on the phase
plane `(ℝ × ℝ, 𝓘(ℝ, ℝ × ℝ))`. Proved exactly as
`Cred.FlowLayer.constField_integralCurve`: the manifold-derivative condition
reduces through `hasMFDerivAt_iff_hasFDerivAt` to the plain `HasDerivAt` of the
curve, here assembled from the `sin`/`cos` component derivatives. -/
theorem oscillator_isIntegralCurve (q₀ p₀ : ℝ) :
    IsIntegralCurve (I := model) (flow q₀ p₀) hamField := by
  intro t
  rw [hasMFDerivAt_iff_hasFDerivAt]
  exact (oscillator_hasDerivAt q₀ p₀ t).hasFDerivAt

/-- HEADLINE A (status form). The integral-curve status of the phase flow for the
Hamiltonian vector field is certainty (1): the flow is, with certainty, an
integral curve of `X_H`. -/
theorem oscillator_flow_status (q₀ p₀ : ℝ) :
    FlowLayer.integralCurveStatus (I := model) hamField (flow q₀ p₀) = 1 :=
  (FlowLayer.integralCurveStatus_eq_one_iff _ _).mpr (oscillator_isIntegralCurve q₀ p₀)

/-! ## Headline B: energy conservation -/

/-- HEADLINE B. Energy conservation: the Hamiltonian is constant along the flow,
`H(γ t) = H(q₀, p₀)` for every time `t`. The proof is the Pythagorean identity
`sin² + cos² = 1`, mirroring `Cred.Approx.symplectic_rotation`. -/
theorem oscillator_energy_conserved (q₀ p₀ t : ℝ) :
    hamiltonian (flow q₀ p₀ t) = hamiltonian (q₀, p₀) := by
  simp only [hamiltonian, flow]
  have h := Real.sin_sq_add_cos_sq t
  nlinarith [h, Real.sin_sq_add_cos_sq t]

/-- Energy conservation as a conservation STATUS: the credence that the energy at
time `t` equals the initial energy is certainty (1). Reads `H(γ t) = H(q₀, p₀)`
through a `0/1` status. -/
noncomputable def energyConservedStatus (q₀ p₀ t : ℝ) : Credence :=
  if hamiltonian (flow q₀ p₀ t) = hamiltonian (q₀, p₀) then 1 else 0

/-- HEADLINE B (status form). The energy-conservation status is certainty (1) at
every time. -/
theorem oscillator_energy_status (q₀ p₀ t : ℝ) :
    energyConservedStatus q₀ p₀ t = 1 := by
  unfold energyConservedStatus
  rw [if_pos (oscillator_energy_conserved q₀ p₀ t)]

/-! ## Headline C: the time-`t` flow map is symplectic -/

/-- The time-`t` flow map as a `2x2` matrix acting on the phase vector `(q₀, p₀)`:
the clockwise rotation `(cos t, sin t; -sin t, cos t)`. Its columns generate the
flow, `(flowMatrix t) • (q₀, p₀)` recovers `flow q₀ p₀ t`. -/
noncomputable def flowMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, Real.sin t; -Real.sin t, Real.cos t]

/-- The flow matrix applied (row · column) to the initial phase vector reproduces
the flow components: it is genuinely the time-`t` evolution map. -/
theorem flowMatrix_apply (q₀ p₀ t : ℝ) :
    (flowMatrix t) 0 0 * q₀ + (flowMatrix t) 0 1 * p₀ = (flow q₀ p₀ t).1 ∧
    (flowMatrix t) 1 0 * q₀ + (flowMatrix t) 1 1 * p₀ = (flow q₀ p₀ t).2 := by
  constructor <;> simp [flowMatrix, flow] <;> ring

/-- HEADLINE C. The time-`t` flow map is symplectic: the rotation matrix
`(cos t, sin t; -sin t, cos t)` preserves the canonical symplectic form `J` of
`Cred.Approx` (equivalently, has determinant 1). The harmonic-oscillator flow is
a one-parameter family of symplectomorphisms. Connects to
`Cred.Approx.symplectic_rotation` (the same rotation with the sign convention
matching this clockwise flow). -/
theorem oscillator_flow_symplectic (t : ℝ) : Cred.Approx.Symplectic (flowMatrix t) := by
  rw [flowMatrix, Cred.Approx.symplectic_iff_det, Matrix.det_fin_two_of]
  have h := Real.sin_sq_add_cos_sq t
  nlinarith [h]

/-- HEADLINE C (status form). The symplectic status of the time-`t` flow map is
certainty (1): the flow map preserves the symplectic structure exactly. -/
theorem oscillator_flow_symplectic_status (t : ℝ) :
    Cred.Approx.symplecticScore (flowMatrix t) = 1 :=
  (Cred.Approx.symplecticScore_one_iff _).mpr (oscillator_flow_symplectic t)

end Hamiltonian

end Cred
