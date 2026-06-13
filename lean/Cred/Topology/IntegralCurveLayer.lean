/-
  Cred Topology: Graded Integral-Curve / Flow Layer

  This layer reports the assertion that a curve `γ : ℝ → M` is an integral curve
  of a vector field `v` on a charted space `M` as a credence STATUS, and recovers
  Mathlib's integral-curve theory at status 1. For

      γ : ℝ → M,  v : (x : M) → TangentSpace I x,

  the status is

      integralCurveStatus v γ = if IsIntegralCurve γ v then 1 else 0,

  certainty (1) exactly when `γ` is a Mathlib `IsIntegralCurve` of `v`.

  HEADLINE RECOVERY. `integralCurveStatus_eq_one_iff` proves
      integralCurveStatus v γ = 1  ↔  IsIntegralCurve γ v,
  a faithful two-valued recovery of Mathlib's integral-curve predicate (the
  manifold-derivative condition `HasMFDerivAt 𝓘(ℝ,ℝ) I γ t (...)` at every `t`).
  `integralCurveStatus_crisp` records that the status is two-valued.

  EXISTENCE (Picard–Lindelöf). `integralCurve_exists` recovers Mathlib's local
  existence theorem `exists_isIntegralCurveAt_of_contMDiffAt_boundaryless`: a
  `C^1` vector field on a boundaryless `C^1` manifold over a complete model space
  has a local integral curve through any point. We carry exactly Mathlib's
  hypotheses (`CompleteSpace E`, `BoundarylessManifold I M`, `IsManifold I 1 M`,
  and the bundled-section smoothness of `v`) and return the `IsIntegralCurveAt`
  witness.

  UNIQUENESS. `integralCurve_unique` recovers Mathlib's global uniqueness theorem
  `isIntegralCurve_eq_of_contMDiff`: two status-1 global integral curves of a
  `C^1` field that agree at one time agree everywhere. We carry Mathlib's
  hypotheses (`T2Space M`, interior points, bundled-section smoothness) and read
  the two `IsIntegralCurve` premises off their status-1 credences.

  CONCRETE FLOW. On the model space `M = ModelSpace n = EuclideanSpace ℝ (Fin n)`
  with `I = 𝓘(ℝ, ModelSpace n)`, the tangent space is definitionally the model
  space, so a constant vector field is `fun _ ↦ c`. `constField_integralCurve`
  proves the explicit translation `γ t = x₀ + t • c` is a genuine
  `IsIntegralCurve` of that field, by reducing the manifold-derivative condition
  to the ordinary `HasFDerivAt` of an affine map. `constField_integralCurve_status`
  exposes this at status 1. The special case `c = 0` recovers Mathlib's
  `isIntegralCurve_const` (the constant curve at a zero of the field) as a status.

  HONEST SCOPE. This recovers Mathlib's `IsIntegralCurve` predicate, its local
  existence (Picard–Lindelöf), and its global uniqueness as a status, with a
  concrete model-space translation flow. It does NOT build the global flow map
  `(t, x) ↦ φ_t x`, the one-parameter group / flow semigroup, completeness of
  vector fields, or Hamiltonian dynamics — those are future cuts.
-/

import Cred.Topology.ManifoldN
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace Cred

namespace FlowLayer

open Credence
open Classical
open Set
open scoped Manifold Topology ContDiff
open Cred.ManifoldN (ModelSpace model)

/-! ## Graded integral-curve status -/

section Status

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are the distinct
reals `0` and `1`. Used to read the status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

/-- Graded integral-curve STATUS of a curve `γ : ℝ → M` for a vector field
`v : (x : M) → TangentSpace I x`, as a credence: certainty (1) when `γ` is a
Mathlib `IsIntegralCurve` of `v`, impossibility (0) otherwise. The `if` is
decided through classical choice on the `IsIntegralCurve` proposition. -/
noncomputable def integralCurveStatus
    (v : (x : M) → TangentSpace I x) (γ : ℝ → M) : Credence :=
  if IsIntegralCurve γ v then 1 else 0

/-- HEADLINE RECOVERY. The graded integral-curve status equals certainty (1) if
and only if `γ` is a genuine Mathlib integral curve of `v` (the manifold
derivative condition `HasMFDerivAt 𝓘(ℝ,ℝ) I γ t ((1).smulRight (v (γ t)))` at
every `t`). A faithful two-valued recovery of Mathlib's `IsIntegralCurve`. -/
theorem integralCurveStatus_eq_one_iff
    (v : (x : M) → TangentSpace I x) (γ : ℝ → M) :
    integralCurveStatus v γ = 1 ↔ IsIntegralCurve γ v := by
  unfold integralCurveStatus
  by_cases h : IsIntegralCurve γ v
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The graded integral-curve status equals impossibility (0) exactly when `γ` is
not an integral curve of `v`. -/
theorem integralCurveStatus_eq_zero_iff
    (v : (x : M) → TangentSpace I x) (γ : ℝ → M) :
    integralCurveStatus v γ = 0 ↔ ¬ IsIntegralCurve γ v := by
  unfold integralCurveStatus
  by_cases h : IsIntegralCurve γ v
  · simp only [h, if_true, not_true, iff_false]
    intro ho; exact absurd ho.symm cred_zero_ne_one
  · simp only [h, if_false, not_false_iff, iff_true]

/-- The status is crisp: it takes only the values `0` or `1`, never an interior
credence. -/
theorem integralCurveStatus_crisp
    (v : (x : M) → TangentSpace I x) (γ : ℝ → M) :
    integralCurveStatus v γ = 0 ∨ integralCurveStatus v γ = 1 := by
  unfold integralCurveStatus
  by_cases h : IsIntegralCurve γ v
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- Convenience: read the Mathlib `IsIntegralCurve` predicate off a status-1
credence. -/
theorem isIntegralCurve_of_status
    {v : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (h : integralCurveStatus v γ = 1) : IsIntegralCurve γ v :=
  (integralCurveStatus_eq_one_iff v γ).mp h

end Status

/-! ## Existence: Picard–Lindelöf as a status witness

We carry Mathlib's hypotheses for local existence on a boundaryless `C^1`
manifold over a complete model space and return the `IsIntegralCurveAt` witness
through the requested point. This is local existence; building the global flow is
a future cut. -/

section Existence

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [CompleteSpace E] [BoundarylessManifold I M]

/-- EXISTENCE (Picard–Lindelöf), recovered as a status statement. For a `C^1`
vector field `v` on a boundaryless `C^1` manifold over a complete model space,
through any point `x₀` and at any time `t₀` there is an integral curve `γ` with
`γ t₀ = x₀` and local integral-curve status `1` at every time in a neighbourhood
of `t₀`. Carries exactly Mathlib's hypotheses for
`exists_isIntegralCurveAt_of_contMDiffAt_boundaryless`. -/
theorem integralCurve_exists
    {v : (x : M) → TangentSpace I x} (t₀ : ℝ) (x₀ : M)
    (hv : ContMDiffAt I I.tangent 1
      (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := t₀) hv

end Existence

/-! ## Uniqueness: global uniqueness read off two status-1 curves

We carry Mathlib's hypotheses for global uniqueness (`T2Space`, interior points,
bundled-section smoothness) and read the two `IsIntegralCurve` premises off their
status-1 credences. -/

section Uniqueness

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [T2Space M]

/-- UNIQUENESS, recovered through the status. Two global integral curves `γ γ'`
of a `C^1` vector field `v`, both at integral-curve status `1`, that agree at one
time `t₀`, are equal. Hypotheses are exactly Mathlib's for
`isIntegralCurve_eq_of_contMDiff`; the two `IsIntegralCurve` premises are read
off the status-1 credences. -/
theorem integralCurve_unique
    {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {t₀ : ℝ}
    (hγt : ∀ t, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : integralCurveStatus v γ = 1) (hγ' : integralCurveStatus v γ' = 1)
    (h : γ t₀ = γ' t₀) : γ = γ' :=
  isIntegralCurve_eq_of_contMDiff hγt hv
    (isIntegralCurve_of_status hγ) (isIntegralCurve_of_status hγ') h

/-- Boundaryless variant of uniqueness: drops the interior-point hypothesis. -/
theorem integralCurve_unique_boundaryless [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {t₀ : ℝ}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : integralCurveStatus v γ = 1) (hγ' : integralCurveStatus v γ' = 1)
    (h : γ t₀ = γ' t₀) : γ = γ' :=
  isIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv
    (isIntegralCurve_of_status hγ) (isIntegralCurve_of_status hγ') h

end Uniqueness

/-! ## Concrete flow: translation by a constant field on the model space

On `M = ModelSpace n = EuclideanSpace ℝ (Fin n)` with `I = 𝓘(ℝ, ModelSpace n)`,
the tangent space `TangentSpace (model n) x` is definitionally `ModelSpace n`, so
a constant vector field is `fun _ ↦ c` with `c : ModelSpace n`. The translation
`γ t = x₀ + t • c` is its integral curve. The manifold-derivative condition
reduces, on the model space, to the ordinary `HasFDerivAt` of an affine map. -/

section ConcreteFlow

variable {n : ℕ}

/-- The affine translation `t ↦ x₀ + t • c` has Fréchet derivative
`(1 : ℝ →L[ℝ] ℝ).smulRight c` at every time: the constant map `a ↦ a • c`. -/
theorem translation_hasFDerivAt (x₀ c : ModelSpace n) (t : ℝ) :
    HasFDerivAt (fun s : ℝ ↦ x₀ + s • c)
      ((1 : ℝ →L[ℝ] ℝ).smulRight c) t := by
  have h : HasFDerivAt (fun s : ℝ ↦ s • c)
      ((1 : ℝ →L[ℝ] ℝ).smulRight c) t := by
    simpa using (hasFDerivAt_id t).smul_const c
  simpa using (hasFDerivAt_const x₀ t).add h

/-- CONCRETE FLOW. On the n-dimensional Euclidean model space, the translation
`γ t = x₀ + t • c` is a genuine Mathlib integral curve of the constant vector
field `fun _ ↦ c`. Proved by reducing the manifold-derivative condition (model
space on both source `𝓘(ℝ,ℝ)` and target `model n`) to the ordinary
`HasFDerivAt` of the affine map. -/
theorem constField_integralCurve (x₀ c : ModelSpace n) :
    IsIntegralCurve (I := model n) (fun t : ℝ ↦ x₀ + t • c)
      (fun p : ModelSpace n ↦ (c : TangentSpace (model n) p)) := by
  intro t
  rw [hasMFDerivAt_iff_hasFDerivAt]
  exact translation_hasFDerivAt x₀ c t

/-- The concrete translation flow at status 1: the graded integral-curve status
of the constant-field translation is certainty. -/
theorem constField_integralCurve_status (x₀ c : ModelSpace n) :
    integralCurveStatus (I := model n)
      (fun p : ModelSpace n ↦ (c : TangentSpace (model n) p))
      (fun t : ℝ ↦ x₀ + t • c) = 1 :=
  (integralCurveStatus_eq_one_iff _ _).mpr (constField_integralCurve x₀ c)

/-- Zero-field special case, recovering Mathlib's `isIntegralCurve_const`: when
`c = 0` the translation is the constant curve at `x₀`, an integral curve of the
zero field, exposed at status 1. -/
theorem constField_zero_integralCurve_status (x₀ : ModelSpace n) :
    integralCurveStatus (I := model n)
      (fun p : ModelSpace n ↦ (0 : TangentSpace (model n) p))
      (fun _ : ℝ ↦ x₀) = 1 :=
  (integralCurveStatus_eq_one_iff _ _).mpr (isIntegralCurve_const rfl)

end ConcreteFlow

end FlowLayer

end Cred
