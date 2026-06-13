/-
  Cred Topology: Graded Differential Layer

  This layer reports C^∞-smoothness of a map between charted spaces over the
  n-dimensional Euclidean models of `Cred/Topology/ManifoldN.lean` as a credence
  STATUS, and exposes the genuine pushforward (the differential `mfderiv`) at
  status 1. For `f : M → M'` with `ChartedSpace (ModelSpace n) M` and
  `ChartedSpace (ModelSpace m) M'`, the status is

      mdiffStatus f = if ContMDiff (model n) (model m) ∞ f then 1 else 0,

  certainty (1) exactly when `f` is a Mathlib `C^∞` map.

  HEADLINE RECOVERY. `mdiffStatus_eq_one_iff` proves
      mdiffStatus f = 1  ↔  ContMDiff (model n) (model m) ∞ f,
  a faithful two-valued recovery of Mathlib's smooth-map notion (`ContMDiff` at
  the `∞ : WithTop ℕ∞`, C^∞, order).

  THE DIFFERENTIAL IS AVAILABLE AT DEGREE 1. `mdiffStatus_mdifferentiable`
  turns status 1 into `MDifferentiable (model n) (model m) f` via
  `ContMDiff.mdifferentiable` with the `1 ≤ ∞` side condition, so the genuine
  pushforward `mfderiv (model n) (model m) f x` is the actual differential — a
  continuous linear map `TangentSpace (model n) x →L[ℝ] TangentSpace (model m) (f x)`.
  `mdiffStatus_mfderiv_isCLM` records the pushforward type at status 1, and
  `mdiffStatus_id_mfderiv` / `mdiffStatus_const_mfderiv` restate Mathlib's
  `mfderiv_id` / `mfderiv_const` in this layer.

  BRIDGE TO ORDINARY CALCULUS. For a map of the model spaces themselves,
  `mdiffStatus_modelMap_eq_one_iff` proves
      mdiffStatus f = 1  ↔  ContDiff ℝ ∞ f,
  connecting this differential layer to ordinary Fréchet calculus (and so to
  `Cred.Math.Smoothness`) via `contMDiff_iff_contDiff`.

  HONEST SCOPE. This recovers Mathlib's `ContMDiff` / `MDifferentiable` /
  `mfderiv` as a status and exposes the differential. It does NOT yet build
  differential forms, pullbacks, or de Rham cohomology — those are future cuts.
-/

import Cred.Topology.ManifoldN
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

namespace Cred

namespace Differential

open Credence
open Classical
open scoped Manifold ContDiff
open Cred.ManifoldN (ModelSpace model)

/-! ## Graded smoothness status of a map -/

section MapStatus

variable {n m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']

/-- Graded C^∞-smoothness STATUS of a map `f : M → M'` between charted spaces
over the n- and m-dimensional Euclidean models, as a credence: certainty (1)
when `f` is a Mathlib `C^∞` map (`ContMDiff` at the `∞` order), impossibility
(0) otherwise. The `if` is decided through classical choice on the `ContMDiff`
proposition. -/
noncomputable def mdiffStatus (n m : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']
    (f : M → M') : Credence :=
  if ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f then 1 else 0

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are the distinct
reals `0` and `1`. Used to read the status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

/-- HEADLINE RECOVERY. The graded smoothness status equals certainty (1) if and
only if `f` is a genuine Mathlib `C^∞` map between the Euclidean-model charted
spaces (`ContMDiff` at the `∞ : WithTop ℕ∞` order). A faithful two-valued
recovery of Mathlib's smooth-map notion. -/
theorem mdiffStatus_eq_one_iff (f : M → M') :
    mdiffStatus n m f = 1 ↔ ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f := by
  unfold mdiffStatus
  by_cases h : ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The graded smoothness status equals impossibility (0) exactly when `f` is not
a `C^∞` map. -/
theorem mdiffStatus_eq_zero_iff (f : M → M') :
    mdiffStatus n m f = 0 ↔ ¬ ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f := by
  unfold mdiffStatus
  by_cases h : ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f
  · simp only [h, if_true, not_true, iff_false]
    intro ho; exact absurd ho.symm cred_zero_ne_one
  · simp only [h, if_false, not_false_iff, iff_true]

/-- The status is crisp: it takes only the values `0` or `1`, never an interior
credence. -/
theorem mdiffStatus_crisp (f : M → M') :
    mdiffStatus n m f = 0 ∨ mdiffStatus n m f = 1 := by
  unfold mdiffStatus
  by_cases h : ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-! ## The differential is available at degree 1

Status 1 means `C^∞`, which is `1 ≤ ∞`-smooth, so `f` is `MDifferentiable` and
the genuine pushforward `mfderiv` is the actual differential. -/

/-- At status 1, `f` is Mathlib-differentiable, so the differential
`mfderiv (model n) (model m) f x` is the genuine pushforward. The `1 ≤ ∞` side
condition is discharged with the `(mod_cast le_top)` idiom from Mathlib's own
manifold code. -/
theorem mdiffStatus_mdifferentiable {f : M → M'} (h : mdiffStatus n m f = 1) :
    MDifferentiable (model n) (model m) f :=
  ((mdiffStatus_eq_one_iff f).mp h).mdifferentiable (mod_cast le_top)

/-- At status 1, the differential at each point is a continuous linear map between
tangent spaces, the genuine tangent pushforward. This exposes the differential's
type: `mfderiv (model n) (model m) f x` lives in
`TangentSpace (model n) x →L[ℝ] TangentSpace (model m) (f x)`. -/
theorem mdiffStatus_mfderiv_isCLM {f : M → M'} (_h : mdiffStatus n m f = 1) (x : M) :
    ∃ L : TangentSpace (model n) x →L[ℝ] TangentSpace (model m) (f x),
      mfderiv (model n) (model m) f x = L :=
  ⟨mfderiv (model n) (model m) f x, rfl⟩

end MapStatus

/-! ## Bridge to ordinary calculus on the model space

For a map of the model spaces themselves, the status reduces to ordinary Fréchet
`C^∞`-smoothness via `contMDiff_iff_contDiff`. This is the bridge to
`Cred.Math.Smoothness` and the rest of ordinary calculus. -/

section ModelMap

variable {n m : ℕ}

/-- BRIDGE TO ORDINARY CALCULUS. For a map `f : ModelSpace n → ModelSpace m` of
the Euclidean model spaces, the graded smoothness status equals certainty (1) if
and only if `f` is ordinarily `C^∞` (`ContDiff ℝ ∞ f`). Connects this
differential layer to Fréchet calculus through `contMDiff_iff_contDiff`. -/
theorem mdiffStatus_modelMap_eq_one_iff (f : ModelSpace n → ModelSpace m) :
    mdiffStatus n m f = 1 ↔ ContDiff ℝ (∞ : WithTop ℕ∞) f := by
  rw [mdiffStatus_eq_one_iff]
  exact contMDiff_iff_contDiff

end ModelMap

/-! ## Supporting reals: id, const, composition, and their differentials -/

section Closure

variable {n m k : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace (ModelSpace k) M'']

/-- The identity map is `C^∞`, so its smoothness status is certain. -/
theorem mdiffStatus_id : mdiffStatus n n (id : M → M) = 1 :=
  (mdiffStatus_eq_one_iff _).mpr contMDiff_id

/-- A constant map is `C^∞`, so its smoothness status is certain. -/
theorem mdiffStatus_const (c : M') : mdiffStatus n m (fun _ : M => c) = 1 :=
  (mdiffStatus_eq_one_iff _).mpr contMDiff_const

/-- Composition preserves smooth status: if `f : M → M'` and `g : M' → M''` are
both at status 1, then `g ∘ f` is at status 1. -/
theorem mdiffStatus_comp {f : M → M'} {g : M' → M''}
    (hg : mdiffStatus m k g = 1) (hf : mdiffStatus n m f = 1) :
    mdiffStatus n k (g ∘ f) = 1 :=
  (mdiffStatus_eq_one_iff _).mpr
    (((mdiffStatus_eq_one_iff g).mp hg).comp ((mdiffStatus_eq_one_iff f).mp hf))

/-- Tangent fact: at the (certain) status of the identity, its differential is
the identity continuous-linear-map on the tangent space, restating Mathlib's
`mfderiv_id`. -/
theorem mdiffStatus_id_mfderiv (x : M) :
    mfderiv (model n) (model n) (id : M → M) x
      = ContinuousLinearMap.id ℝ (TangentSpace (model n) x) :=
  mfderiv_id

/-- Tangent fact: a constant map's differential is the zero continuous-linear-map,
restating Mathlib's `mfderiv_const`. -/
theorem mdiffStatus_const_mfderiv (c : M') (x : M) :
    mfderiv (model n) (model m) (fun _ : M => c) x
      = (0 : TangentSpace (model n) x →L[ℝ] TangentSpace (model m) c) :=
  mfderiv_const

end Closure

end Differential

end Cred
