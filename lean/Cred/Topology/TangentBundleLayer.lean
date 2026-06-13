/-
  Cred Topology: Graded Tangent-Bundle Layer

  This layer reports three genuine Mathlib facts about the tangent bundle of a
  smooth manifold over the n-dimensional Euclidean models of
  `Cred/Topology/ManifoldN.lean` as STATUS credences, each certain (`1`) exactly
  because the underlying Mathlib object/fact really exists:

    1. The tangent bundle `TangentBundle (model n) M` is itself a Mathlib smooth
       manifold (`IsManifold (model n).tangent ∞ (TangentBundle (model n) M)`),
       supplied by `Bundle.TotalSpace.isManifold`. Status:
       `tangentBundleStatus = 1`.
    2. The bundle projection `π E (TangentSpace (model n))` is `C^∞`
       (`Bundle.contMDiff_proj`). Status: `tangentProjStatus = 1`.
    3. The zero section is a `C^∞` section. Mathlib bundles it as the zero
       element of `ContMDiffSection`, whose smoothness proof is
       `Bundle.contMDiff_zeroSection`. Status: `zeroSectionStatus = 1`.

  We work over an abstract base manifold `M` charted over `ModelSpace n` carrying
  the standard `IsManifold (model n) ∞ M` instance, so every tangent-bundle
  instance the dossier names is automatic. Instantiating `M := ModelSpace n`
  (charted over itself) discharges that hypothesis for free
  (`intIsManifoldModelSpace`); the `*_model_space` corollaries record this.

  WHAT IS GRADED vs THE CRISP RECOVERY. Each status is the credence `1` when the
  corresponding Mathlib smoothness proposition holds and `0` otherwise; the
  decision rides classical choice on that Prop. Each `*_eq_one` headline is a
  real theorem proving the status is `1` from the genuine Mathlib instance/lemma,
  and each `*_eq_one_iff` records the recovery direction: status `1` is
  equivalent to the underlying Mathlib smoothness proposition. The statuses are
  crisp (only `0` or `1`).

  The smoothness order is `∞ : WithTop ℕ∞` (C^∞) throughout, matching
  `ManifoldN`/`Differential` and Mathlib's `IsManifold`/`ContMDiff` orders.

  HONEST SCOPE. This recovers, as statuses: (TM is a smooth manifold),
  (the bundle projection is smooth), (the zero section is smooth). All three are
  proved. It does NOT build differential forms, pullbacks, connections,
  curvature, or de Rham theory — those exceed the tangent-bundle API available in
  this Mathlib version and are future cuts.
-/

import Cred.Topology.ManifoldN
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace Cred

namespace TangentLayer

open Credence
open Classical
open Bundle
open scoped Manifold ContDiff Bundle

open Cred.ManifoldN (ModelSpace model)

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are the distinct
reals `0` and `1`. Used to read each status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

section Bundle

variable {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
  [IsManifold (model n) (∞ : WithTop ℕ∞) M]

/-! ## 1. The tangent bundle is a smooth manifold

`Bundle.TotalSpace.isManifold` makes the tangent-bundle total space a Mathlib
smooth manifold for the model-with-corners `(model n).tangent = (model n).prod
𝓘(ℝ, ModelSpace n)`. The status is `1` exactly because that instance exists. -/

/-- Graded STATUS that the tangent bundle `TangentBundle (model n) M` is a Mathlib
smooth manifold (at the `∞` order, for the tangent model-with-corners): certainty
(`1`) when `IsManifold (model n).tangent ∞ (TangentBundle (model n) M)` holds,
impossibility (`0`) otherwise. -/
noncomputable def tangentBundleStatus (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
    [IsManifold (model n) (∞ : WithTop ℕ∞) M] : Credence :=
  if IsManifold (model n).tangent (∞ : WithTop ℕ∞) (TangentBundle (model n) M)
  then 1 else 0

/-- Recovery: the tangent-bundle status is `1` iff the underlying Mathlib
proposition `IsManifold (model n).tangent ∞ (TangentBundle (model n) M)` holds. -/
theorem tangentBundleStatus_eq_one_iff :
    tangentBundleStatus n M = 1 ↔
      IsManifold (model n).tangent (∞ : WithTop ℕ∞) (TangentBundle (model n) M) := by
  unfold tangentBundleStatus
  by_cases h : IsManifold (model n).tangent (∞ : WithTop ℕ∞) (TangentBundle (model n) M)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The tangent-bundle status is crisp: only `0` or `1`. -/
theorem tangentBundleStatus_crisp :
    tangentBundleStatus n M = 0 ∨ tangentBundleStatus n M = 1 := by
  unfold tangentBundleStatus
  by_cases h : IsManifold (model n).tangent (∞ : WithTop ℕ∞) (TangentBundle (model n) M)
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- HEADLINE 1. The tangent bundle is a genuine Mathlib smooth manifold, so its
status is certain (`1`). The witnessing instance is `Bundle.TotalSpace.isManifold`
(the tangent model-with-corners `(model n).tangent` is `(model n).prod 𝓘(ℝ, _)`),
which fires from `IsManifold (model n) ∞ M` together with the automatic
`ContMDiffVectorBundle ∞ (ModelSpace n) (TangentSpace (model n)) (model n)`
instance. -/
theorem tangentBundleStatus_eq_one : tangentBundleStatus n M = 1 :=
  tangentBundleStatus_eq_one_iff.mpr inferInstance

/-! ## 2. The bundle projection is smooth

`Bundle.contMDiff_proj` proves the tangent-bundle projection
`π (ModelSpace n) (TangentSpace (model n))` is `C^∞` from `(model n).tangent` to
`model n`. The status is `1` exactly because that lemma applies. -/

/-- Graded STATUS that the tangent-bundle projection is a Mathlib `C^∞` map:
certainty (`1`) when `ContMDiff (model n).tangent (model n) ∞
(π (ModelSpace n) (TangentSpace (model n)))` holds, impossibility (`0`) otherwise. -/
noncomputable def tangentProjStatus (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
    [IsManifold (model n) (∞ : WithTop ℕ∞) M] : Credence :=
  if ContMDiff (model n).tangent (model n) (∞ : WithTop ℕ∞)
      (π (ModelSpace n) (TangentSpace (model n) : M → Type _))
  then 1 else 0

/-- Recovery: the projection status is `1` iff the underlying Mathlib smoothness
proposition for the bundle projection holds. -/
theorem tangentProjStatus_eq_one_iff :
    tangentProjStatus n M = 1 ↔
      ContMDiff (model n).tangent (model n) (∞ : WithTop ℕ∞)
        (π (ModelSpace n) (TangentSpace (model n) : M → Type _)) := by
  unfold tangentProjStatus
  by_cases h : ContMDiff (model n).tangent (model n) (∞ : WithTop ℕ∞)
      (π (ModelSpace n) (TangentSpace (model n) : M → Type _))
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The projection status is crisp: only `0` or `1`. -/
theorem tangentProjStatus_crisp :
    tangentProjStatus n M = 0 ∨ tangentProjStatus n M = 1 := by
  unfold tangentProjStatus
  by_cases h : ContMDiff (model n).tangent (model n) (∞ : WithTop ℕ∞)
      (π (ModelSpace n) (TangentSpace (model n) : M → Type _))
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- HEADLINE 2. The tangent-bundle projection is a genuine Mathlib `C^∞` map, so
its status is certain (`1`). The witness is `Bundle.contMDiff_proj`. -/
theorem tangentProjStatus_eq_one : tangentProjStatus n M = 1 :=
  tangentProjStatus_eq_one_iff.mpr
    (Bundle.contMDiff_proj (TangentSpace (model n) : M → Type _))

/-! ## 3. The zero section is a smooth section

`Bundle.contMDiff_zeroSection` proves the zero section
`zeroSection (ModelSpace n) (TangentSpace (model n))` is `C^∞` from `model n` to
`(model n).tangent`. Mathlib also bundles it as the zero element of
`ContMDiffSection`. The status is `1` exactly because that lemma applies. -/

/-- Graded STATUS that the tangent-bundle zero section is a Mathlib `C^∞` map:
certainty (`1`) when `ContMDiff (model n) (model n).tangent ∞
(zeroSection (ModelSpace n) (TangentSpace (model n)))` holds, impossibility (`0`)
otherwise. -/
noncomputable def zeroSectionStatus (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
    [IsManifold (model n) (∞ : WithTop ℕ∞) M] : Credence :=
  if ContMDiff (model n) (model n).tangent (∞ : WithTop ℕ∞)
      (zeroSection (ModelSpace n) (TangentSpace (model n) : M → Type _))
  then 1 else 0

/-- Recovery: the zero-section status is `1` iff the underlying Mathlib smoothness
proposition for the zero section holds. -/
theorem zeroSectionStatus_eq_one_iff :
    zeroSectionStatus n M = 1 ↔
      ContMDiff (model n) (model n).tangent (∞ : WithTop ℕ∞)
        (zeroSection (ModelSpace n) (TangentSpace (model n) : M → Type _)) := by
  unfold zeroSectionStatus
  by_cases h : ContMDiff (model n) (model n).tangent (∞ : WithTop ℕ∞)
      (zeroSection (ModelSpace n) (TangentSpace (model n) : M → Type _))
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The zero-section status is crisp: only `0` or `1`. -/
theorem zeroSectionStatus_crisp :
    zeroSectionStatus n M = 0 ∨ zeroSectionStatus n M = 1 := by
  unfold zeroSectionStatus
  by_cases h : ContMDiff (model n) (model n).tangent (∞ : WithTop ℕ∞)
      (zeroSection (ModelSpace n) (TangentSpace (model n) : M → Type _))
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- HEADLINE 3. The tangent-bundle zero section is a genuine Mathlib `C^∞` map, so
its status is certain (`1`). The witness is `Bundle.contMDiff_zeroSection`, the
same proof Mathlib uses for the smooth zero element of `ContMDiffSection`. -/
theorem zeroSectionStatus_eq_one : zeroSectionStatus n M = 1 :=
  zeroSectionStatus_eq_one_iff.mpr
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (model n) : M → Type _))

/-- The zero section as the smooth section bundled by Mathlib: the zero element of
`ContMDiffSection`. Its `.contMDiff` field is the `C^∞` proof witnessing
`zeroSectionStatus_eq_one`. -/
noncomputable def zeroSmoothSection :
    ContMDiffSection (model n) (ModelSpace n) (∞ : WithTop ℕ∞)
      (TangentSpace (model n) : M → Type _) :=
  0

end Bundle

/-! ## Model-space corollaries

Instantiating `M := ModelSpace n` (charted over itself) discharges the
`IsManifold (model n) ∞ M` hypothesis for free via `intIsManifoldModelSpace`, so
all three statuses are certain with no carried assumption. -/

/-- The tangent bundle of the model space over itself is a smooth manifold: status
`1`. -/
theorem tangentBundleStatus_model_space (n : ℕ) :
    tangentBundleStatus n (ModelSpace n) = 1 :=
  tangentBundleStatus_eq_one

/-- The tangent-bundle projection over the model space is smooth: status `1`. -/
theorem tangentProjStatus_model_space (n : ℕ) :
    tangentProjStatus n (ModelSpace n) = 1 :=
  tangentProjStatus_eq_one

/-- The zero section over the model space is smooth: status `1`. -/
theorem zeroSectionStatus_model_space (n : ℕ) :
    zeroSectionStatus n (ModelSpace n) = 1 :=
  zeroSectionStatus_eq_one

end TangentLayer

end Cred
