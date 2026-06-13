/-
  Cred Topology: Graded Diffeomorphism Layer

  This layer reports whether a map `f : M → M'` between charted spaces over the
  Euclidean models of `Cred/Topology/ManifoldN.lean` is a `C^∞` DIFFEOMORPHISM
  (a smooth isomorphism, Mathlib's `Diffeomorph`) as a credence STATUS:

      diffeoStatus f = if (∃ d : M ≃ₘ⟮model n, model m⟯ M', d.toFun = f) then 1 else 0,

  certainty (1) exactly when `f` is the underlying map of some genuine Mathlib
  `Diffeomorph` at the `∞ : WithTop ℕ∞` (C^∞) order.

  HEADLINE RECOVERY. `diffeoStatus_eq_one_iff` proves
      diffeoStatus f = 1  ↔  ∃ d : Diffeomorph (model n) (model m) M M' ∞, d.toFun = f,
  a faithful two-valued recovery of "f is a C^∞ diffeomorphism". Mathlib has no
  unbundled `IsDiffeomorph` predicate in this version, so the witness is the
  bundled `Diffeomorph` itself.

  SMOOTHNESS BOTH WAYS AT STATUS 1. A diffeomorphism is `ContMDiff` in both
  directions. `diffeoStatus_contMDiff` extracts, from status 1, the forward
  `ContMDiff (model n) (model m) ∞ f` (via the witness' `Diffeomorph.contMDiff`),
  and `diffeoStatus_contMDiff_symm` extracts the inverse's smoothness
  `ContMDiff (model m) (model n) ∞ d.symm` (via `Diffeomorph.contMDiff_invFun`).

  CONCRETE WITNESSES. `diffeoStatus_id` shows the identity is a diffeomorphism
  (status 1) via `Diffeomorph.refl`. `clmDiffeoStatus_eq_one` shows that any
  continuous linear equivalence on the model space induces a diffeomorphism
  (status 1) via `ContinuousLinearEquiv.toDiffeomorph`.

  CLOSURE. `Diffeomorph.trans` already gives composition of diffeomorphisms at
  the bundled level; `diffeoStatus_comp` exposes that closure at the status
  level: composing two status-1 maps yields a status-1 map.

  HONEST SCOPE. This recovers Mathlib's `Diffeomorph` (smooth isomorphism) as a
  status, rounding out the smooth-map layer: `ContMDiff` is the morphisms,
  `Diffeomorph` is the isomorphisms. It adds NO new differential-geometry
  structure beyond what Mathlib already provides.
-/

import Cred.Topology.ManifoldN
import Mathlib.Geometry.Manifold.Diffeomorph

namespace Cred

namespace DiffeoLayer

open Credence
open Classical
open scoped Manifold ContDiff
open Cred.ManifoldN (ModelSpace model)

/-! ## Graded diffeomorphism status of a map -/

section MapStatus

variable {n m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']

/-- Graded DIFFEOMORPHISM STATUS of a map `f : M → M'` between charted spaces
over the n- and m-dimensional Euclidean models, as a credence: certainty (1)
when `f` is the underlying map of some Mathlib `Diffeomorph` at the `∞` (C^∞)
order, impossibility (0) otherwise. The `if` is decided through classical choice
on the existence of a witnessing diffeomorphism. -/
noncomputable def diffeoStatus (n m : ℕ)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']
    (f : M → M') : Credence :=
  if (∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f) then 1 else 0

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are the distinct
reals `0` and `1`. Used to read the status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

/-- HEADLINE RECOVERY. The graded diffeomorphism status equals certainty (1) if
and only if `f` is the underlying map of a genuine Mathlib `Diffeomorph` at the
`∞ : WithTop ℕ∞` (C^∞) order. A faithful two-valued recovery of "f is a C^∞
diffeomorphism"; with no unbundled `IsDiffeomorph` in this Mathlib version the
witness is the bundled `Diffeomorph` itself. -/
theorem diffeoStatus_eq_one_iff (f : M → M') :
    diffeoStatus n m f = 1 ↔
      ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f := by
  unfold diffeoStatus
  by_cases h : ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The graded diffeomorphism status equals impossibility (0) exactly when `f` is
not the underlying map of any `Diffeomorph`. -/
theorem diffeoStatus_eq_zero_iff (f : M → M') :
    diffeoStatus n m f = 0 ↔
      ¬ ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f := by
  unfold diffeoStatus
  by_cases h : ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f
  · simp only [h, if_true, not_true, iff_false]
    intro ho; exact absurd ho.symm cred_zero_ne_one
  · simp only [h, if_false, not_false_iff, iff_true]

/-- The status is crisp: it takes only the values `0` or `1`, never an interior
credence. -/
theorem diffeoStatus_crisp (f : M → M') :
    diffeoStatus n m f = 0 ∨ diffeoStatus n m f = 1 := by
  unfold diffeoStatus
  by_cases h : ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞), d.toFun = f
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-! ## Smoothness both ways at status 1

A diffeomorphism is `ContMDiff` in both directions. Status 1 supplies the
witnessing `Diffeomorph`, from which we recover the forward smoothness of `f`
and the smoothness of the inverse. -/

/-- At status 1, `f` is a Mathlib `C^∞` map. We extract the witnessing
`Diffeomorph` and use `Diffeomorph.contMDiff` (the forward `contMDiff_toFun`
field), rewriting along the witness equation `d.toFun = f`. -/
theorem diffeoStatus_contMDiff {f : M → M'} (h : diffeoStatus n m f = 1) :
    ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) f := by
  obtain ⟨d, hd⟩ := (diffeoStatus_eq_one_iff f).mp h
  have : ContMDiff (model n) (model m) (∞ : WithTop ℕ∞) d.toFun := d.contMDiff_toFun
  rwa [hd] at this

/-- At status 1, the inverse of the witnessing diffeomorphism is itself a Mathlib
`C^∞` map. We extract the witnessing `Diffeomorph` and expose its inverse's
smoothness `ContMDiff (model m) (model n) ∞ d.symm` via the `contMDiff_invFun`
field (idiomatically `d.symm.contMDiff`). The map `f` is the forward direction,
so its inverse is `d.symm`. -/
theorem diffeoStatus_contMDiff_symm {f : M → M'} (h : diffeoStatus n m f = 1) :
    ∃ d : Diffeomorph (model n) (model m) M M' (∞ : WithTop ℕ∞),
      d.toFun = f ∧ ContMDiff (model m) (model n) (∞ : WithTop ℕ∞) d.symm := by
  obtain ⟨d, hd⟩ := (diffeoStatus_eq_one_iff f).mp h
  exact ⟨d, hd, d.symm.contMDiff⟩

end MapStatus

/-! ## Concrete witnesses: identity and continuous linear equivalences -/

section Concrete

variable {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]

/-- CONCRETE. The identity map is a `C^∞` diffeomorphism, so its diffeomorphism
status is certain (1). The witness is `Diffeomorph.refl (model n) M ∞`, whose
underlying map is `Equiv.refl M`, i.e. `id`. -/
theorem diffeoStatus_id : diffeoStatus n n (id : M → M) = 1 :=
  (diffeoStatus_eq_one_iff _).mpr ⟨Diffeomorph.refl (model n) M (∞ : WithTop ℕ∞), rfl⟩

end Concrete

section LinearEquiv

variable {n : ℕ}

/-- CONCRETE. Any continuous linear equivalence `e` on the n-dimensional Euclidean
model space induces a `C^∞` diffeomorphism via
`ContinuousLinearEquiv.toDiffeomorph`, so the underlying map `e` has diffeomorphism
status 1. This is the easy linear example: linear isomorphisms are smooth both
ways. The model spaces are `model n` on both sides, matching `e : E ≃L[ℝ] E`. -/
theorem clmDiffeoStatus_eq_one (e : ModelSpace n ≃L[ℝ] ModelSpace n) :
    diffeoStatus n n (e : ModelSpace n → ModelSpace n) = 1 :=
  (diffeoStatus_eq_one_iff _).mpr ⟨e.toDiffeomorph, rfl⟩

end LinearEquiv

/-! ## Closure under composition

`Diffeomorph.trans` composes diffeomorphisms at the bundled level. We expose that
closure at the status level: composing two status-1 maps yields a status-1 map,
witnessed by the `trans` of the two witnessing diffeomorphisms. -/

section Closure

variable {n m k : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelSpace n) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ModelSpace m) M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace (ModelSpace k) M'']

/-- CLOSURE. Composition preserves diffeomorphism status: if `f : M → M'` and
`g : M' → M''` are both status-1 (each the underlying map of a diffeomorphism),
then `g ∘ f` is status-1. The witness is `d.trans d'` of the two witnessing
diffeomorphisms, whose underlying map is `g ∘ f` by `Diffeomorph.coe_trans`. -/
theorem diffeoStatus_comp {f : M → M'} {g : M' → M''}
    (hf : diffeoStatus n m f = 1) (hg : diffeoStatus m k g = 1) :
    diffeoStatus n k (g ∘ f) = 1 := by
  obtain ⟨d, hd⟩ := (diffeoStatus_eq_one_iff f).mp hf
  obtain ⟨d', hd'⟩ := (diffeoStatus_eq_one_iff g).mp hg
  refine (diffeoStatus_eq_one_iff _).mpr ⟨d.trans d', ?_⟩
  have hcoe : ⇑(d.trans d') = g ∘ f := by
    rw [Diffeomorph.coe_trans]
    have hdf : ⇑d = f := hd
    have hdg : ⇑d' = g := hd'
    rw [hdf, hdg]
  exact hcoe

end Closure

end DiffeoLayer

end Cred
