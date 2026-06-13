/-
  Cred Topology: Graded Lie Group Layer

  This layer reports Mathlib's smooth-group-manifold structure as credence
  STATUSES. A group/additive-group `G` that is simultaneously a manifold over a
  model-with-corners `I` (at the C^∞ order `∞ : WithTop ℕ∞`) is a Lie group when
  the group operations are smooth. We grade three facts:

    1. WHETHER G IS A LIE GROUP. `lieGroupStatus` (multiplicative) and
       `lieAddGroupStatus` (additive) are `1` exactly when Mathlib's `LieGroup I n G`
       resp. `LieAddGroup I n G` holds. `lieGroupStatus_eq_one_iff` and
       `lieAddGroupStatus_eq_one_iff` recover the underlying mathlib proposition.

    2. WHETHER THE OPERATIONS ARE SMOOTH. For the carrier `EuclideanSpace ℝ (Fin n)`
       (the additive group where the instance `instNormedSpaceLieAddGroup` makes
       everything automatic), `groupAddStatus_eq_one` records that addition is
       `ContMDiff` and `groupNegStatus_eq_one` that negation is `ContMDiff`, each
       with an iff-recovery to the mathlib smoothness proposition.

    3. WHETHER TRANSLATION IS SMOOTH. `leftAddTransStatus_eq_one` /
       `rightAddTransStatus_eq_one` record that left/right translation on the
       Euclidean additive group is `ContMDiff` (via `contMDiff_add_left` /
       `contMDiff_add_right`, which need only `ContMDiffAdd`).

  THE CONCRETE MODEL. The Euclidean additive group `EuclideanSpace ℝ (Fin n)` with
  the self model `𝓘(ℝ, EuclideanSpace ℝ (Fin n))` is a Lie additive group at every
  order via Mathlib's `instNormedSpaceLieAddGroup`. `lieAddGroupStatus_model_space`
  discharges status `1` with no carried assumption.

  Each status is crisp: it takes only `0` or `1`.

  HONEST SCOPE. This recovers Mathlib's `LieGroup` / `LieAddGroup` and the
  smoothness of the group operations (multiplication/addition, inversion/negation,
  translation) as statuses, for the Euclidean additive group and for an abstract
  `G` carrying the needed typeclass instances. It does NOT build the Lie algebra
  bracket, the exponential map, or representation theory — those are future cuts
  (and partly upstream).
-/

import Cred.Topology.ManifoldN
import Mathlib.Geometry.Manifold.Algebra.LieGroup

namespace Cred

namespace LieLayer

open Credence
open Classical
open scoped Manifold ContDiff
open Cred.ManifoldN (ModelSpace model)

/-- `(0 : Credence)` and `(1 : Credence)` differ: their `.val`s are the distinct
reals `0` and `1`. Used to read each status back off the `if`. -/
theorem cred_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := congrArg Credence.val h
  exact zero_ne_one this

/-! ## Lie group status (abstract, multiplicative)

For a group `G` that is a charted space over `H` with model `I`, the Lie-group
status is `1` exactly when Mathlib's `LieGroup I n G` holds at the C^∞ order. -/

section LieGroupStatus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]

/-- Graded STATUS that `G` is a Lie group for the model `I` at the C^∞ order, as a
credence: certainty (1) when Mathlib's `LieGroup I ∞ G` holds, impossibility (0)
otherwise. -/
noncomputable def lieGroupStatus : Credence :=
  if LieGroup I (∞ : WithTop ℕ∞) G then 1 else 0

variable {I G}

/-- HEADLINE RECOVERY (multiplicative). The Lie-group status equals certainty (1)
if and only if `G` is a genuine Mathlib `LieGroup` for `I` at the C^∞ order. -/
theorem lieGroupStatus_eq_one_iff :
    lieGroupStatus I G = 1 ↔ LieGroup I (∞ : WithTop ℕ∞) G := by
  unfold lieGroupStatus
  by_cases h : LieGroup I (∞ : WithTop ℕ∞) G
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The Lie-group status is crisp: it takes only `0` or `1`. -/
theorem lieGroupStatus_crisp :
    lieGroupStatus I G = 0 ∨ lieGroupStatus I G = 1 := by
  unfold lieGroupStatus
  by_cases h : LieGroup I (∞ : WithTop ℕ∞) G
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- With a `LieGroup` instance in scope, the status is certain. -/
theorem lieGroupStatus_eq_one [LieGroup I (∞ : WithTop ℕ∞) G] :
    lieGroupStatus I G = 1 :=
  lieGroupStatus_eq_one_iff.mpr ‹_›

end LieGroupStatus

/-! ## Lie additive group status (abstract, additive)

The additive dual: status `1` exactly when Mathlib's `LieAddGroup I n G` holds. -/

section LieAddGroupStatus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  (G : Type*) [AddGroup G] [TopologicalSpace G] [ChartedSpace H G]

/-- Graded STATUS that `G` is a Lie additive group for the model `I` at the C^∞
order, as a credence: certainty (1) when Mathlib's `LieAddGroup I ∞ G` holds,
impossibility (0) otherwise. -/
noncomputable def lieAddGroupStatus : Credence :=
  if LieAddGroup I (∞ : WithTop ℕ∞) G then 1 else 0

variable {I G}

/-- HEADLINE RECOVERY (additive). The Lie-add-group status equals certainty (1)
if and only if `G` is a genuine Mathlib `LieAddGroup` for `I` at the C^∞ order. -/
theorem lieAddGroupStatus_eq_one_iff :
    lieAddGroupStatus I G = 1 ↔ LieAddGroup I (∞ : WithTop ℕ∞) G := by
  unfold lieAddGroupStatus
  by_cases h : LieAddGroup I (∞ : WithTop ℕ∞) G
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- The Lie-add-group status is crisp: it takes only `0` or `1`. -/
theorem lieAddGroupStatus_crisp :
    lieAddGroupStatus I G = 0 ∨ lieAddGroupStatus I G = 1 := by
  unfold lieAddGroupStatus
  by_cases h : LieAddGroup I (∞ : WithTop ℕ∞) G
  · exact Or.inr (by simp only [h, if_true])
  · exact Or.inl (by simp only [h, if_false])

/-- With a `LieAddGroup` instance in scope, the status is certain. -/
theorem lieAddGroupStatus_eq_one [LieAddGroup I (∞ : WithTop ℕ∞) G] :
    lieAddGroupStatus I G = 1 :=
  lieAddGroupStatus_eq_one_iff.mpr ‹_›

end LieAddGroupStatus

/-! ## Concrete instance: the Euclidean additive group is a Lie additive group

`EuclideanSpace ℝ (Fin n)` is a normed space over `ℝ`, so Mathlib's
`instNormedSpaceLieAddGroup` makes it a `LieAddGroup` for the self model
`𝓘(ℝ, EuclideanSpace ℝ (Fin n))` at every order. No assumption is carried. -/

/-- The Euclidean additive group `EuclideanSpace ℝ (Fin n)` is a Mathlib Lie
additive group for the self model at the C^∞ order: status certain, discharged by
`instNormedSpaceLieAddGroup` with no carried hypothesis. -/
theorem lieAddGroupStatus_model_space (n : ℕ) :
    lieAddGroupStatus (model n) (ModelSpace n) = 1 :=
  lieAddGroupStatus_eq_one_iff.mpr inferInstance

/-! ## Smooth group operations on the Euclidean additive group

For `E := EuclideanSpace ℝ (Fin n)` with the self model, addition and negation are
`ContMDiff`. The instance chain is automatic, so the statuses are certain. -/

section EuclideanOps

variable {n : ℕ}

/-- Graded STATUS that addition on the Euclidean additive group is `C^∞`: certainty
(1) when the pointwise sum map on the product manifold is `ContMDiff` at the C^∞
order, impossibility (0) otherwise. -/
noncomputable def groupAddStatus (n : ℕ) : Credence :=
  if ContMDiff ((model n).prod (model n)) (model n) (∞ : WithTop ℕ∞)
      (fun p : ModelSpace n × ModelSpace n => p.1 + p.2) then 1 else 0

/-- Recovery: the addition status equals certainty (1) iff addition on the
Euclidean additive group is `ContMDiff`. -/
theorem groupAddStatus_eq_one_iff :
    groupAddStatus n = 1 ↔
      ContMDiff ((model n).prod (model n)) (model n) (∞ : WithTop ℕ∞)
        (fun p : ModelSpace n × ModelSpace n => p.1 + p.2) := by
  unfold groupAddStatus
  by_cases h : ContMDiff ((model n).prod (model n)) (model n) (∞ : WithTop ℕ∞)
      (fun p : ModelSpace n × ModelSpace n => p.1 + p.2)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- Addition on the Euclidean additive group is `C^∞`, so its status is certain.
Discharged through Mathlib's `contMDiff_add` for the automatic `ContMDiffAdd`
instance. -/
theorem groupAddStatus_eq_one : groupAddStatus n = 1 :=
  groupAddStatus_eq_one_iff.mpr (contMDiff_add (model n) (∞ : WithTop ℕ∞))

/-- The addition status is crisp. -/
theorem groupAddStatus_crisp : groupAddStatus n = 0 ∨ groupAddStatus n = 1 :=
  Or.inr groupAddStatus_eq_one

/-- Graded STATUS that negation on the Euclidean additive group is `C^∞`. -/
noncomputable def groupNegStatus (n : ℕ) : Credence :=
  if ContMDiff (model n) (model n) (∞ : WithTop ℕ∞)
      (fun x : ModelSpace n => -x) then 1 else 0

/-- Recovery: the negation status equals certainty (1) iff negation on the
Euclidean additive group is `ContMDiff`. -/
theorem groupNegStatus_eq_one_iff :
    groupNegStatus n = 1 ↔
      ContMDiff (model n) (model n) (∞ : WithTop ℕ∞)
        (fun x : ModelSpace n => -x) := by
  unfold groupNegStatus
  by_cases h : ContMDiff (model n) (model n) (∞ : WithTop ℕ∞)
      (fun x : ModelSpace n => -x)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- Negation on the Euclidean additive group is `C^∞`, so its status is certain.
Discharged through Mathlib's `contMDiff_neg` for the automatic `LieAddGroup`
instance. -/
theorem groupNegStatus_eq_one : groupNegStatus n = 1 :=
  groupNegStatus_eq_one_iff.mpr (contMDiff_neg (model n) (∞ : WithTop ℕ∞))

/-- The negation status is crisp. -/
theorem groupNegStatus_crisp : groupNegStatus n = 0 ∨ groupNegStatus n = 1 :=
  Or.inr groupNegStatus_eq_one

/-! ## Smooth translation on the Euclidean additive group

Left and right translation use only addition, so `contMDiff_add_left` /
`contMDiff_add_right` (needing only `ContMDiffAdd`) make them `C^∞`. -/

/-- Graded STATUS that left translation `a + ·` on the Euclidean additive group is
`C^∞`. -/
noncomputable def leftAddTransStatus (n : ℕ) (a : ModelSpace n) : Credence :=
  if ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (a + ·) then 1 else 0

/-- Recovery: left-translation status equals certainty (1) iff `a + ·` is
`ContMDiff`. -/
theorem leftAddTransStatus_eq_one_iff (a : ModelSpace n) :
    leftAddTransStatus n a = 1 ↔
      ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (a + ·) := by
  unfold leftAddTransStatus
  by_cases h : ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (a + ·)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- Left translation on the Euclidean additive group is `C^∞`, so its status is
certain. Discharged through Mathlib's `contMDiff_add_left`. -/
theorem leftAddTransStatus_eq_one (a : ModelSpace n) : leftAddTransStatus n a = 1 :=
  (leftAddTransStatus_eq_one_iff a).mpr contMDiff_add_left

/-- The left-translation status is crisp. -/
theorem leftAddTransStatus_crisp (a : ModelSpace n) :
    leftAddTransStatus n a = 0 ∨ leftAddTransStatus n a = 1 :=
  Or.inr (leftAddTransStatus_eq_one a)

/-- Graded STATUS that right translation `· + a` on the Euclidean additive group is
`C^∞`. -/
noncomputable def rightAddTransStatus (n : ℕ) (a : ModelSpace n) : Credence :=
  if ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (· + a) then 1 else 0

/-- Recovery: right-translation status equals certainty (1) iff `· + a` is
`ContMDiff`. -/
theorem rightAddTransStatus_eq_one_iff (a : ModelSpace n) :
    rightAddTransStatus n a = 1 ↔
      ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (· + a) := by
  unfold rightAddTransStatus
  by_cases h : ContMDiff (model n) (model n) (∞ : WithTop ℕ∞) (· + a)
  · simp only [h, if_true, iff_true]
  · simp only [h, if_false, iff_false]
    intro hz; exact absurd hz cred_zero_ne_one

/-- Right translation on the Euclidean additive group is `C^∞`, so its status is
certain. Discharged through Mathlib's `contMDiff_add_right`. -/
theorem rightAddTransStatus_eq_one (a : ModelSpace n) : rightAddTransStatus n a = 1 :=
  (rightAddTransStatus_eq_one_iff a).mpr contMDiff_add_right

/-- The right-translation status is crisp. -/
theorem rightAddTransStatus_crisp (a : ModelSpace n) :
    rightAddTransStatus n a = 0 ∨ rightAddTransStatus n a = 1 :=
  Or.inr (rightAddTransStatus_eq_one a)

end EuclideanOps

end LieLayer

end Cred
