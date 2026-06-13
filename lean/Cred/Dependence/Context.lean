/-
  Cred Dependence: Joint-Context Layer (issue #633)

  Dependence is supplied data, not a derived t-norm. A joint context attaches
  an explicit joint credence to each pair of propositions, alongside the
  marginals. This mirrors `JointValuation` (Cred.Valuation) but isolates the
  dependence layer so the conditioning, robust-collapse, and worked-example
  modules can share one vocabulary.

  Three levels of commitment:
  - `ExactJointContext`: a single, fully specified joint per pair.
  - `CoherentJointContext`: an exact context carrying Fréchet upper- and
    lower-bound witnesses (the lower bound is an explicit field, as in
    `JointValuation`, since complement non-negativity is extra data).
  - `IntervalJointContext`: a joint *band* `[lo, hi]` per pair, the imprecise
    case driving robust collapse and dependence sensitivity.

  A `JointFamily` is a predicate on exact contexts: the set of exact joints a
  given dependence policy admits. A copula is ONE optional implementation of a
  JointFamily (a value-level coupling), not the primitive dependence layer.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Dependence

open Cred.Credence

/-! ## Exact joint context -/

/-- An exact joint context: marginal `value` for each proposition and an
    explicit `joint` credence for each pair. The joint is supplied data, not
    computed from the marginals by any t-norm. -/
structure ExactJointContext (α : Type*) where
  value : α → Credence
  joint : α → α → Credence

namespace ExactJointContext

variable {α : Type*}

/-- The product (independence) joint reading: `joint a b = value a ⊗ value b`. -/
def IsProduct (Γ : ExactJointContext α) : Prop :=
  ∀ a b, Γ.joint a b = Γ.value a ⊗ Γ.value b

/-- The min (maximal positive dependence) joint reading on values. -/
def IsMin (Γ : ExactJointContext α) : Prop :=
  ∀ a b, (Γ.joint a b).val = min (Γ.value a).val (Γ.value b).val

end ExactJointContext

/-! ## Coherent joint context

A coherent context bundles the Fréchet upper bound (which the chain rule
forces on its own) with an explicit Fréchet lower-bound witness
(`joint ≥ value a + value b - 1`, via complement non-negativity). The lower
bound is a separate field because it is not implied by marginals plus
nonnegativity alone — same pattern as `JointValuation`. -/

/-- An exact joint context together with Fréchet upper- and lower-bound
    witnesses on every pair. -/
structure CoherentJointContext (α : Type*) extends ExactJointContext α where
  joint_le_left : ∀ a b,
    (toExactJointContext.joint a b).val ≤ (toExactJointContext.value a).val
  joint_le_right : ∀ a b,
    (toExactJointContext.joint a b).val ≤ (toExactJointContext.value b).val
  frechet_lower : ∀ a b,
    (toExactJointContext.value a).val + (toExactJointContext.value b).val - 1
      ≤ (toExactJointContext.joint a b).val

namespace CoherentJointContext

variable {α : Type*}

/-- The joint sits at or below the Fréchet upper bound `min(a, b)`. -/
theorem joint_le_min (Γ : CoherentJointContext α) (a b : α) :
    (Γ.joint a b).val ≤ min (Γ.value a).val (Γ.value b).val :=
  le_min (Γ.joint_le_left a b) (Γ.joint_le_right a b)

/-- The joint sits at or above the Fréchet lower bound `max(a + b - 1, 0)`. -/
theorem joint_ge_frechet_lower (Γ : CoherentJointContext α) (a b : α) :
    max ((Γ.value a).val + (Γ.value b).val - 1) 0 ≤ (Γ.joint a b).val :=
  max_le (Γ.frechet_lower a b) (Γ.joint a b).nonneg

/-- When the right marginal is positive, a coherent context yields a unique
    admissible conditional (the chain-rule solution `joint / value b`). -/
noncomputable def conditioning (Γ : CoherentJointContext α) (a b : α)
    (hb : 0 < (Γ.value b).val) :
    Conditioning (Γ.joint a b) (Γ.value b) :=
  conditioning_mk (Γ.joint a b) (Γ.value b) hb (Γ.joint_le_right a b)

end CoherentJointContext

/-! ## Interval joint context

The imprecise case: each pair carries a joint *band* `[lo, hi]`. This is the
input to robust collapse and to dependence-sensitivity analysis. -/

/-- A joint band per pair: lower and upper joint credences with `lo ≤ hi`. -/
structure IntervalJointContext (α : Type*) where
  value : α → Credence
  lo : α → α → Credence
  hi : α → α → Credence
  lo_le_hi : ∀ a b, (lo a b).val ≤ (hi a b).val

namespace IntervalJointContext

variable {α : Type*}

/-- The band has nonnegative width. -/
theorem width_nonneg (Γ : IntervalJointContext α) (a b : α) :
    0 ≤ (Γ.hi a b).val - (Γ.lo a b).val := by
  have := Γ.lo_le_hi a b
  linarith

/-- A degenerate band (`lo = hi`) collapses to an exact context. -/
def toExact (Γ : IntervalJointContext α) (_h : ∀ a b, Γ.lo a b = Γ.hi a b) :
    ExactJointContext α where
  value := Γ.value
  joint := Γ.hi

end IntervalJointContext

/-! ## Joint families

A `JointFamily` is a predicate carving out the exact contexts a dependence
policy admits. A copula is one optional value-level implementation of a
JointFamily, not the primitive dependence layer: the primitive is the
supplied joint itself. -/

/-- A dependence policy as a predicate on exact joint contexts. -/
def JointFamily (α : Type*) := ExactJointContext α → Prop

namespace JointFamily

variable {α : Type*}

/-- The family of independence (product-joint) contexts. -/
def independence : JointFamily α := fun Γ => Γ.IsProduct

/-- The family of max-dependence (min-joint) contexts. -/
def maxDependence : JointFamily α := fun Γ => Γ.IsMin

/-- The trivial family admitting every coherent supplied joint. -/
def any : JointFamily α := fun _ => True

end JointFamily

/-! ## Constructors

Each builds an `ExactJointContext` from marginals plus the data needed to fix
the joint. The min and Fréchet-lower constructors take the marginals as the
context's `value` and read off the corresponding joint band endpoint. -/

variable {α : Type*}

/-- Independence: `joint a b = value a ⊗ value b`. -/
def productJoint (value : α → Credence) : ExactJointContext α where
  value := value
  joint := fun a b => value a ⊗ value b

/-- The product constructor is in the independence family. -/
theorem productJoint_isProduct (value : α → Credence) :
    (productJoint value).IsProduct := fun _ _ => rfl

/-- Max positive dependence: `joint a b = min(value a, value b)` as a
    credence. The min of two credences is again a credence. -/
def minCredence (x y : Credence) : Credence where
  val := min x.val y.val
  nonneg := le_min x.nonneg y.nonneg
  le_one := le_trans (min_le_left _ _) x.le_one

@[simp] theorem minCredence_val (x y : Credence) :
    (minCredence x y).val = min x.val y.val := rfl

/-- Max positive dependence joint: `joint a b = minCredence (value a) (value b)`. -/
def minJoint (value : α → Credence) : ExactJointContext α where
  value := value
  joint := fun a b => minCredence (value a) (value b)

/-- The min constructor is in the max-dependence family. -/
theorem minJoint_isMin (value : α → Credence) :
    (minJoint value).IsMin := fun _ _ => rfl

/-- Minimal overlap: the Fréchet lower joint `max(a + b - 1, 0)`, again a
    credence (it lies in `[0, min(a,b)] ⊆ [0,1]`). -/
def frechetLowerCredence (x y : Credence) : Credence where
  val := max (x.val + y.val - 1) 0
  nonneg := le_max_right _ _
  le_one := by
    apply max_le
    · have := x.le_one; have := y.le_one; linarith
    · exact zero_le_one

@[simp] theorem frechetLowerCredence_val (x y : Credence) :
    (frechetLowerCredence x y).val = max (x.val + y.val - 1) 0 := rfl

/-- Minimal-overlap joint: `joint a b = frechetLowerCredence (value a) (value b)`. -/
def frechetLowerJoint (value : α → Credence) : ExactJointContext α where
  value := value
  joint := fun a b => frechetLowerCredence (value a) (value b)

/-- An arbitrary coherent joint: marginals plus a supplied joint function. The
    caller chooses the joint freely; coherence (Fréchet bounds) is recorded
    separately when wrapping into a `CoherentJointContext`. -/
def suppliedJoint (value : α → Credence) (joint : α → α → Credence) :
    ExactJointContext α where
  value := value
  joint := joint

@[simp] theorem suppliedJoint_value (value : α → Credence) (joint : α → α → Credence)
    (a : α) : (suppliedJoint value joint).value a = value a := rfl

@[simp] theorem suppliedJoint_joint (value : α → Credence) (joint : α → α → Credence)
    (a b : α) : (suppliedJoint value joint).joint a b = joint a b := rfl

end Dependence

end Cred
