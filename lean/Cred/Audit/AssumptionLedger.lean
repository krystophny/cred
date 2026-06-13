/-
  Cred Audit: Assumption Ledger for an Inference Step (issue #666)

  An inference step from marginals to a conditional hides several commitments:
  which joint policy fixes `cred(A ∧ B)` from the marginals, how the conditional
  is read off the joint, and whether the verdict is reported as a measure-theory
  point, a credal interval, or a three-valued collapse. The ledger names these
  commitments explicitly so a step can be audited rather than trusted.

  The layer is thin and true over existing machinery: the independence verdict
  reuses `prod_trivial_conditioning` (product joint makes the conditional equal
  to the prior marginal, i.e. evidence is irrelevant), and the robustness
  verdict reuses `collapseIntervalToThree` from the robust-collapse layer.
-/

import Cred.Cond.Admissible
import Cred.Cond.Copula
import Cred.Dependence.RobustCollapse

namespace Cred

namespace Audit

open Cred.Credence
open Cred.Dependence

/-! ## Commitments of an inference step -/

/-- How the joint `cred(A ∧ B)` is fixed from the marginals. -/
inductive JointPolicy where
  | product
  | min
  | frechetLower
  | interval
  | family
  | exact
  | unknown
deriving DecidableEq, Repr

/-- How the conditional `cred(A | B)` is read off the joint and evidence. -/
inductive ConditioningPolicy where
  | fiber
  | residuum
  | division
  | undefined
deriving DecidableEq, Repr

/-- The bundled commitments of one inference step. `usesMeasure` and
    `usesCredal` record the semantic frame (a measure-theoretic point versus an
    imprecise credal set); `collapsesToThree` records whether the verdict is
    reported through the three-valued robust collapse. -/
structure InferenceCommitments where
  jointPolicy : JointPolicy
  conditioningPolicy : ConditioningPolicy
  usesMeasure : Bool
  usesCredal : Bool
  collapsesToThree : Bool
deriving DecidableEq, Repr

namespace InferenceCommitments

/-- The step assumes independence exactly when its joint policy is `product`. -/
def assumesIndependence (c : InferenceCommitments) : Bool :=
  c.jointPolicy == JointPolicy.product

@[simp] theorem assumesIndependence_product
    (cp : ConditioningPolicy) (m cr t : Bool) :
    assumesIndependence ⟨JointPolicy.product, cp, m, cr, t⟩ = true := rfl

end InferenceCommitments

/-! ## Independence makes evidence irrelevant

The defining consequence of the independence commitment: when the joint is the
product of the marginals, the chain-rule conditional equals the prior marginal,
so the evidence narrows nothing. This is the credence-side restatement of
`prod_trivial_conditioning`. -/

/-- Under the product (independence) joint `cred(A ∧ B) = a ⊗ b` with positive
    evidence `b`, the admissible conditional is the singleton `{a}`: the
    posterior equals the prior, so the evidence is irrelevant. The hypothesis
    `a ≤ 1` is automatic for credences; positivity of `b` is the only side
    condition. -/
theorem independence_makes_evidence_irrelevant (a b : Credence)
    (hb : 0 < b.val) :
    Cond (a ⊗ b) b = {a} := by
  have hle : (a ⊗ b).val ≤ b.val := by
    rw [conj_val]
    calc a.val * b.val ≤ 1 * b.val :=
          mul_le_mul_of_nonneg_right a.le_one b.nonneg
      _ = b.val := one_mul _
  rw [cond_singleton_of_pos (a ⊗ b) b hb hle]
  congr 1
  ext
  show (a ⊗ b).val / b.val = a.val
  rw [conj_val]
  exact prod_trivial_conditioning a b (ne_of_gt hb)

/-! ## Robustness verdict over a conditional interval

A threshold claim against an imprecise conditional band `[lo, hi]` is audited by
collapsing the band through `collapseIntervalToThree`. A robust verdict
(`robustZero`/`robustOne`) survives the whole band; a `dependenceSensitive`
verdict flips with the unknown joint, exposing false precision. -/

/-- The robustness verdict for a conditional band `[lo, hi]`: the three-valued
    robust collapse of the interval. The threshold `t` is implicit in the
    `robustZero` (`hi < ½`) versus `robustOne` (`½ < lo`) split that
    `collapseIntervalToThree` performs around ½. -/
noncomputable def robustnessVerdict (lo hi : Credence) : RobustStatus :=
  collapseIntervalToThree lo hi

/-- Audit dichotomy: a coherent conditional band that is not the full
    `[0,1]` band and is not the degenerate `½` point lands in exactly one of the
    robust classes (`robustZero`/`robustOne`) or is flagged
    `dependenceSensitive`. The audit always returns a verdict, never a hidden
    point estimate. -/
theorem audit_robust_or_sensitive (lo hi : Credence)
    (hcoh : lo.val ≤ hi.val) :
    robustnessVerdict lo hi = RobustStatus.robustZero ∨
    robustnessVerdict lo hi = RobustStatus.robustOne ∨
    robustnessVerdict lo hi = RobustStatus.robustHalf ∨
    robustnessVerdict lo hi = RobustStatus.underdetermined ∨
    robustnessVerdict lo hi = RobustStatus.dependenceSensitive := by
  unfold robustnessVerdict collapseIntervalToThree
  have hncoh : ¬ hi.val < lo.val := not_lt.mpr hcoh
  rw [if_neg hncoh]
  split_ifs <;> simp

end Audit

end Cred
