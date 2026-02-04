/-
  Cred Part 2: Valuations

  A valuation maps propositions to credences, providing the interpretation
  layer that Part 1 deliberately omits. This file defines:
  - Valuation structure with complement preservation
  - Independent valuations (homomorphisms for conj/disj)
  - Collapse composition: composing a valuation with the three-valued collapse
  - Frechet bounds lifted to valuations
-/

import Cred.Basic

namespace Cred

/-! ## Complement-Preserving Valuation

A valuation `v` is complement-preserving when equipped with a negation on
propositions `σ : α → α` such that `v(σ a) = ~v(a)`. We model this as
a bundled structure. -/

/-- A complement-preserving valuation over a type with propositional negation. -/
structure CpValuation (α : Type*) where
  val : α → Credence
  propNeg : α → α
  complement : ∀ a, val (propNeg a) = Credence.neg (val a)

namespace CpValuation

variable {α : Type*}

/-- Applying propositional negation twice preserves the credence. -/
theorem complement_involutive (v : CpValuation α) (a : α)
    (h_inv : v.propNeg (v.propNeg a) = a) :
    v.val (v.propNeg (v.propNeg a)) = v.val a := by
  rw [h_inv]

/-- A constant valuation assigning `c` to everything, with identity negation.
    Only valid when `c = half` (the negation fixed point). -/
noncomputable def constant_half (α : Type*) : CpValuation α where
  val := fun _ => Credence.half
  propNeg := id
  complement := by
    intro a
    simp only [id]
    exact Credence.liar_fixed_point.symm

end CpValuation

/-! ## Independent Valuation

An independent valuation treats conjunction as product and disjunction as
De Morgan dual. This makes the valuation a homomorphism for the connective
algebra. -/

/-- An independent valuation is a complement-preserving valuation where
    conjunction maps to product and disjunction maps to De Morgan dual. -/
structure IndepValuation (α : Type*) extends CpValuation α where
  propConj : α → α → α
  propDisj : α → α → α
  conj_compat : ∀ a b, toCpValuation.val (propConj a b) =
    toCpValuation.val a ⊗ toCpValuation.val b
  disj_compat : ∀ a b, toCpValuation.val (propDisj a b) =
    toCpValuation.val a ⊔ toCpValuation.val b

namespace IndepValuation

variable {α : Type*}

/-- Under an independent valuation, conjunction is commutative. -/
theorem conj_comm (v : IndepValuation α) (a b : α) :
    v.val (v.propConj a b) = v.val (v.propConj b a) := by
  rw [v.conj_compat, v.conj_compat, Credence.conj_comm]

/-- Under an independent valuation, disjunction is commutative. -/
theorem disj_comm (v : IndepValuation α) (a b : α) :
    v.val (v.propDisj a b) = v.val (v.propDisj b a) := by
  rw [v.disj_compat, v.disj_compat, Credence.disj_comm]

/-- The idempotence problem: v(A ∧ A) = v(A)^2 ≠ v(A) in general. -/
theorem conj_not_idempotent (v : IndepValuation α) (a : α)
    (h : v.val a = Credence.half) :
    v.val (v.propConj a a) ≠ v.val a := by
  rw [v.conj_compat, h]
  intro heq
  have habs : (Credence.half ⊗ Credence.half).val = Credence.half.val :=
    congrArg Credence.val heq
  simp [Credence.conj_val, Credence.half_val] at habs

end IndepValuation

/-! ## Joint-Parametrized Valuation

A joint-parametrized valuation supplies joint credences externally,
connecting to Part 1's conditioning structure. -/

/-- A joint-parametrized valuation supplies joints as external data. -/
structure JointValuation (α : Type*) extends CpValuation α where
  joint : α → α → Credence
  joint_le_marginal_left : ∀ a b, (joint a b).val ≤ (toCpValuation.val a).val
  joint_le_marginal_right : ∀ a b, (joint a b).val ≤ (toCpValuation.val b).val

namespace JointValuation

variable {α : Type*}

/-- The joint is bounded by the Frechet upper bound. -/
theorem frechet_upper_bound (v : JointValuation α) (a b : α) :
    (v.joint a b).val ≤ (v.val a).val ∧
    (v.joint a b).val ≤ (v.val b).val :=
  ⟨v.joint_le_marginal_left a b, v.joint_le_marginal_right a b⟩

/-- When both marginals are positive, conditioning is uniquely determined. -/
noncomputable def conditioning (v : JointValuation α) (a b : α)
    (hb : 0 < (v.val b).val) :
    Credence.Conditioning (v.joint a b) (v.val b) :=
  Credence.conditioning_mk (v.joint a b) (v.val b) hb
    (v.joint_le_marginal_right a b)

end JointValuation

/-! ## Collapse Composition

Composing a valuation with the three-valued collapse gives a Kleene valuation.
The collapse homomorphism (Part 1) ensures this preserves the connective algebra. -/

/-- Compose a credence-valued function with the collapse to get a three-valued function. -/
noncomputable def collapseValuation (f : α → Credence) : α → ThreeVal :=
  fun a => collapse (f a)

/-- Collapse of a complement-preserving valuation preserves ThreeVal negation. -/
theorem collapse_val_neg (v : CpValuation α) (a : α) :
    collapse (v.val (v.propNeg a)) = ThreeVal.neg (collapse (v.val a)) := by
  rw [v.complement]
  exact collapse_neg (v.val a)

/-- Collapse of an independent valuation preserves ThreeVal conjunction. -/
theorem collapse_val_conj (v : IndepValuation α) (a b : α) :
    collapse (v.val (v.propConj a b)) =
    ThreeVal.conj (collapse (v.val a)) (collapse (v.val b)) := by
  rw [v.conj_compat]
  exact collapse_conj (v.val a) (v.val b)

/-- Collapse of an independent valuation preserves ThreeVal disjunction. -/
theorem collapse_val_disj (v : IndepValuation α) (a b : α) :
    collapse (v.val (v.propDisj a b)) =
    ThreeVal.disj (collapse (v.val a)) (collapse (v.val b)) := by
  rw [v.disj_compat]
  exact collapse_disj (v.val a) (v.val b)

/-! ## Frechet Bounds on Valuations

Lifting Part 1's Frechet bounds to valuations: given marginals v(A) and v(B),
the joint v(A ∧ B) is constrained to the Frechet-Hoeffding interval. -/

/-- Any joint valuation automatically satisfies the Frechet upper bound. -/
theorem joint_frechet_upper (v : JointValuation α) (a b : α) :
    (v.joint a b).val ≤ min (v.val a).val (v.val b).val := by
  exact le_min (v.joint_le_marginal_left a b) (v.joint_le_marginal_right a b)

/-- If complement non-negativity holds, the Frechet lower bound applies. -/
theorem joint_frechet_lower (v : JointValuation α) (a b : α)
    (h : 0 ≤ 1 - (v.val a).val - (v.val b).val + (v.joint a b).val) :
    (v.val a).val + (v.val b).val - 1 ≤ (v.joint a b).val := by
  linarith

/-! ## Independent Valuation as Homomorphism -/

/-- If v(A ∧ B) = v(A) ⊗ v(B) for all A, B, then v is a homomorphism
    for conjunction. This is definitional for IndepValuation. -/
theorem indep_is_conj_homomorphism (v : IndepValuation α) (a b : α) :
    v.val (v.propConj a b) = v.val a ⊗ v.val b :=
  v.conj_compat a b

end Cred
