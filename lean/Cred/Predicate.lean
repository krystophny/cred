/-
  Cred Part 2: Graded Predicates and Quantifiers

  Graded predicates assign credences pointwise over a domain. This file defines:
  - GradedPredicate: functions α → Credence with pointwise operations
  - Pointwise negation, conjunction, disjunction
  - De Morgan laws (pointwise)
  - credSup/credInf wrappers for quantifiers
  - Quantifier duality (value-level)
  - Classical agreement for crisp predicates
  - Russell fixed point
-/

import Cred.Basic
import Mathlib.Tactic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Cred

/-! ## Graded Predicates -/

/-- A graded predicate assigns a credence to each element of a domain. -/
def GradedPredicate (α : Type*) := α → Credence

namespace GradedPredicate

variable {α : Type*}

/-- Pointwise negation: (~P)(x) = ~P(x) -/
def neg (P : GradedPredicate α) : GradedPredicate α :=
  fun x => Credence.neg (P x)

/-- Pointwise conjunction: (P ⊗ Q)(x) = P(x) ⊗ Q(x) -/
def conj (P Q : GradedPredicate α) : GradedPredicate α :=
  fun x => (P x) ⊗ (Q x)

/-- Pointwise disjunction: (P ⊔ Q)(x) = P(x) ⊔ Q(x) -/
def disj (P Q : GradedPredicate α) : GradedPredicate α :=
  fun x => (P x) ⊔ (Q x)

/-! ### Pointwise algebraic properties -/

/-- Double negation: ~~P = P pointwise -/
@[simp] theorem neg_neg (P : GradedPredicate α) : neg (neg P) = P := by
  funext x
  exact Credence.neg_neg (P x)

/-- Conjunction is commutative pointwise -/
theorem conj_comm (P Q : GradedPredicate α) : conj P Q = conj Q P := by
  funext x
  exact Credence.conj_comm (P x) (Q x)

/-- Conjunction is associative pointwise -/
theorem conj_assoc (P Q R : GradedPredicate α) :
    conj (conj P Q) R = conj P (conj Q R) := by
  funext x
  exact Credence.conj_assoc (P x) (Q x) (R x)

/-- Disjunction is commutative pointwise -/
theorem disj_comm (P Q : GradedPredicate α) : disj P Q = disj Q P := by
  funext x
  exact Credence.disj_comm (P x) (Q x)

/-- Disjunction is associative pointwise -/
theorem disj_assoc (P Q R : GradedPredicate α) :
    disj (disj P Q) R = disj P (disj Q R) := by
  funext x
  exact Credence.disj_assoc (P x) (Q x) (R x)

/-- De Morgan: ~(P ⊗ Q) = ~P ⊔ ~Q pointwise -/
theorem de_morgan_conj (P Q : GradedPredicate α) :
    neg (conj P Q) = disj (neg P) (neg Q) := by
  funext x
  exact Credence.de_morgan_conj (P x) (Q x)

/-- De Morgan: ~(P ⊔ Q) = ~P ⊗ ~Q pointwise -/
theorem de_morgan_disj (P Q : GradedPredicate α) :
    neg (disj P Q) = conj (neg P) (neg Q) := by
  funext x
  exact Credence.de_morgan_disj (P x) (Q x)

/-! ## Quantifiers as Inf/Sup

We use wrapper functions that work directly with the underlying real values
and prove the result stays in [0,1]. The key observation: credence values
are bounded in [0,1], so the ranges are always bounded. -/

private theorem bddAbove_range_val (f : α → Credence) :
    BddAbove (Set.range (fun a => (f a).val)) :=
  ⟨1, by rintro _ ⟨a, rfl⟩; exact (f a).le_one⟩

private theorem bddBelow_range_val (f : α → Credence) :
    BddBelow (Set.range (fun a => (f a).val)) :=
  ⟨0, by rintro _ ⟨a, rfl⟩; exact (f a).nonneg⟩

/-- Supremum of credences over a nonempty type. -/
noncomputable def credSup [Nonempty α] (f : α → Credence) : Credence where
  val := iSup (fun a => (f a).val)
  nonneg := le_ciSup_of_le (bddAbove_range_val f) (Classical.arbitrary α) (f _).nonneg
  le_one := ciSup_le (fun a => (f a).le_one)

/-- Infimum of credences over a nonempty type. -/
noncomputable def credInf [Nonempty α] (f : α → Credence) : Credence where
  val := iInf (fun a => (f a).val)
  nonneg := le_ciInf (fun a => (f a).nonneg)
  le_one := ciInf_le_of_le (bddBelow_range_val f) (Classical.arbitrary α) (f _).le_one

/-- Universal quantifier: cred(∀x. P(x)) = inf_x P(x) -/
noncomputable def forall' [Nonempty α] (P : GradedPredicate α) : Credence :=
  credInf P

/-- Existential quantifier: cred(∃x. P(x)) = sup_x P(x) -/
noncomputable def exists' [Nonempty α] (P : GradedPredicate α) : Credence :=
  credSup P

/-! ### Quantifier properties -/

/-- The universal quantifier is bounded above by any instance. -/
theorem forall_le [Nonempty α] (P : GradedPredicate α) (a : α) :
    (forall' P).val ≤ (P a).val := by
  exact ciInf_le (bddBelow_range_val P) a

/-- The existential quantifier is bounded below by any instance. -/
theorem le_exists [Nonempty α] (P : GradedPredicate α) (a : α) :
    (P a).val ≤ (exists' P).val := by
  exact le_ciSup (bddAbove_range_val P) a

/-! ### Quantifier Duality

The key duality: ~(∀x. P(x)) = ∃x. ~P(x), i.e.
1 - inf_x P(x) = sup_x (1 - P(x)).

We prove this at the value level using standard real analysis. -/

/-- Quantifier duality at the value level:
    1 - inf_x P(x) = sup_x (1 - P(x)). -/
theorem quantifier_duality_val [Nonempty α] (P : GradedPredicate α) :
    1 - iInf (fun a => (P a).val) = iSup (fun a => 1 - (P a).val) := by
  have hbdd_below := bddBelow_range_val P
  have hbdd_above : BddAbove (Set.range (fun a => 1 - (P a).val)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    simp only []
    linarith [(P a).nonneg]
  apply le_antisymm
  · have h_le : 1 - iSup (fun a => 1 - (P a).val) ≤ iInf (fun a => (P a).val) :=
      le_ciInf (fun a => by have := le_ciSup hbdd_above a; linarith)
    linarith
  · exact ciSup_le (fun a => by have := ciInf_le hbdd_below a; linarith)

/-! ### Classical Agreement

For crisp predicates (range ⊆ {0,1}), inf = ∀ and sup = ∃. -/

/-- A predicate is crisp when its range is contained in {0,1}. -/
def IsCrisp (P : GradedPredicate α) : Prop :=
  ∀ x, P x = 0 ∨ P x = 1

/-- For a crisp predicate, the infimum is 0 iff some element maps to 0. -/
theorem crisp_inf_zero_iff [Nonempty α] (P : GradedPredicate α) (hcrisp : IsCrisp P) :
    iInf (fun a => (P a).val) = 0 ↔ ∃ a, P a = 0 := by
  constructor
  · intro hinf
    by_contra h
    push_neg at h
    have hall : ∀ a, P a = 1 := fun a => (hcrisp a).resolve_left (h a)
    have : iInf (fun a => (P a).val) = 1 := by
      apply le_antisymm
      · exact ciInf_le_of_le (bddBelow_range_val P) (Classical.arbitrary α)
          (by rw [hall (Classical.arbitrary α)]; simp)
      · exact le_ciInf (fun a => by rw [hall a]; simp)
    linarith
  · intro ⟨a, ha⟩
    apply le_antisymm
    · exact ciInf_le_of_le (bddBelow_range_val P) a (by rw [ha]; simp)
    · exact le_ciInf (fun b => (P b).nonneg)

/-- For a crisp predicate, the supremum is 1 iff some element maps to 1. -/
theorem crisp_sup_one_iff [Nonempty α] (P : GradedPredicate α) (hcrisp : IsCrisp P) :
    iSup (fun a => (P a).val) = 1 ↔ ∃ a, P a = 1 := by
  constructor
  · intro hsup
    by_contra h
    push_neg at h
    have hall : ∀ a, P a = 0 := fun a => (hcrisp a).resolve_right (h a)
    have : iSup (fun a => (P a).val) = 0 := by
      apply le_antisymm
      · exact ciSup_le (fun a => by rw [hall a]; simp)
      · exact le_ciSup_of_le (bddAbove_range_val P) (Classical.arbitrary α)
          (by rw [hall (Classical.arbitrary α)]; simp)
    linarith
  · intro ⟨a, ha⟩
    apply le_antisymm
    · exact ciSup_le (fun b => (P b).le_one)
    · exact le_ciSup_of_le (bddAbove_range_val P) a (by rw [ha]; simp)

/-! ## Russell Fixed Point

Russell's predicate R(x) = ~(x(x)) applied to itself gives R(R) = 1/2.
We encode this using Part 1's liar_fixed_point. -/

/-- The Russell fixed-point theorem: any self-referential negation yields 1/2.
    If c = ~c (the abstract Russell equation), then c = 1/2. -/
theorem russell_fixed_point (c : Credence) (h : c = Credence.neg c) :
    c = Credence.half :=
  Credence.neg_fixed_point_unique c h.symm

end GradedPredicate

end Cred
