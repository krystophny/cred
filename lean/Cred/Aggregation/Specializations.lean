/-
  Cred Aggregation: Specializations of the Forall Consequence Layer

  Specializes a universally-quantified (forall over a domain) consequence
  relation to three carriers:

  - the Boolean carrier (classical two-valued reasoning),
  - the Kleene carrier {0, 1/2, 1} with the LP designation {1/2, 1}
    (read as positivity) and the K3 designation {1} (read as certainty),
  - the product / native [0,1] carrier as a De Morgan triplet witness.

  The forall layer entails a conclusion when every domain-indexed valuation
  whose premises are all designated also makes the conclusion designated.
  Each carrier instance reads the abstract `designated` predicate as the
  notion appropriate to it: classical truth, positivity, or certainty.

  Godel and Lukasiewicz carriers are added in `Cred.Aggregation.ManyValued`
  as De Morgan triplets (min/max and bounded sum/difference with the
  complement). Their residuated implications are deliberately omitted: this
  layer aggregates only the negation/conjunction/disjunction triplet.
-/

import Cred.Aggregation.ForallConsequence
import Cred.Core.Consequence

namespace Cred.Aggregation

open Cred ThreeVal

/-! ## Generic Forall Consequence Over a Domain

A domain-indexed valuation assigns a carrier value to each element of a
domain `D` for each atom drawn from `α`. The forall consequence holds when,
for every such valuation, designation of all premises at every domain point
forces designation of the conclusion at every domain point. -/

/-- Forall consequence over a domain `D` with carrier `C` and a designation
    predicate on `C`. -/
def forallConsequence {C : Type*} (designated : C → Prop) (D α : Type*)
    (premises : List α) (conclusion : α) : Prop :=
  ∀ v : D → α → C,
    (∀ d : D, ∀ p ∈ premises, designated (v d p)) →
    (∀ d : D, designated (v d conclusion))

/-- Reflexivity: a premise is its own forall consequence. -/
theorem forallConsequence_reflexivity {C : Type*} (designated : C → Prop)
    (D α : Type*) (φ : α) :
    forallConsequence designated D α [φ] φ := by
  intro v hprem d
  exact hprem d φ (List.mem_cons_self φ [])

/-- Monotonicity (weakening the premise list). -/
theorem forallConsequence_monotonicity {C : Type*} (designated : C → Prop)
    {D α : Type*} {Γ Δ : List α} {φ : α}
    (h : forallConsequence designated D α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    forallConsequence designated D α Δ φ := by
  intro v hprem d
  exact h v (fun d' p hp => hprem d' p (hsub p hp)) d

/-! ## Boolean Carrier (Classical)

With `Bool` as carrier and `(· = true)` as designation, forall consequence
collapses to ordinary classical consequence pointwise over the domain. -/

/-- Classical designation on `Bool`: a value is designated iff it is `true`. -/
def isDesignatedBool : Bool → Prop := fun b => b = true

/-- On the Boolean carrier, forall consequence is exactly classical
    consequence: at every domain point, premises true force the conclusion
    true. This is definitional unfolding, recorded as the classical anchor. -/
theorem boolean_forall_consequence_is_classical (D α : Type*)
    (premises : List α) (conclusion : α) :
    forallConsequence isDesignatedBool D α premises conclusion ↔
    ∀ v : D → α → Bool,
      (∀ d : D, ∀ p ∈ premises, v d p = true) →
      (∀ d : D, v d conclusion = true) :=
  Iff.rfl

/-! ## Kleene Carrier {0, 1/2, 1}

The Kleene carrier is `ThreeVal`. The LP designation `{1/2, 1}` reads as
positivity (designated iff not zero); the K3 designation `{1}` reads as
certainty (designated iff equal to `one`). -/

/-- LP designation on the Kleene carrier coincides with positivity: a value
    is LP-designated iff it is not `zero`. -/
theorem lp_designation_as_positive (v : ThreeVal) :
    isDesignatedLP v ↔ v ≠ ThreeVal.zero := by
  cases v <;> simp [isDesignatedLP]

/-- K3 designation on the Kleene carrier coincides with certainty: a value is
    K3-designated iff it equals `one`. -/
theorem k3_designation_as_certain (v : ThreeVal) :
    isDesignatedK3 v ↔ v = ThreeVal.one := by
  cases v <;> simp [isDesignatedK3]

/-- LP forall consequence on the Kleene carrier, stated through positivity. -/
theorem lp_forall_consequence_as_positive (D α : Type*)
    (premises : List α) (conclusion : α) :
    forallConsequence isDesignatedLP D α premises conclusion ↔
    ∀ v : D → α → ThreeVal,
      (∀ d : D, ∀ p ∈ premises, v d p ≠ ThreeVal.zero) →
      (∀ d : D, v d conclusion ≠ ThreeVal.zero) := by
  unfold forallConsequence
  constructor
  · intro h v hprem d
    exact (lp_designation_as_positive _).mp
      (h v (fun d' p hp => (lp_designation_as_positive _).mpr (hprem d' p hp)) d)
  · intro h v hprem d
    exact (lp_designation_as_positive _).mpr
      (h v (fun d' p hp => (lp_designation_as_positive _).mp (hprem d' p hp)) d)

/-- K3 forall consequence on the Kleene carrier, stated through certainty. -/
theorem k3_forall_consequence_as_certain (D α : Type*)
    (premises : List α) (conclusion : α) :
    forallConsequence isDesignatedK3 D α premises conclusion ↔
    ∀ v : D → α → ThreeVal,
      (∀ d : D, ∀ p ∈ premises, v d p = ThreeVal.one) →
      (∀ d : D, v d conclusion = ThreeVal.one) := by
  unfold forallConsequence
  constructor
  · intro h v hprem d
    exact (k3_designation_as_certain _).mp
      (h v (fun d' p hp => (k3_designation_as_certain _).mpr (hprem d' p hp)) d)
  · intro h v hprem d
    exact (k3_designation_as_certain _).mpr
      (h v (fun d' p hp => (k3_designation_as_certain _).mp (hprem d' p hp)) d)

/-! ## Product / Native [0,1] Carrier

The native `Credence` carrier is a De Morgan triplet: involutive negation,
commutative associative product conjunction, and the De Morgan dual
disjunction. We record this as the instance witness for the [0,1] carrier
of the forall layer. -/

/-- The product / native `[0,1]` De Morgan triplet witness: negation is
    involutive, conjunction is commutative and associative, and the two
    De Morgan laws connect conjunction and disjunction. -/
theorem product_deMorgan_instance :
    (∀ c : Credence, Credence.neg (Credence.neg c) = c) ∧
    (∀ a b : Credence, a ⊗ b = b ⊗ a) ∧
    (∀ a b c : Credence, (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)) ∧
    (∀ a b : Credence, Credence.neg (a ⊗ b) = a.neg ⊔ b.neg) ∧
    (∀ a b : Credence, Credence.neg (a ⊔ b) = a.neg ⊗ b.neg) :=
  ⟨Credence.neg_neg, Credence.conj_comm, Credence.conj_assoc,
   Credence.de_morgan_conj, Credence.de_morgan_disj⟩

/-- Positivity designation on the native carrier: designated iff the value is
    strictly positive. This is the [0,1] reading of the LP designation. -/
def isDesignatedPositive : Credence → Prop := fun c => 0 < c.val

/-- Certainty designation on the native carrier: designated iff the value is
    `1`. This is the [0,1] reading of the K3 designation. -/
def isDesignatedCertain : Credence → Prop := fun c => c = 1

/-- On the native carrier, positivity forall consequence unfolds to its
    threshold reading at every domain point. -/
theorem positive_forall_consequence_unfold (D α : Type*)
    (premises : List α) (conclusion : α) :
    forallConsequence isDesignatedPositive D α premises conclusion ↔
    ∀ v : D → α → Credence,
      (∀ d : D, ∀ p ∈ premises, 0 < (v d p).val) →
      (∀ d : D, 0 < (v d conclusion).val) :=
  Iff.rfl

end Cred.Aggregation
