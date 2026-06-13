/-
  Cred Aggregation: Generic Forall-Consequence Layer (#648)

  A value-algebra abstraction over the propositional bridge. A `ValueAlgebra`
  bundles a carrier with an order and the three core operations (negation,
  product conjunction, De Morgan disjunction); a `Designation` picks out the
  "good" values, and `Consequence` is the universally quantified
  preservation-of-designation relation:

      Γ ⊨ φ  :=  ∀ v, (∀ γ ∈ Γ, D (eval v γ)) → D (eval v φ).

  The structural rules (reflexivity, weakening/monotonicity, cut) hold for
  this generic shape regardless of the algebra, eval, or designation. The
  native product-De Morgan instance reuses `Cred.Credence` so the concrete
  bridge of `Cred.Core` is a special case of this layer.

  There is deliberately no implication or conditional constructor: the
  algebra exposes only negation, conjunction, and disjunction, matching the
  product De Morgan triplet.
-/

import Cred.Core.Consequence

namespace Cred.Aggregation

universe u

/-! ## Value Algebras -/

/-- A value algebra: a carrier with an order and the three core operations of
    the product De Morgan triplet. No implication/conditional is exposed. -/
structure ValueAlgebra where
  Carrier : Type u
  le : Carrier → Carrier → Prop
  neg : Carrier → Carrier
  conj : Carrier → Carrier → Carrier
  disj : Carrier → Carrier → Carrier

/-- A valuation assigns a carrier value to each atom. -/
def Valuation (Atom : Type*) (V : Type u) : Type _ := Atom → V

/-- A designation marks the "good" (designated) values of a carrier. -/
def Designation (V : Type u) : Type _ := V → Prop

/-! ## Generic Consequence

`eval` is supplied as `Valuation Atom V → φType → V`, so the same definition
covers atom-level (`φType = Atom`) and formula-level evaluation. -/

/-- Forall-consequence: every valuation that designates all premises also
    designates the conclusion. -/
def Consequence {Atom : Type*} {V : Type u} {φType : Type*}
    (D : Designation V) (eval : Valuation Atom V → φType → V)
    (Γ : List φType) (φ : φType) : Prop :=
  ∀ v : Valuation Atom V, (∀ γ ∈ Γ, D (eval v γ)) → D (eval v φ)

variable {Atom : Type*} {V : Type u} {φType : Type*}
  {D : Designation V} {eval : Valuation Atom V → φType → V}

/-- Reflexivity: a premise entails itself. -/
theorem consequence_refl (φ : φType) : Consequence D eval [φ] φ := by
  intro v hprem
  exact hprem φ (List.mem_cons_self φ [])

/-- Monotonicity (weakening): enlarging the premise set preserves consequence. -/
theorem consequence_mono {Γ Δ : List φType} {φ : φType}
    (h : Consequence D eval Γ φ) (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    Consequence D eval Δ φ := by
  intro v hprem
  exact h v (fun p hp => hprem p (hsub p hp))

/-- Cut: an entailed lemma may be discharged. -/
theorem consequence_cut {Γ : List φType} {φ ψ : φType}
    (h1 : Consequence D eval Γ φ)
    (h2 : Consequence D eval (φ :: Γ) ψ) :
    Consequence D eval Γ ψ := by
  intro v hprem
  have hφ := h1 v hprem
  exact h2 v (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

/-! ## Native Product-De Morgan Instance

The `[0,1]` / `Credence` carrier with its native order and the product
conjunction, complement negation, and De Morgan disjunction. -/

/-- The native product De Morgan triplet on `Credence` as a `ValueAlgebra`. -/
def nativeCred_value_algebra : ValueAlgebra where
  Carrier := Credence
  le := fun c₁ c₂ => c₁ ≤ c₂
  neg := Credence.neg
  conj := Credence.conj
  disj := Credence.disj

@[simp] theorem nativeCred_carrier :
    nativeCred_value_algebra.Carrier = Credence := rfl

@[simp] theorem nativeCred_neg (c : Credence) :
    nativeCred_value_algebra.neg c = ~c := rfl

@[simp] theorem nativeCred_conj (c₁ c₂ : Credence) :
    nativeCred_value_algebra.conj c₁ c₂ = c₁ ⊗ c₂ := rfl

@[simp] theorem nativeCred_disj (c₁ c₂ : Credence) :
    nativeCred_value_algebra.disj c₁ c₂ = c₁ ⊔ c₂ := rfl

/-! ### Concrete designations and eval on the native carrier

These specialize the generic `Consequence` to the product De Morgan triplet,
recovering the positivity and certainty bridges of `Cred.Core` as instances. -/

/-- Positivity designation: a credence value is designated when it is positive. -/
def positiveDesignation : Designation Credence := fun c => 0 < c.val

/-- Certainty designation: a credence value is designated when it equals 1. -/
def certaintyDesignation : Designation Credence := fun c => c = 1

/-- Positivity consequence at the atom level is an instance of the generic
    forall-consequence with the positivity designation. -/
theorem positivity_is_consequence (Γ : List Atom) (φ : Atom) :
    Consequence (Atom := Atom) positiveDesignation (fun v a => v a) Γ φ ↔
    ∀ v : Atom → Credence, (∀ p ∈ Γ, 0 < (v p).val) → 0 < (v φ).val :=
  Iff.rfl

/-- Certainty consequence at the atom level is an instance of the generic
    forall-consequence with the certainty designation. -/
theorem certainty_is_consequence (Γ : List Atom) (φ : Atom) :
    Consequence (Atom := Atom) certaintyDesignation (fun v a => v a) Γ φ ↔
    ∀ v : Atom → Credence, (∀ p ∈ Γ, v p = 1) → v φ = 1 :=
  Iff.rfl

/-- The native positivity bridge inherits reflexivity from the generic layer. -/
theorem nativeCred_positivity_refl (φ : Atom) :
    Consequence (Atom := Atom) positiveDesignation (fun v a => v a) [φ] φ :=
  consequence_refl φ

/-- The native certainty bridge inherits cut from the generic layer. -/
theorem nativeCred_certainty_cut {Γ : List Atom} {φ ψ : Atom}
    (h1 : Consequence (Atom := Atom) certaintyDesignation (fun v a => v a) Γ φ)
    (h2 : Consequence (Atom := Atom) certaintyDesignation (fun v a => v a) (φ :: Γ) ψ) :
    Consequence (Atom := Atom) certaintyDesignation (fun v a => v a) Γ ψ :=
  consequence_cut h1 h2

end Cred.Aggregation
