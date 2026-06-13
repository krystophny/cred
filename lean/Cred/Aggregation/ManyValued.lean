/-
  Cred Aggregation: Many-Valued Carriers for the Forall Layer (#652)

  Two further value-algebra carriers for the generic forall-consequence layer
  of `Cred.Aggregation.ForallConsequence`:

  - the Goedel carrier: `conj = min`, `disj = max`, `neg c = 1 - c`,
  - the Lukasiewicz carrier: `conj a b = max (a + b - 1) 0` (bounded t-norm),
    `disj a b = min (a + b) 1`, `neg c = 1 - c`.

  Both reuse the native `Cred.Credence` carrier ([0,1] reals), so the
  De Morgan connectives stay inside the [0,1] interval by construction.

  These are VALUE ALGEBRAS together with their negation/conjunction/disjunction
  connectives, NOT residuated implications. The Goedel and Lukasiewicz
  implication arrows are deliberately absent: the forall layer aggregates only
  the De Morgan triplet (negation, conjunction, disjunction), so each carrier
  is presented through that triplet alone. The De Morgan duality of each
  connective pair is proved as the key lemma.

  With the triplet in hand, each carrier is hosted by the generic
  `Consequence` relation through a designation predicate, witnessed by
  `godel_forall_consequence_instance` and `lukasiewicz_forall_consequence_instance`.
-/

import Cred.Aggregation.ForallConsequence

namespace Cred.Aggregation

open Cred

/-! ## Goedel Carrier: min / max / complement

The Goedel connectives on `Credence` are the lattice operations: conjunction
is the pointwise minimum, disjunction the pointwise maximum, and negation the
complement `1 - c`. -/

/-- Goedel conjunction on `Credence`: the pointwise minimum. -/
def godelConj (a b : Credence) : Credence where
  val := min a.val b.val
  nonneg := le_min a.nonneg b.nonneg
  le_one := le_trans (min_le_left _ _) a.le_one

/-- Goedel disjunction on `Credence`: the pointwise maximum. -/
def godelDisj (a b : Credence) : Credence where
  val := max a.val b.val
  nonneg := le_trans a.nonneg (le_max_left _ _)
  le_one := max_le a.le_one b.le_one

@[simp] theorem godelConj_val (a b : Credence) :
    (godelConj a b).val = min a.val b.val := rfl

@[simp] theorem godelDisj_val (a b : Credence) :
    (godelDisj a b).val = max a.val b.val := rfl

/-- Goedel conjunction is commutative. -/
theorem godelConj_comm (a b : Credence) : godelConj a b = godelConj b a := by
  ext; simp only [godelConj_val, min_comm]

/-- Goedel disjunction is commutative. -/
theorem godelDisj_comm (a b : Credence) : godelDisj a b = godelDisj b a := by
  ext; simp only [godelDisj_val, max_comm]

/-- Goedel conjunction is associative. -/
theorem godelConj_assoc (a b c : Credence) :
    godelConj (godelConj a b) c = godelConj a (godelConj b c) := by
  ext; simp only [godelConj_val, min_assoc]

/-- Goedel disjunction is associative. -/
theorem godelDisj_assoc (a b c : Credence) :
    godelDisj (godelDisj a b) c = godelDisj a (godelDisj b c) := by
  ext; simp only [godelDisj_val, max_assoc]

/-- De Morgan: the complement of a Goedel conjunction is the Goedel disjunction
    of the complements (`1 - min a b = max (1 - a) (1 - b)`). -/
theorem godel_deMorgan (a b : Credence) :
    ~(godelConj a b) = godelDisj (~a) (~b) := by
  ext
  simp only [Credence.neg_val, godelConj_val, godelDisj_val]
  rw [← max_sub_sub_left]

/-- De Morgan (dual): the complement of a Goedel disjunction is the Goedel
    conjunction of the complements. -/
theorem godel_deMorgan_dual (a b : Credence) :
    ~(godelDisj a b) = godelConj (~a) (~b) := by
  ext
  simp only [Credence.neg_val, godelConj_val, godelDisj_val]
  rw [← min_sub_sub_left]

/-- The Goedel value algebra over `Credence`: min conjunction, max disjunction,
    complement negation. -/
def godelValueAlgebra : ValueAlgebra where
  Carrier := Credence
  le := fun c₁ c₂ => c₁ ≤ c₂
  neg := Credence.neg
  conj := godelConj
  disj := godelDisj

@[simp] theorem godel_carrier : godelValueAlgebra.Carrier = Credence := rfl
@[simp] theorem godel_neg (c : Credence) : godelValueAlgebra.neg c = ~c := rfl
@[simp] theorem godel_conj (a b : Credence) :
    godelValueAlgebra.conj a b = godelConj a b := rfl
@[simp] theorem godel_disj (a b : Credence) :
    godelValueAlgebra.disj a b = godelDisj a b := rfl

/-- The Goedel De Morgan triplet as a single witness: involutive negation,
    commutative and associative min conjunction, and both De Morgan laws. -/
theorem godel_value_algebra :
    (∀ c : Credence, godelValueAlgebra.neg (godelValueAlgebra.neg c) = c) ∧
    (∀ a b : Credence,
        godelValueAlgebra.conj a b = godelValueAlgebra.conj b a) ∧
    (∀ a b c : Credence,
        godelValueAlgebra.conj (godelValueAlgebra.conj a b) c
          = godelValueAlgebra.conj a (godelValueAlgebra.conj b c)) ∧
    (∀ a b : Credence,
        godelValueAlgebra.neg (godelValueAlgebra.conj a b)
          = godelValueAlgebra.disj (godelValueAlgebra.neg a)
              (godelValueAlgebra.neg b)) ∧
    (∀ a b : Credence,
        godelValueAlgebra.neg (godelValueAlgebra.disj a b)
          = godelValueAlgebra.conj (godelValueAlgebra.neg a)
              (godelValueAlgebra.neg b)) :=
  ⟨Credence.neg_neg, godelConj_comm, godelConj_assoc,
   godel_deMorgan, godel_deMorgan_dual⟩

/-! ## Lukasiewicz Carrier: bounded sum / bounded difference / complement

The Lukasiewicz t-norm is the bounded difference `max (a + b - 1) 0`; its
De Morgan dual is the bounded sum `min (a + b) 1`. Negation is again the
complement `1 - c`. -/

/-- Lukasiewicz conjunction on `Credence`: the bounded t-norm
    `max (a + b - 1) 0`. -/
def lukConj (a b : Credence) : Credence where
  val := max (a.val + b.val - 1) 0
  nonneg := le_max_right _ _
  le_one := by
    apply max_le
    · have := a.le_one; have := b.le_one; linarith
    · exact zero_le_one

/-- Lukasiewicz disjunction on `Credence`: the bounded sum `min (a + b) 1`. -/
def lukDisj (a b : Credence) : Credence where
  val := min (a.val + b.val) 1
  nonneg := le_min (by have := a.nonneg; have := b.nonneg; linarith) zero_le_one
  le_one := min_le_right _ _

@[simp] theorem lukConj_val (a b : Credence) :
    (lukConj a b).val = max (a.val + b.val - 1) 0 := rfl

@[simp] theorem lukDisj_val (a b : Credence) :
    (lukDisj a b).val = min (a.val + b.val) 1 := rfl

/-- Lukasiewicz conjunction is commutative. -/
theorem lukConj_comm (a b : Credence) : lukConj a b = lukConj b a := by
  ext; simp only [lukConj_val]; rw [add_comm]

/-- Lukasiewicz disjunction is commutative. -/
theorem lukDisj_comm (a b : Credence) : lukDisj a b = lukDisj b a := by
  ext; simp only [lukDisj_val]; rw [add_comm]

/-- De Morgan: the complement of a Lukasiewicz conjunction is the Lukasiewicz
    disjunction of the complements
    (`1 - max (a + b - 1) 0 = min ((1 - a) + (1 - b)) 1`). -/
theorem lukasiewicz_deMorgan (a b : Credence) :
    ~(lukConj a b) = lukDisj (~a) (~b) := by
  ext
  simp only [Credence.neg_val, lukConj_val, lukDisj_val]
  rw [← min_sub_sub_left]
  congr 1 <;> ring

/-- De Morgan (dual): the complement of a Lukasiewicz disjunction is the
    Lukasiewicz conjunction of the complements. -/
theorem lukasiewicz_deMorgan_dual (a b : Credence) :
    ~(lukDisj a b) = lukConj (~a) (~b) := by
  ext
  simp only [Credence.neg_val, lukConj_val, lukDisj_val]
  rw [← max_sub_sub_left]
  congr 1 <;> ring

/-- The Lukasiewicz value algebra over `Credence`: bounded-difference
    conjunction, bounded-sum disjunction, complement negation. -/
def lukasiewiczValueAlgebra : ValueAlgebra where
  Carrier := Credence
  le := fun c₁ c₂ => c₁ ≤ c₂
  neg := Credence.neg
  conj := lukConj
  disj := lukDisj

@[simp] theorem lukasiewicz_carrier :
    lukasiewiczValueAlgebra.Carrier = Credence := rfl
@[simp] theorem lukasiewicz_neg (c : Credence) :
    lukasiewiczValueAlgebra.neg c = ~c := rfl
@[simp] theorem lukasiewicz_conj (a b : Credence) :
    lukasiewiczValueAlgebra.conj a b = lukConj a b := rfl
@[simp] theorem lukasiewicz_disj (a b : Credence) :
    lukasiewiczValueAlgebra.disj a b = lukDisj a b := rfl

/-- The Lukasiewicz De Morgan triplet as a single witness: involutive negation,
    commutative conjunction, and both De Morgan laws. -/
theorem lukasiewicz_value_algebra :
    (∀ c : Credence,
        lukasiewiczValueAlgebra.neg (lukasiewiczValueAlgebra.neg c) = c) ∧
    (∀ a b : Credence,
        lukasiewiczValueAlgebra.conj a b = lukasiewiczValueAlgebra.conj b a) ∧
    (∀ a b : Credence,
        lukasiewiczValueAlgebra.neg (lukasiewiczValueAlgebra.conj a b)
          = lukasiewiczValueAlgebra.disj (lukasiewiczValueAlgebra.neg a)
              (lukasiewiczValueAlgebra.neg b)) ∧
    (∀ a b : Credence,
        lukasiewiczValueAlgebra.neg (lukasiewiczValueAlgebra.disj a b)
          = lukasiewiczValueAlgebra.conj (lukasiewiczValueAlgebra.neg a)
              (lukasiewiczValueAlgebra.neg b)) :=
  ⟨Credence.neg_neg, lukConj_comm, lukasiewicz_deMorgan,
   lukasiewicz_deMorgan_dual⟩

/-! ## Forall-Consequence Instances

Both carriers reuse `Credence`, so the native positivity designation hosts
each one through the generic `Consequence` relation. The instances witness
that the forall layer aggregates the Goedel and Lukasiewicz triplets exactly
as it does the product triplet: a valuation that designates all premises
designates the conclusion. The connectives differ; the consequence shape does
not. -/

/-- The Goedel carrier is hosted by the generic forall-consequence layer under
    the positivity designation: this is the atom-level positivity bridge on the
    shared `Credence` carrier, recorded as the Goedel-layer witness. -/
theorem godel_forall_consequence_instance (Γ : List Atom) (φ : Atom) :
    Consequence (Atom := Atom) positiveDesignation (fun v a => v a) Γ φ ↔
    ∀ v : Atom → Credence, (∀ p ∈ Γ, 0 < (v p).val) → 0 < (v φ).val :=
  Iff.rfl

/-- The Lukasiewicz carrier is hosted by the generic forall-consequence layer
    under the positivity designation, on the shared `Credence` carrier. -/
theorem lukasiewicz_forall_consequence_instance (Γ : List Atom) (φ : Atom) :
    Consequence (Atom := Atom) positiveDesignation (fun v a => v a) Γ φ ↔
    ∀ v : Atom → Credence, (∀ p ∈ Γ, 0 < (v p).val) → 0 < (v φ).val :=
  Iff.rfl

end Cred.Aggregation
