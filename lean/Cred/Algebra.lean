/-
  Cred Algebra: Abstract Product De Morgan Structure

  Abstraction layer for the value algebra of Cred.Core.Value. The `CredAlgebra`
  typeclass axiomatises the product De Morgan structure carried by `Credence`:
  a bounded partial order with an involutive order-reversing negation, a
  commutative associative monotone product with unit `⊤` and absorbing `⊥`, and
  a disjunction fixed as the De Morgan dual of the product.

  Disjunction is a class field rather than a definition so instances can supply
  a defeq-friendly form; `disj_eq` ties it to the De Morgan dual, from which the
  De Morgan laws and `⊥`/`⊤` boundaries follow generically.

  This is the abstraction layer only. Migration of the downstream `Credence`
  results onto the abstract interface is future work; here we establish the
  class, its laws, the generic lemmas, and the standard `Credence` instance.
-/

import Cred.Core.Value

namespace Cred

/-- Abstract product De Morgan algebra: a bounded partial order with an
involutive order-reversing negation, a commutative associative monotone product
(unit `⊤`, absorbing `⊥`), and a De Morgan-dual disjunction. -/
class CredAlgebra (V : Type*) extends PartialOrder V where
  /-- Least element. -/
  bot : V
  /-- Greatest element. -/
  top : V
  /-- Negation (complement). -/
  cneg : V → V
  /-- Product conjunction. -/
  cconj : V → V → V
  /-- Disjunction (De Morgan dual of the product). -/
  cdisj : V → V → V
  bot_le : ∀ a, bot ≤ a
  le_top : ∀ a, a ≤ top
  cneg_cneg : ∀ a, cneg (cneg a) = a
  cneg_le_cneg : ∀ a b, a ≤ b → cneg b ≤ cneg a
  cneg_bot : cneg bot = top
  cconj_comm : ∀ a b, cconj a b = cconj b a
  cconj_assoc : ∀ a b c, cconj (cconj a b) c = cconj a (cconj b c)
  cconj_top : ∀ a, cconj a top = a
  cconj_bot : ∀ a, cconj a bot = bot
  cconj_le_cconj_left : ∀ a {b c}, b ≤ c → cconj a b ≤ cconj a c
  disj_eq : ∀ a b, cdisj a b = cneg (cconj (cneg a) (cneg b))

namespace CredAlgebra

variable {V : Type*} [CredAlgebra V]

@[inherit_doc] prefix:80 "~ᶜ" => cneg
@[inherit_doc] infixl:70 " ⊗ᶜ " => cconj
@[inherit_doc] infixl:65 " ⊔ᶜ " => cdisj

/-! ## Boundary consequences -/

/-- Negation of the top element is the bottom element. -/
@[simp] theorem cneg_top : ~ᶜ(top : V) = bot := by
  have := cneg_cneg (V := V) bot
  rw [cneg_bot] at this
  exact this

/-- The product is monotone in its right argument (named restatement). -/
theorem cconj_mono_right (a : V) {b c : V} (h : b ≤ c) : a ⊗ᶜ b ≤ a ⊗ᶜ c :=
  cconj_le_cconj_left a h

/-- The product is monotone in its left argument. -/
theorem cconj_mono_left {a b : V} (c : V) (h : a ≤ b) : a ⊗ᶜ c ≤ b ⊗ᶜ c := by
  rw [cconj_comm a c, cconj_comm b c]
  exact cconj_le_cconj_left c h

/-- `top` is a left unit for the product. -/
@[simp] theorem top_cconj (a : V) : (top : V) ⊗ᶜ a = a := by
  rw [cconj_comm]; exact cconj_top a

/-- `bot` is a left absorbing element for the product. -/
@[simp] theorem bot_cconj (a : V) : (bot : V) ⊗ᶜ a = bot := by
  rw [cconj_comm]; exact cconj_bot a

/-! ## Disjunction boundaries -/

/-- `bot` is a right identity for disjunction. -/
@[simp] theorem cdisj_bot (a : V) : a ⊔ᶜ bot = a := by
  rw [disj_eq, cneg_bot, cconj_top, cneg_cneg]

/-- `bot` is a left identity for disjunction. -/
@[simp] theorem bot_cdisj (a : V) : (bot : V) ⊔ᶜ a = a := by
  rw [disj_eq, cneg_bot, top_cconj, cneg_cneg]

/-- `top` absorbs on the right for disjunction. -/
@[simp] theorem cdisj_top (a : V) : a ⊔ᶜ top = top := by
  rw [disj_eq, cneg_top, cconj_bot, cneg_bot]

/-- `top` absorbs on the left for disjunction. -/
@[simp] theorem top_cdisj (a : V) : (top : V) ⊔ᶜ a = top := by
  rw [disj_eq, cneg_top, bot_cconj, cneg_bot]

/-! ## Disjunction structure -/

/-- Disjunction is commutative. -/
theorem cdisj_comm (a b : V) : a ⊔ᶜ b = b ⊔ᶜ a := by
  rw [disj_eq, disj_eq, cconj_comm]

/-- Disjunction is associative (inherited from product associativity through De Morgan). -/
theorem cdisj_assoc (a b c : V) : (a ⊔ᶜ b) ⊔ᶜ c = a ⊔ᶜ (b ⊔ᶜ c) := by
  simp only [disj_eq, cneg_cneg, cconj_assoc]

/-! ## De Morgan laws -/

/-- De Morgan: `~(a ⊗ b) = ~a ⊔ ~b`. -/
theorem de_morgan_cconj (a b : V) : ~ᶜ(a ⊗ᶜ b) = ~ᶜa ⊔ᶜ ~ᶜb := by
  rw [disj_eq, cneg_cneg, cneg_cneg]

/-- De Morgan: `~(a ⊔ b) = ~a ⊗ ~b`. -/
theorem de_morgan_cdisj (a b : V) : ~ᶜ(a ⊔ᶜ b) = ~ᶜa ⊗ᶜ ~ᶜb := by
  rw [disj_eq, cneg_cneg]

/-- Negation is an order isomorphism onto the dual: the reverse direction. -/
theorem cneg_le_cneg_iff (a b : V) : ~ᶜb ≤ ~ᶜa ↔ a ≤ b := by
  constructor
  · intro h
    have := cneg_le_cneg _ _ h
    rwa [cneg_cneg, cneg_cneg] at this
  · exact cneg_le_cneg a b

end CredAlgebra

/-! ## Standard instance: `Credence` -/

/-- The credence value algebra of `Cred.Core.Value` is a `CredAlgebra`. -/
instance : CredAlgebra Credence where
  bot := 0
  top := 1
  cneg := Credence.neg
  cconj := Credence.conj
  cdisj := Credence.disj
  bot_le := Credence.zero_le
  le_top := Credence.le_one'
  cneg_cneg := Credence.neg_neg
  cneg_le_cneg a b h := (Credence.neg_le_neg_iff a b).mp h
  cneg_bot := Credence.neg_zero
  cconj_comm := Credence.conj_comm
  cconj_assoc := Credence.conj_assoc
  cconj_top := Credence.conj_one
  cconj_bot := Credence.conj_zero
  cconj_le_cconj_left a {b c} h := by
    rw [Credence.le_def, Credence.conj_val, Credence.conj_val]
    exact mul_le_mul_of_nonneg_left h a.nonneg
  disj_eq _ _ := rfl

end Cred
