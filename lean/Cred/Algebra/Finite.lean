/-
  Finite, real-free models of the `CredAlgebra` signature.

  The standard `CredAlgebra Credence` instance in `Cred.Algebra` is built on the
  real-number carrier of `Cred.Core.Value`. This module shows the abstraction is
  not tied to the reals by exhibiting two finite carriers that satisfy every
  `CredAlgebra` axiom without mentioning `ℝ`:

    * `Bool` — the two-element Boolean algebra (∧ as product, ∨ as De Morgan dual);
    * `Three` — a fresh three-element type modelling the `{0, 1/2, 1}` collapse
      (Kleene) algebra, with strong conjunction as `min` and disjunction as `max`.

  Together these are finite, real-free models of the value-algebra signature. The
  full internal construction of the `[0,1]` algebra (Dedekind cuts over internal
  rationals) is not attempted here.
-/

import Cred.Algebra

namespace Cred

/-! ## Two-element Boolean model -/

-- noncomputable: `Bool`'s mathlib `PartialOrder` derives from a Boolean-algebra
-- instance that carries no executable code; the data here is otherwise decidable.
/-- `Bool` is a real-free `CredAlgebra`: the standard two-element Boolean algebra
with `∧` as the product and `∨` as its De Morgan dual. -/
noncomputable instance : CredAlgebra Bool where
  bot := false
  top := true
  cneg := not
  cconj := and
  cdisj := or
  bot_le a := by cases a <;> decide
  le_top a := by cases a <;> decide
  cneg_cneg a := by cases a <;> rfl
  cneg_le_cneg a b h := by cases a <;> cases b <;> simp_all
  cneg_bot := rfl
  cconj_comm a b := by cases a <;> cases b <;> rfl
  cconj_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  cconj_top a := by cases a <;> rfl
  cconj_bot a := by cases a <;> rfl
  cconj_le_cconj_left a {b c} h := by cases a <;> cases b <;> cases c <;> simp_all
  disj_eq a b := by cases a <;> cases b <;> rfl

/-! ## Three-element Kleene (collapse) model -/

/-- Three-element collapse carrier modelling `{0, 1/2, 1}` with `lo < mid < hi`. -/
inductive Three : Type
  | lo
  | mid
  | hi
  deriving DecidableEq, Repr

namespace Three

/-- Numeric rank used to define the order and the min/max operations. -/
def rank : Three → Nat
  | lo => 0
  | mid => 1
  | hi => 2

/-- Order by rank: `lo ≤ mid ≤ hi`. -/
instance : LE Three := ⟨fun a b => a.rank ≤ b.rank⟩
instance : LT Three := ⟨fun a b => a.rank < b.rank⟩

instance : DecidableEq Three := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- Rank is injective, so the rank order is genuinely antisymmetric. -/
theorem rank_inj : ∀ {a b : Three}, a.rank = b.rank → a = b := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

instance : PartialOrder Three where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl _
  le_trans a b c := Nat.le_trans
  le_antisymm a b hab hba := rank_inj (Nat.le_antisymm hab hba)
  lt_iff_le_not_le a b := by
    constructor
    · intro h; exact ⟨Nat.le_of_lt h, Nat.not_le_of_lt h⟩
    · intro ⟨h₁, h₂⟩; exact Nat.lt_of_le_of_ne h₁ (fun e => h₂ (Nat.le_of_eq e.symm))

/-- Strong (Kleene) negation: reflects the order around `mid`. -/
def neg : Three → Three
  | lo => hi
  | mid => mid
  | hi => lo

/-- Strong conjunction is the pointwise minimum of credences. -/
def conj : Three → Three → Three
  | lo, _ => lo
  | _, lo => lo
  | mid, mid => mid
  | mid, hi => mid
  | hi, mid => mid
  | hi, hi => hi

/-- Disjunction is the De Morgan dual of `conj` (pointwise maximum). -/
def disj (a b : Three) : Three := neg (conj (neg a) (neg b))

theorem neg_neg : ∀ a : Three, neg (neg a) = a := by
  intro a; cases a <;> rfl

theorem conj_comm : ∀ a b : Three, conj a b = conj b a := by
  intro a b; cases a <;> cases b <;> rfl

theorem conj_assoc : ∀ a b c : Three, conj (conj a b) c = conj a (conj b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem conj_hi : ∀ a : Three, conj a hi = a := by
  intro a; cases a <;> rfl

theorem conj_lo : ∀ a : Three, conj a lo = lo := by
  intro a; cases a <;> rfl

theorem neg_le_neg : ∀ a b : Three, a ≤ b → neg b ≤ neg a := by
  intro a b h; cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem conj_le_conj_left : ∀ (a : Three) {b c : Three}, b ≤ c → conj a b ≤ conj a c := by
  intro a b c h; cases a <;> cases b <;> cases c <;>
    first | decide | exact absurd h (by decide)

end Three

/-- `Three` is a real-free `CredAlgebra`: the strong Kleene three-element algebra
on `{0, 1/2, 1}` with `min` conjunction and `max` disjunction. -/
instance : CredAlgebra Three where
  bot := Three.lo
  top := Three.hi
  cneg := Three.neg
  cconj := Three.conj
  cdisj := Three.disj
  bot_le a := by cases a <;> decide
  le_top a := by cases a <;> decide
  cneg_cneg := Three.neg_neg
  cneg_le_cneg := Three.neg_le_neg
  cneg_bot := rfl
  cconj_comm := Three.conj_comm
  cconj_assoc := Three.conj_assoc
  cconj_top := Three.conj_hi
  cconj_bot := Three.conj_lo
  cconj_le_cconj_left a {b c} h := Three.conj_le_conj_left a h
  disj_eq _ _ := rfl

end Cred
