/-
  Cred Collapse: Three-Valued Credences

  The discrete value set {0, 1/2, 1} with Kleene operations, the RM3,
  Gödel, and product-residuated implications for comparison, and Bayes
  consistency of these arrows on three values.
-/

import Cred.Cond.Admissible

namespace Cred

/-! ## Three-Valued Collapse

The three-valued collapse maps [0,1] to {0, 1/2, 1}:
- 0 maps to 0
- (0,1) maps to 1/2
- 1 maps to 1

This collapsed algebra matches RM3 for {negation, conjunction, disjunction},
but differs on implication: RM3 has 0 → b = 1 (ex falso), while Cred
conditioning on 0 is unconstrained.
-/

/-- Three-valued credence type -/
inductive ThreeVal where
  | zero : ThreeVal
  | half : ThreeVal
  | one : ThreeVal
deriving DecidableEq, Repr

namespace ThreeVal

/-- Negation on three values (matches Cred and RM3) -/
def neg : ThreeVal → ThreeVal
  | zero => one
  | half => half
  | one => zero

/-- Conjunction on three values (matches RM3 min) -/
def conj : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => zero
  | _, zero => zero
  | one, b => b
  | a, one => a
  | half, half => half

/-- Disjunction on three values (matches RM3 max) -/
def disj : ThreeVal → ThreeVal → ThreeVal
  | one, _ => one
  | _, one => one
  | zero, b => b
  | a, zero => a
  | half, half => half

/-- Negation is involutive -/
theorem neg_neg (v : ThreeVal) : neg (neg v) = v := by
  cases v <;> rfl

/-- 0 is absorbing for conjunction -/
theorem conj_zero (v : ThreeVal) : conj zero v = zero := by
  cases v <;> rfl

theorem zero_conj (v : ThreeVal) : conj v zero = zero := by
  cases v <;> rfl

/-- 1 is identity for conjunction -/
theorem conj_one (v : ThreeVal) : conj one v = v := by
  cases v <;> rfl

theorem one_conj (v : ThreeVal) : conj v one = v := by
  cases v <;> rfl

/-- half ∧ half = half (key RM3 property) -/
theorem conj_half_half : conj half half = half := by rfl

/-- 1 is absorbing for disjunction -/
theorem disj_one (v : ThreeVal) : disj one v = one := by
  cases v <;> rfl

theorem one_disj (v : ThreeVal) : disj v one = one := by
  cases v <;> rfl

/-- 0 is identity for disjunction -/
theorem disj_zero (v : ThreeVal) : disj zero v = v := by
  cases v <;> rfl

theorem zero_disj (v : ThreeVal) : disj v zero = v := by
  cases v <;> rfl

/-- half ∨ half = half (key RM3 property) -/
theorem disj_half_half : disj half half = half := by rfl

/-- De Morgan law -/
theorem de_morgan_conj (a b : ThreeVal) : neg (conj a b) = disj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem de_morgan_disj (a b : ThreeVal) : neg (disj a b) = conj (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- RM3 implication (for comparison - NOT used in Cred) -/
def rm3_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one  -- Ex falso!
  | half, zero => half
  | half, half => half
  | half, one => one
  | one, zero => zero
  | one, half => half
  | one, one => one

/-- RM3 has ex falso: 0 → b = 1 for all b -/
theorem rm3_ex_falso (b : ThreeVal) : rm3_impl zero b = one := by
  cases b <;> rfl

/-! ### Complete RM3 Implication Table

The following 9 theorems verify every entry in the RM3 implication table:
       | 0 | 1/2 | 1
   ----+---+-----+---
   0   | 1 |  1  | 1    (ex falso row)
   1/2 |1/2| 1/2 | 1
   1   | 0 | 1/2 | 1
-/

theorem rm3_impl_zero_zero : rm3_impl zero zero = one := rfl
theorem rm3_impl_zero_half : rm3_impl zero half = one := rfl
theorem rm3_impl_zero_one : rm3_impl zero one = one := rfl
theorem rm3_impl_half_zero : rm3_impl half zero = half := rfl
theorem rm3_impl_half_half : rm3_impl half half = half := rfl
theorem rm3_impl_half_one : rm3_impl half one = one := rfl
theorem rm3_impl_one_zero : rm3_impl one zero = zero := rfl
theorem rm3_impl_one_half : rm3_impl one half = half := rfl
theorem rm3_impl_one_one : rm3_impl one one = one := rfl

/-- Cred conditioning on 0 is NOT forced to 1 (blocks ex falso).
    Any credence value can serve as the conditional when evidence = 0. -/
theorem cred_no_ex_falso (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

/-! ### Gödel / Product Residuated Implication

On {0, 1/2, 1}, the product residuated implication min(b/a, 1) coincides
with the Gödel implication. Both differ from RM3 at (half, zero):
Gödel/residuated gives zero, RM3 gives half.

Cred conditioning (with Kleene joint = min(a,b)) recovers this arrow for
evidence > 0 and replaces the a = 0 row with * (unconstrained).
-/

/-- Gödel implication on three values (= product residuated on three values) -/
def godel_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one
  | half, zero => zero
  | half, half => one
  | half, one => one
  | one, zero => zero
  | one, half => half
  | one, one => one

/-! #### Complete Gödel Implication Table

       | 0 | 1/2 | 1
   ----+---+-----+---
   0   | 1 |  1  | 1    (vacuous truth row, shared with RM3)
   1/2 | 0 |  1  | 1
   1   | 0 | 1/2 | 1
-/

theorem godel_impl_zero_zero : godel_impl zero zero = one := rfl
theorem godel_impl_zero_half : godel_impl zero half = one := rfl
theorem godel_impl_zero_one : godel_impl zero one = one := rfl
theorem godel_impl_half_zero : godel_impl half zero = zero := rfl
theorem godel_impl_half_half : godel_impl half half = one := rfl
theorem godel_impl_half_one : godel_impl half one = one := rfl
theorem godel_impl_one_zero : godel_impl one zero = zero := rfl
theorem godel_impl_one_half : godel_impl one half = half := rfl
theorem godel_impl_one_one : godel_impl one one = one := rfl

/-- Product residuated implication on three values: min(b/a, 1) for a > 0, 1 for a = 0.
    Defined independently of godel_impl to verify their coincidence. -/
def prod_resid_impl : ThreeVal → ThreeVal → ThreeVal
  | zero, _ => one        -- convention: 0 → b = 1
  | half, zero => zero    -- min(0 / (1/2), 1) = 0
  | half, half => one     -- min((1/2) / (1/2), 1) = min(1, 1) = 1
  | half, one => one      -- min(1 / (1/2), 1) = min(2, 1) = 1
  | one, zero => zero     -- min(0/1, 1) = 0
  | one, half => half     -- min((1/2)/1, 1) = 1/2
  | one, one => one       -- min(1/1, 1) = 1

/-- On {0, 1/2, 1}, Gödel and product residuated implications coincide. -/
theorem godel_impl_eq_prod_resid (a b : ThreeVal) :
    godel_impl a b = prod_resid_impl a b := by
  cases a <;> cases b <;> rfl

/-- Gödel and RM3 differ at (half, zero): Gödel gives zero, RM3 gives half -/
theorem godel_impl_ne_rm3_impl : godel_impl half zero ≠ rm3_impl half zero := by
  decide

/-- Gödel also has 0 -> b = 1 (vacuous truth, shared with RM3) -/
theorem godel_impl_zero_is_one (b : ThreeVal) : godel_impl zero b = one := by
  cases b <;> rfl

/-- Cred conditioning blocks ex falso relative to both RM3 and Gödel:
    both have 0 -> b = 1, but Cred conditioning at evidence 0 is unconstrained. -/
theorem cred_no_ex_falso_godel (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

/-! ### Bayes Consistency

A binary arrow f(a, b) used as conditioning is Bayes-consistent when the joint
it induces is symmetric: f(a, b) * a = f(b, a) * b.  This is the constraint
from applying the chain rule in both directions (Bayes theorem).
-/

theorem rm3_not_bayes_consistent :
    ∃ a b : ThreeVal, conj (rm3_impl a b) a ≠ conj (rm3_impl b a) b := by
  use half, zero; decide

theorem godel_bayes_consistent (a b : ThreeVal) :
    conj (godel_impl a b) a = conj (godel_impl b a) b := by
  cases a <;> cases b <;> rfl

end ThreeVal

end Cred
