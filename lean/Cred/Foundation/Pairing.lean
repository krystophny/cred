/-
  Cred Foundation: pairing as an explicit arithmetic formula

  Sequence coding is the foundation of the classical arithmetization of
  provability, and sequence coding rests on the pairing function. This module
  builds an object-language formula `pairGraph x y z` over the Robinson Q
  signature and proves it represents Mathlib's `Nat.pair` in the standard model:
  the formula is designated exactly when `z` is the pair of `x` and `y`. This is
  a complete, fully proved representability result for a concrete arithmetic
  function, the first brick of the object-language `Prov` arithmetization.

  `Nat.pair a b = if a < b then b * b + a else a * a + a + b`, so the graph is
  the disjunction of the two branches, each guarded by the definable order.
-/

import Cred.Foundation.SigmaOne

namespace Cred
namespace Foundation
namespace arithQ

open Credence

-- `SigmaOne` exposes `LE` on the domain; the order conditional and the strict
-- order need decidability, `LT`, and the arithmetic operations as well.
instance : LT natModel.Domain := inferInstanceAs (LT Nat)
instance : Add natModel.Domain := inferInstanceAs (Add Nat)
instance : Mul natModel.Domain := inferInstanceAs (Mul Nat)
instance (a b : natModel.Domain) : Decidable (a ≤ b) := Nat.decLe a b

/-! ## The definable order evaluates crisply, as a conditional value -/

/-- The definable order takes value `1` when `⟦a⟧ ≤ ⟦b⟧` and `0` otherwise. -/
theorem leF_eval_eq (env : natModel.Assignment) (a b : ArithQTerm) :
    natModel.evalFormula env (leF a b) =
      (if natModel.evalTerm env a ≤ natModel.evalTerm env b then 1 else 0) := by
  by_cases h : natModel.evalTerm env a ≤ natModel.evalTerm env b
  · rw [if_pos h]; exact (leF_eval_one_iff env a b).2 h
  · rw [if_neg h]
    -- with no witness the body is identically 0, so its supremum is 0
    have hbody : ∀ c : Nat,
        natModel.evalFormula (Structure.update natModel env c)
          (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))
          = (if Nat.add (natModel.evalTerm env a) c = natModel.evalTerm env b
              then (1 : Credence) else 0) := by
      intro c
      have ha : natModel.evalTerm (Structure.update natModel env c)
          (Term.rename Nat.succ a) = natModel.evalTerm env a := by
        rw [Structure.evalTerm_rename]; rfl
      have hb : natModel.evalTerm (Structure.update natModel env c)
          (Term.rename Nat.succ b) = natModel.evalTerm env b := by
        rw [Structure.evalTerm_rename]; rfl
      show natModel.eq (natModel.func .add
          [natModel.evalTerm (Structure.update natModel env c) (Term.rename Nat.succ a),
           c])
          (natModel.evalTerm (Structure.update natModel env c) (Term.rename Nat.succ b))
          = _
      rw [ha, hb]
      rfl
    have hzero : (fun c : Nat => natModel.evalFormula (Structure.update natModel env c)
        (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b)))
        = fun _ : Nat => (0 : Credence) := by
      funext c
      rw [hbody c]
      exact if_neg (fun hc => h (Nat.le.intro hc))
    show natModel.ex (fun c : Nat => natModel.evalFormula (Structure.update natModel env c)
        (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))) = 0
    exact (congrArg natModel.ex hzero).trans natModel_quantifierLaws.ex_zero

theorem leF_crisp (env : natModel.Assignment) (a b : ArithQTerm) :
    natModel.evalFormula env (leF a b) = 0 ∨
      natModel.evalFormula env (leF a b) = 1 := by
  rw [leF_eval_eq]
  by_cases h : natModel.evalTerm env a ≤ natModel.evalTerm env b <;> simp [h]

/-! ## Strict order, definable from the order -/

/-- Strict order `a < b := S a ≤ b`. -/
def ltF (a b : ArithQTerm) : ArithQFormula := leF (succT a) b

theorem ltF_eval_one_iff (env : natModel.Assignment) (a b : ArithQTerm) :
    natModel.evalFormula env (ltF a b) = 1 ↔
      natModel.evalTerm env a < natModel.evalTerm env b := by
  rw [ltF, leF_eval_one_iff]
  show natModel.func .succ [natModel.evalTerm env a] ≤ natModel.evalTerm env b ↔
    natModel.evalTerm env a < natModel.evalTerm env b
  exact Nat.succ_le_iff

theorem ltF_crisp (env : natModel.Assignment) (a b : ArithQTerm) :
    natModel.evalFormula env (ltF a b) = 0 ∨
      natModel.evalFormula env (ltF a b) = 1 :=
  leF_crisp env (succT a) b

/-! ## Crisp connective helpers in the standard model -/

theorem conj_crisp_one_iff {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ⊗ b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.zero_conj, Credence.conj_zero, Credence.one_conj]

theorem disj_crisp_one_iff {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ⊔ b = 1 ↔ a = 1 ∨ b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.zero_disj, Credence.disj_zero, Credence.disj_one,
      Credence.one_disj]

/-- A conjunction of crisp credences is crisp. -/
theorem conj_crisp {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ⊗ b = 0 ∨ a ⊗ b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.zero_conj, Credence.conj_zero, Credence.one_conj]

/-! ## The pairing graph -/

/-- The graph of `Nat.pair` as an object formula: `(x < y ∧ z = y² + x) ∨
    (y ≤ x ∧ z = x² + x + y)`. -/
def pairGraph (x y z : ArithQTerm) : ArithQFormula :=
  .disj
    (.conj (ltF x y) (.equal z (addT (mulT y y) x)))
    (.conj (leF y x) (.equal z (addT (addT (mulT x x) x) y)))

/-- Each equality atom of the graph evaluates crisply. -/
theorem eqAtom_crisp (env : natModel.Assignment) (s t : ArithQTerm) :
    natModel.evalFormula env (.equal s t) = 0 ∨
      natModel.evalFormula env (.equal s t) = 1 :=
  quantifierFree_crisp env (.equal s t) True.intro

/-- An equality atom is designated exactly when both sides evaluate equally. -/
theorem eqAtom_eval_one_iff (env : natModel.Assignment) (s t : ArithQTerm) :
    natModel.evalFormula env (.equal s t) = 1 ↔
      natModel.evalTerm env s = natModel.evalTerm env t := by
  show natModel.eq _ _ = 1 ↔ _
  exact ⟨natModel_crispEquality.eq_one_imp, fun h => natModel_eq_of_eq h⟩

/-- The two guarded branches of the graph, against `Nat.pair`'s definition. -/
private theorem pair_branch_iff (xv yv zv : Nat) :
    ((xv < yv ∧ zv = yv * yv + xv) ∨ (yv ≤ xv ∧ zv = xv * xv + xv + yv)) ↔
      zv = Nat.pair xv yv := by
  unfold Nat.pair
  by_cases hlt : xv < yv
  · rw [if_pos hlt]
    constructor
    · rintro (⟨_, hz⟩ | ⟨hle, _⟩)
      · exact hz
      · exact absurd hlt (Nat.not_lt.mpr hle)
    · exact fun hz => Or.inl ⟨hlt, hz⟩
  · rw [if_neg hlt]
    constructor
    · rintro (⟨hlt', _⟩ | ⟨_, hz⟩)
      · exact absurd hlt' hlt
      · exact hz
    · exact fun hz => Or.inr ⟨Nat.le_of_not_lt hlt, hz⟩

/-- The pairing graph is designated in the standard model exactly when `z` is
    `Nat.pair x y`. -/
theorem pairGraph_eval_one_iff (env : natModel.Assignment) (x y z : ArithQTerm) :
    natModel.evalFormula env (pairGraph x y z) = 1 ↔
      natModel.evalTerm env z =
        Nat.pair (natModel.evalTerm env x) (natModel.evalTerm env y) := by
  -- crispness of the two branch conjunctions
  have h1 : natModel.evalFormula env
        (.conj (ltF x y) (.equal z (addT (mulT y y) x))) = 0 ∨
      natModel.evalFormula env
        (.conj (ltF x y) (.equal z (addT (mulT y y) x))) = 1 :=
    conj_crisp (ltF_crisp env x y) (eqAtom_crisp env z (addT (mulT y y) x))
  have h2 : natModel.evalFormula env
        (.conj (leF y x) (.equal z (addT (addT (mulT x x) x) y))) = 0 ∨
      natModel.evalFormula env
        (.conj (leF y x) (.equal z (addT (addT (mulT x x) x) y))) = 1 :=
    conj_crisp (leF_crisp env y x) (eqAtom_crisp env z (addT (addT (mulT x x) x) y))
  -- the two branches, read off crisply
  have hc1 : natModel.evalFormula env
        (.conj (ltF x y) (.equal z (addT (mulT y y) x))) = 1 ↔
      natModel.evalTerm env x < natModel.evalTerm env y ∧
        natModel.evalTerm env z =
          natModel.evalTerm env y * natModel.evalTerm env y +
            natModel.evalTerm env x := by
    show natModel.evalFormula env (ltF x y) ⊗
        natModel.evalFormula env (.equal z (addT (mulT y y) x)) = 1 ↔ _
    rw [conj_crisp_one_iff (ltF_crisp env x y)
          (eqAtom_crisp env z (addT (mulT y y) x)),
      ltF_eval_one_iff, eqAtom_eval_one_iff]
    exact Iff.rfl
  have hc2 : natModel.evalFormula env
        (.conj (leF y x) (.equal z (addT (addT (mulT x x) x) y))) = 1 ↔
      natModel.evalTerm env y ≤ natModel.evalTerm env x ∧
        natModel.evalTerm env z =
          natModel.evalTerm env x * natModel.evalTerm env x +
            natModel.evalTerm env x + natModel.evalTerm env y := by
    show natModel.evalFormula env (leF y x) ⊗
        natModel.evalFormula env (.equal z (addT (addT (mulT x x) x) y)) = 1 ↔ _
    rw [conj_crisp_one_iff (leF_crisp env y x)
          (eqAtom_crisp env z (addT (addT (mulT x x) x) y)),
      leF_eval_one_iff, eqAtom_eval_one_iff]
    exact Iff.rfl
  -- assemble: disj of two crisp conjunctions matches Nat.pair's case split
  show natModel.evalFormula env (.conj (ltF x y) (.equal z (addT (mulT y y) x)))
      ⊔ natModel.evalFormula env (.conj (leF y x)
          (.equal z (addT (addT (mulT x x) x) y))) = 1 ↔ _
  rw [disj_crisp_one_iff h1 h2, hc1, hc2]
  exact pair_branch_iff _ _ _

/-- Numeral-level representability: the graph at numerals is designated exactly
    when `c = Nat.pair a b`. -/
theorem pairGraph_represents (a b c : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env
        (pairGraph (numeral a) (numeral b) (numeral c)) = 1 ↔
      c = Nat.pair a b := by
  rw [pairGraph_eval_one_iff, eval_numeral, eval_numeral, eval_numeral]

/-! ## Unpairing, read off the pairing graph

`Nat.unpair` is defined through `sqrt`, which does not arithmetize directly. But
its graph is the pairing graph read backward: `(x, y)` unpairs `z` iff
`z = Nat.pair x y`. So the same `pairGraph` formula represents unpairing, using
the pairing bijection rather than any square-root arithmetic. -/

/-- The unpairing graph: `pairGraph` with the pair argument in the output slot. -/
def unpairGraph (z x y : ArithQTerm) : ArithQFormula := pairGraph x y z

/-- `c = Nat.pair a b` iff `(a, b)` is the unpairing of `c`: the pairing
    bijection. -/
theorem pair_eq_iff_unpair (a b c : Nat) :
    c = Nat.pair a b ↔ Nat.unpair c = (a, b) := by
  constructor
  · intro h; rw [h, Nat.unpair_pair]
  · intro h
    have := Nat.pair_unpair c
    rw [h] at this
    exact this.symm

/-- Numeral-level representability of unpairing: the graph at numerals is
    designated exactly when `(a, b)` is `Nat.unpair c`. -/
theorem unpairGraph_represents (a b c : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env
        (unpairGraph (numeral c) (numeral a) (numeral b)) = 1 ↔
      Nat.unpair c = (a, b) := by
  rw [unpairGraph, pairGraph_represents, pair_eq_iff_unpair]

end arithQ
end Foundation
end Cred
